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
% DateTime   : Thu Dec  3 12:17:21 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  194 (12606 expanded)
%              Number of clauses        :  121 (3402 expanded)
%              Number of leaves         :   19 (3673 expanded)
%              Depth                    :   32
%              Number of atoms          :  685 (81552 expanded)
%              Number of equality atoms :  258 (13091 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f57,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f56,f55,f54])).

fof(f90,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f82,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f87,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f85,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f83,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f86,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f91,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
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

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f92,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f64,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f70,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f67,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f68,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f93,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1207,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_24,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_409,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_410,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_409])).

cnf(c_35,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_414,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_415,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_414])).

cnf(c_1242,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1207,c_410,c_415])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_25,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_396,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_397,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_396])).

cnf(c_48,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_399,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_397,c_34,c_33,c_48])).

cnf(c_421,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_399])).

cnf(c_422,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_14,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_19,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_479,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_14,c_19])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_483,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_479,c_19,c_14,c_13])).

cnf(c_484,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_483])).

cnf(c_523,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_422,c_484])).

cnf(c_1201,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_1342,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1201,c_410])).

cnf(c_1866,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1342])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1206,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1236,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1206,c_410,c_415])).

cnf(c_2007,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1866,c_39,c_1236])).

cnf(c_2008,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2007])).

cnf(c_2015,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1242,c_2008])).

cnf(c_2018,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2015,c_1242])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1212,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2371,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2018,c_1212])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1239,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_29,c_410,c_415])).

cnf(c_2020,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_2015,c_1239])).

cnf(c_2570,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2371,c_2020])).

cnf(c_2573,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2570,c_2371])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1211,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3251,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2573,c_1211])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_42,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2576,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2570,c_2018])).

cnf(c_2019,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2015,c_1236])).

cnf(c_2577,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2570,c_2019])).

cnf(c_4242,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3251,c_39,c_42,c_2576,c_2577])).

cnf(c_1205,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(X0) = k4_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1219,plain,
    ( k2_funct_1(X0) = k4_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3259,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1219])).

cnf(c_1478,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_1493,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3458,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3259,c_32,c_30,c_28,c_1478,c_1493])).

cnf(c_4246,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4242,c_3458])).

cnf(c_4249,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4246,c_1212])).

cnf(c_1213,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_2372,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2018,c_1213])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1221,plain,
    ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2471,plain,
    ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2372,c_1221])).

cnf(c_4259,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4249,c_2471])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1209,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4366,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
    | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4259,c_1209])).

cnf(c_12,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1214,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2743,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1214])).

cnf(c_1496,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_2987,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2743,c_32,c_30,c_28,c_1478,c_1496])).

cnf(c_3463,plain,
    ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3458,c_2987])).

cnf(c_4372,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2
    | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k4_relat_1(sK2)) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4366,c_3463])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1479,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1478])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_203,plain,
    ( ~ v2_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23,c_13,c_9])).

cnf(c_204,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_203])).

cnf(c_1204,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_204])).

cnf(c_1626,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1242,c_1204])).

cnf(c_1472,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_1473,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1472])).

cnf(c_1901,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1626,c_39,c_41,c_42,c_1473,c_1479])).

cnf(c_3464,plain,
    ( v1_funct_1(k4_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3458,c_1901])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1218,plain,
    ( v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3481,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k4_relat_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3458,c_1218])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1210,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3043,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2573,c_1210])).

cnf(c_4234,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3043,c_39,c_42,c_2576,c_2577])).

cnf(c_4238,plain,
    ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4234,c_3458])).

cnf(c_4426,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4372,c_39,c_41,c_42,c_1479,c_3464,c_3481,c_4238,c_4246])).

cnf(c_20,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_27,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_444,plain,
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
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_445,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_444])).

cnf(c_721,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_445])).

cnf(c_1202,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_1389,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1202,c_410,c_415])).

cnf(c_720,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_445])).

cnf(c_1203,plain,
    ( v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_1323,plain,
    ( v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1203,c_410,c_415])).

cnf(c_1395,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1389,c_1323])).

cnf(c_2173,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2020,c_1209])).

cnf(c_2381,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2173,c_39,c_42,c_2018,c_2019])).

cnf(c_2462,plain,
    ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1395,c_2015,c_2381])).

cnf(c_2574,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2570,c_2462])).

cnf(c_3461,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3458,c_2574])).

cnf(c_4429,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4426,c_3461])).

cnf(c_723,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1689,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4429,c_2577,c_2576,c_1689,c_39])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:57:40 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 3.15/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.00  
% 3.15/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.15/1.00  
% 3.15/1.00  ------  iProver source info
% 3.15/1.00  
% 3.15/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.15/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.15/1.00  git: non_committed_changes: false
% 3.15/1.00  git: last_make_outside_of_git: false
% 3.15/1.00  
% 3.15/1.00  ------ 
% 3.15/1.00  
% 3.15/1.00  ------ Input Options
% 3.15/1.00  
% 3.15/1.00  --out_options                           all
% 3.15/1.00  --tptp_safe_out                         true
% 3.15/1.00  --problem_path                          ""
% 3.15/1.00  --include_path                          ""
% 3.15/1.00  --clausifier                            res/vclausify_rel
% 3.15/1.00  --clausifier_options                    --mode clausify
% 3.15/1.00  --stdin                                 false
% 3.15/1.00  --stats_out                             all
% 3.15/1.00  
% 3.15/1.00  ------ General Options
% 3.15/1.00  
% 3.15/1.00  --fof                                   false
% 3.15/1.00  --time_out_real                         305.
% 3.15/1.00  --time_out_virtual                      -1.
% 3.15/1.00  --symbol_type_check                     false
% 3.15/1.00  --clausify_out                          false
% 3.15/1.00  --sig_cnt_out                           false
% 3.15/1.00  --trig_cnt_out                          false
% 3.15/1.00  --trig_cnt_out_tolerance                1.
% 3.15/1.00  --trig_cnt_out_sk_spl                   false
% 3.15/1.00  --abstr_cl_out                          false
% 3.15/1.00  
% 3.15/1.00  ------ Global Options
% 3.15/1.00  
% 3.15/1.00  --schedule                              default
% 3.15/1.00  --add_important_lit                     false
% 3.15/1.00  --prop_solver_per_cl                    1000
% 3.15/1.00  --min_unsat_core                        false
% 3.15/1.00  --soft_assumptions                      false
% 3.15/1.00  --soft_lemma_size                       3
% 3.15/1.00  --prop_impl_unit_size                   0
% 3.15/1.00  --prop_impl_unit                        []
% 3.15/1.00  --share_sel_clauses                     true
% 3.15/1.00  --reset_solvers                         false
% 3.15/1.00  --bc_imp_inh                            [conj_cone]
% 3.15/1.00  --conj_cone_tolerance                   3.
% 3.15/1.00  --extra_neg_conj                        none
% 3.15/1.00  --large_theory_mode                     true
% 3.15/1.00  --prolific_symb_bound                   200
% 3.15/1.00  --lt_threshold                          2000
% 3.15/1.00  --clause_weak_htbl                      true
% 3.15/1.00  --gc_record_bc_elim                     false
% 3.15/1.00  
% 3.15/1.00  ------ Preprocessing Options
% 3.15/1.00  
% 3.15/1.00  --preprocessing_flag                    true
% 3.15/1.00  --time_out_prep_mult                    0.1
% 3.15/1.00  --splitting_mode                        input
% 3.15/1.00  --splitting_grd                         true
% 3.15/1.00  --splitting_cvd                         false
% 3.15/1.00  --splitting_cvd_svl                     false
% 3.15/1.00  --splitting_nvd                         32
% 3.15/1.00  --sub_typing                            true
% 3.15/1.00  --prep_gs_sim                           true
% 3.15/1.00  --prep_unflatten                        true
% 3.15/1.00  --prep_res_sim                          true
% 3.15/1.00  --prep_upred                            true
% 3.15/1.00  --prep_sem_filter                       exhaustive
% 3.15/1.00  --prep_sem_filter_out                   false
% 3.15/1.00  --pred_elim                             true
% 3.15/1.00  --res_sim_input                         true
% 3.15/1.00  --eq_ax_congr_red                       true
% 3.15/1.00  --pure_diseq_elim                       true
% 3.15/1.00  --brand_transform                       false
% 3.15/1.00  --non_eq_to_eq                          false
% 3.15/1.00  --prep_def_merge                        true
% 3.15/1.00  --prep_def_merge_prop_impl              false
% 3.15/1.00  --prep_def_merge_mbd                    true
% 3.15/1.00  --prep_def_merge_tr_red                 false
% 3.15/1.00  --prep_def_merge_tr_cl                  false
% 3.15/1.00  --smt_preprocessing                     true
% 3.15/1.00  --smt_ac_axioms                         fast
% 3.15/1.00  --preprocessed_out                      false
% 3.15/1.00  --preprocessed_stats                    false
% 3.15/1.00  
% 3.15/1.00  ------ Abstraction refinement Options
% 3.15/1.00  
% 3.15/1.00  --abstr_ref                             []
% 3.15/1.00  --abstr_ref_prep                        false
% 3.15/1.00  --abstr_ref_until_sat                   false
% 3.15/1.00  --abstr_ref_sig_restrict                funpre
% 3.15/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.15/1.00  --abstr_ref_under                       []
% 3.15/1.00  
% 3.15/1.00  ------ SAT Options
% 3.15/1.00  
% 3.15/1.00  --sat_mode                              false
% 3.15/1.00  --sat_fm_restart_options                ""
% 3.15/1.00  --sat_gr_def                            false
% 3.15/1.00  --sat_epr_types                         true
% 3.15/1.00  --sat_non_cyclic_types                  false
% 3.15/1.00  --sat_finite_models                     false
% 3.15/1.00  --sat_fm_lemmas                         false
% 3.15/1.00  --sat_fm_prep                           false
% 3.15/1.00  --sat_fm_uc_incr                        true
% 3.15/1.00  --sat_out_model                         small
% 3.15/1.00  --sat_out_clauses                       false
% 3.15/1.00  
% 3.15/1.00  ------ QBF Options
% 3.15/1.00  
% 3.15/1.00  --qbf_mode                              false
% 3.15/1.00  --qbf_elim_univ                         false
% 3.15/1.00  --qbf_dom_inst                          none
% 3.15/1.00  --qbf_dom_pre_inst                      false
% 3.15/1.00  --qbf_sk_in                             false
% 3.15/1.00  --qbf_pred_elim                         true
% 3.15/1.00  --qbf_split                             512
% 3.15/1.00  
% 3.15/1.00  ------ BMC1 Options
% 3.15/1.00  
% 3.15/1.00  --bmc1_incremental                      false
% 3.15/1.00  --bmc1_axioms                           reachable_all
% 3.15/1.00  --bmc1_min_bound                        0
% 3.15/1.00  --bmc1_max_bound                        -1
% 3.15/1.00  --bmc1_max_bound_default                -1
% 3.15/1.00  --bmc1_symbol_reachability              true
% 3.15/1.00  --bmc1_property_lemmas                  false
% 3.15/1.00  --bmc1_k_induction                      false
% 3.15/1.00  --bmc1_non_equiv_states                 false
% 3.15/1.00  --bmc1_deadlock                         false
% 3.15/1.00  --bmc1_ucm                              false
% 3.15/1.00  --bmc1_add_unsat_core                   none
% 3.15/1.00  --bmc1_unsat_core_children              false
% 3.15/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.15/1.00  --bmc1_out_stat                         full
% 3.15/1.00  --bmc1_ground_init                      false
% 3.15/1.00  --bmc1_pre_inst_next_state              false
% 3.15/1.00  --bmc1_pre_inst_state                   false
% 3.15/1.00  --bmc1_pre_inst_reach_state             false
% 3.15/1.00  --bmc1_out_unsat_core                   false
% 3.15/1.00  --bmc1_aig_witness_out                  false
% 3.15/1.00  --bmc1_verbose                          false
% 3.15/1.00  --bmc1_dump_clauses_tptp                false
% 3.15/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.15/1.00  --bmc1_dump_file                        -
% 3.15/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.15/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.15/1.00  --bmc1_ucm_extend_mode                  1
% 3.15/1.00  --bmc1_ucm_init_mode                    2
% 3.15/1.00  --bmc1_ucm_cone_mode                    none
% 3.15/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.15/1.00  --bmc1_ucm_relax_model                  4
% 3.15/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.15/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.15/1.00  --bmc1_ucm_layered_model                none
% 3.15/1.00  --bmc1_ucm_max_lemma_size               10
% 3.15/1.00  
% 3.15/1.00  ------ AIG Options
% 3.15/1.00  
% 3.15/1.00  --aig_mode                              false
% 3.15/1.00  
% 3.15/1.00  ------ Instantiation Options
% 3.15/1.00  
% 3.15/1.00  --instantiation_flag                    true
% 3.15/1.00  --inst_sos_flag                         false
% 3.15/1.00  --inst_sos_phase                        true
% 3.15/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.15/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.15/1.00  --inst_lit_sel_side                     num_symb
% 3.15/1.00  --inst_solver_per_active                1400
% 3.15/1.00  --inst_solver_calls_frac                1.
% 3.15/1.00  --inst_passive_queue_type               priority_queues
% 3.15/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.15/1.00  --inst_passive_queues_freq              [25;2]
% 3.15/1.00  --inst_dismatching                      true
% 3.15/1.00  --inst_eager_unprocessed_to_passive     true
% 3.15/1.00  --inst_prop_sim_given                   true
% 3.15/1.00  --inst_prop_sim_new                     false
% 3.15/1.00  --inst_subs_new                         false
% 3.15/1.00  --inst_eq_res_simp                      false
% 3.15/1.00  --inst_subs_given                       false
% 3.15/1.00  --inst_orphan_elimination               true
% 3.15/1.00  --inst_learning_loop_flag               true
% 3.15/1.00  --inst_learning_start                   3000
% 3.15/1.00  --inst_learning_factor                  2
% 3.15/1.00  --inst_start_prop_sim_after_learn       3
% 3.15/1.00  --inst_sel_renew                        solver
% 3.15/1.00  --inst_lit_activity_flag                true
% 3.15/1.00  --inst_restr_to_given                   false
% 3.15/1.00  --inst_activity_threshold               500
% 3.15/1.00  --inst_out_proof                        true
% 3.15/1.00  
% 3.15/1.00  ------ Resolution Options
% 3.15/1.00  
% 3.15/1.00  --resolution_flag                       true
% 3.15/1.00  --res_lit_sel                           adaptive
% 3.15/1.00  --res_lit_sel_side                      none
% 3.15/1.00  --res_ordering                          kbo
% 3.15/1.00  --res_to_prop_solver                    active
% 3.15/1.00  --res_prop_simpl_new                    false
% 3.15/1.00  --res_prop_simpl_given                  true
% 3.15/1.00  --res_passive_queue_type                priority_queues
% 3.15/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.15/1.00  --res_passive_queues_freq               [15;5]
% 3.15/1.00  --res_forward_subs                      full
% 3.15/1.00  --res_backward_subs                     full
% 3.15/1.00  --res_forward_subs_resolution           true
% 3.15/1.00  --res_backward_subs_resolution          true
% 3.15/1.00  --res_orphan_elimination                true
% 3.15/1.00  --res_time_limit                        2.
% 3.15/1.00  --res_out_proof                         true
% 3.15/1.00  
% 3.15/1.00  ------ Superposition Options
% 3.15/1.00  
% 3.15/1.00  --superposition_flag                    true
% 3.15/1.00  --sup_passive_queue_type                priority_queues
% 3.15/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.15/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.15/1.00  --demod_completeness_check              fast
% 3.15/1.00  --demod_use_ground                      true
% 3.15/1.00  --sup_to_prop_solver                    passive
% 3.15/1.00  --sup_prop_simpl_new                    true
% 3.15/1.00  --sup_prop_simpl_given                  true
% 3.15/1.00  --sup_fun_splitting                     false
% 3.15/1.00  --sup_smt_interval                      50000
% 3.15/1.00  
% 3.15/1.00  ------ Superposition Simplification Setup
% 3.15/1.00  
% 3.15/1.00  --sup_indices_passive                   []
% 3.15/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.15/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/1.00  --sup_full_bw                           [BwDemod]
% 3.15/1.00  --sup_immed_triv                        [TrivRules]
% 3.15/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/1.00  --sup_immed_bw_main                     []
% 3.15/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.15/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/1.00  
% 3.15/1.00  ------ Combination Options
% 3.15/1.00  
% 3.15/1.00  --comb_res_mult                         3
% 3.15/1.00  --comb_sup_mult                         2
% 3.15/1.00  --comb_inst_mult                        10
% 3.15/1.00  
% 3.15/1.00  ------ Debug Options
% 3.15/1.00  
% 3.15/1.00  --dbg_backtrace                         false
% 3.15/1.00  --dbg_dump_prop_clauses                 false
% 3.15/1.00  --dbg_dump_prop_clauses_file            -
% 3.15/1.00  --dbg_out_stat                          false
% 3.15/1.00  ------ Parsing...
% 3.15/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.15/1.00  
% 3.15/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.15/1.00  
% 3.15/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.15/1.00  
% 3.15/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.15/1.00  ------ Proving...
% 3.15/1.00  ------ Problem Properties 
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  clauses                                 28
% 3.15/1.00  conjectures                             5
% 3.15/1.00  EPR                                     4
% 3.15/1.00  Horn                                    28
% 3.15/1.00  unary                                   8
% 3.15/1.00  binary                                  6
% 3.15/1.00  lits                                    84
% 3.15/1.00  lits eq                                 17
% 3.15/1.00  fd_pure                                 0
% 3.15/1.00  fd_pseudo                               0
% 3.15/1.00  fd_cond                                 0
% 3.15/1.00  fd_pseudo_cond                          2
% 3.15/1.00  AC symbols                              0
% 3.15/1.00  
% 3.15/1.00  ------ Schedule dynamic 5 is on 
% 3.15/1.00  
% 3.15/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  ------ 
% 3.15/1.00  Current options:
% 3.15/1.00  ------ 
% 3.15/1.00  
% 3.15/1.00  ------ Input Options
% 3.15/1.00  
% 3.15/1.00  --out_options                           all
% 3.15/1.00  --tptp_safe_out                         true
% 3.15/1.00  --problem_path                          ""
% 3.15/1.00  --include_path                          ""
% 3.15/1.00  --clausifier                            res/vclausify_rel
% 3.15/1.00  --clausifier_options                    --mode clausify
% 3.15/1.00  --stdin                                 false
% 3.15/1.00  --stats_out                             all
% 3.15/1.00  
% 3.15/1.00  ------ General Options
% 3.15/1.00  
% 3.15/1.00  --fof                                   false
% 3.15/1.00  --time_out_real                         305.
% 3.15/1.00  --time_out_virtual                      -1.
% 3.15/1.00  --symbol_type_check                     false
% 3.15/1.00  --clausify_out                          false
% 3.15/1.00  --sig_cnt_out                           false
% 3.15/1.00  --trig_cnt_out                          false
% 3.15/1.00  --trig_cnt_out_tolerance                1.
% 3.15/1.00  --trig_cnt_out_sk_spl                   false
% 3.15/1.00  --abstr_cl_out                          false
% 3.15/1.00  
% 3.15/1.00  ------ Global Options
% 3.15/1.00  
% 3.15/1.00  --schedule                              default
% 3.15/1.00  --add_important_lit                     false
% 3.15/1.00  --prop_solver_per_cl                    1000
% 3.15/1.00  --min_unsat_core                        false
% 3.15/1.00  --soft_assumptions                      false
% 3.15/1.00  --soft_lemma_size                       3
% 3.15/1.00  --prop_impl_unit_size                   0
% 3.15/1.00  --prop_impl_unit                        []
% 3.15/1.00  --share_sel_clauses                     true
% 3.15/1.00  --reset_solvers                         false
% 3.15/1.00  --bc_imp_inh                            [conj_cone]
% 3.15/1.00  --conj_cone_tolerance                   3.
% 3.15/1.00  --extra_neg_conj                        none
% 3.15/1.00  --large_theory_mode                     true
% 3.15/1.00  --prolific_symb_bound                   200
% 3.15/1.00  --lt_threshold                          2000
% 3.15/1.00  --clause_weak_htbl                      true
% 3.15/1.00  --gc_record_bc_elim                     false
% 3.15/1.00  
% 3.15/1.00  ------ Preprocessing Options
% 3.15/1.00  
% 3.15/1.00  --preprocessing_flag                    true
% 3.15/1.00  --time_out_prep_mult                    0.1
% 3.15/1.00  --splitting_mode                        input
% 3.15/1.00  --splitting_grd                         true
% 3.15/1.00  --splitting_cvd                         false
% 3.15/1.00  --splitting_cvd_svl                     false
% 3.15/1.00  --splitting_nvd                         32
% 3.15/1.00  --sub_typing                            true
% 3.15/1.00  --prep_gs_sim                           true
% 3.15/1.00  --prep_unflatten                        true
% 3.15/1.00  --prep_res_sim                          true
% 3.15/1.00  --prep_upred                            true
% 3.15/1.00  --prep_sem_filter                       exhaustive
% 3.15/1.00  --prep_sem_filter_out                   false
% 3.15/1.00  --pred_elim                             true
% 3.15/1.00  --res_sim_input                         true
% 3.15/1.00  --eq_ax_congr_red                       true
% 3.15/1.00  --pure_diseq_elim                       true
% 3.15/1.00  --brand_transform                       false
% 3.15/1.00  --non_eq_to_eq                          false
% 3.15/1.00  --prep_def_merge                        true
% 3.15/1.00  --prep_def_merge_prop_impl              false
% 3.15/1.00  --prep_def_merge_mbd                    true
% 3.15/1.00  --prep_def_merge_tr_red                 false
% 3.15/1.00  --prep_def_merge_tr_cl                  false
% 3.15/1.00  --smt_preprocessing                     true
% 3.15/1.00  --smt_ac_axioms                         fast
% 3.15/1.00  --preprocessed_out                      false
% 3.15/1.00  --preprocessed_stats                    false
% 3.15/1.00  
% 3.15/1.00  ------ Abstraction refinement Options
% 3.15/1.00  
% 3.15/1.00  --abstr_ref                             []
% 3.15/1.00  --abstr_ref_prep                        false
% 3.15/1.00  --abstr_ref_until_sat                   false
% 3.15/1.00  --abstr_ref_sig_restrict                funpre
% 3.15/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.15/1.00  --abstr_ref_under                       []
% 3.15/1.00  
% 3.15/1.00  ------ SAT Options
% 3.15/1.00  
% 3.15/1.00  --sat_mode                              false
% 3.15/1.00  --sat_fm_restart_options                ""
% 3.15/1.00  --sat_gr_def                            false
% 3.15/1.00  --sat_epr_types                         true
% 3.15/1.00  --sat_non_cyclic_types                  false
% 3.15/1.00  --sat_finite_models                     false
% 3.15/1.00  --sat_fm_lemmas                         false
% 3.15/1.00  --sat_fm_prep                           false
% 3.15/1.00  --sat_fm_uc_incr                        true
% 3.15/1.00  --sat_out_model                         small
% 3.15/1.00  --sat_out_clauses                       false
% 3.15/1.00  
% 3.15/1.00  ------ QBF Options
% 3.15/1.00  
% 3.15/1.00  --qbf_mode                              false
% 3.15/1.00  --qbf_elim_univ                         false
% 3.15/1.00  --qbf_dom_inst                          none
% 3.15/1.00  --qbf_dom_pre_inst                      false
% 3.15/1.00  --qbf_sk_in                             false
% 3.15/1.00  --qbf_pred_elim                         true
% 3.15/1.00  --qbf_split                             512
% 3.15/1.00  
% 3.15/1.00  ------ BMC1 Options
% 3.15/1.00  
% 3.15/1.00  --bmc1_incremental                      false
% 3.15/1.00  --bmc1_axioms                           reachable_all
% 3.15/1.00  --bmc1_min_bound                        0
% 3.15/1.00  --bmc1_max_bound                        -1
% 3.15/1.00  --bmc1_max_bound_default                -1
% 3.15/1.00  --bmc1_symbol_reachability              true
% 3.15/1.00  --bmc1_property_lemmas                  false
% 3.15/1.00  --bmc1_k_induction                      false
% 3.15/1.00  --bmc1_non_equiv_states                 false
% 3.15/1.00  --bmc1_deadlock                         false
% 3.15/1.00  --bmc1_ucm                              false
% 3.15/1.00  --bmc1_add_unsat_core                   none
% 3.15/1.00  --bmc1_unsat_core_children              false
% 3.15/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.15/1.00  --bmc1_out_stat                         full
% 3.15/1.00  --bmc1_ground_init                      false
% 3.15/1.00  --bmc1_pre_inst_next_state              false
% 3.15/1.00  --bmc1_pre_inst_state                   false
% 3.15/1.00  --bmc1_pre_inst_reach_state             false
% 3.15/1.00  --bmc1_out_unsat_core                   false
% 3.15/1.00  --bmc1_aig_witness_out                  false
% 3.15/1.00  --bmc1_verbose                          false
% 3.15/1.00  --bmc1_dump_clauses_tptp                false
% 3.15/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.15/1.00  --bmc1_dump_file                        -
% 3.15/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.15/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.15/1.00  --bmc1_ucm_extend_mode                  1
% 3.15/1.00  --bmc1_ucm_init_mode                    2
% 3.15/1.00  --bmc1_ucm_cone_mode                    none
% 3.15/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.15/1.00  --bmc1_ucm_relax_model                  4
% 3.15/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.15/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.15/1.00  --bmc1_ucm_layered_model                none
% 3.15/1.00  --bmc1_ucm_max_lemma_size               10
% 3.15/1.00  
% 3.15/1.00  ------ AIG Options
% 3.15/1.00  
% 3.15/1.00  --aig_mode                              false
% 3.15/1.00  
% 3.15/1.00  ------ Instantiation Options
% 3.15/1.00  
% 3.15/1.00  --instantiation_flag                    true
% 3.15/1.00  --inst_sos_flag                         false
% 3.15/1.00  --inst_sos_phase                        true
% 3.15/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.15/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.15/1.00  --inst_lit_sel_side                     none
% 3.15/1.00  --inst_solver_per_active                1400
% 3.15/1.00  --inst_solver_calls_frac                1.
% 3.15/1.00  --inst_passive_queue_type               priority_queues
% 3.15/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.15/1.00  --inst_passive_queues_freq              [25;2]
% 3.15/1.00  --inst_dismatching                      true
% 3.15/1.00  --inst_eager_unprocessed_to_passive     true
% 3.15/1.00  --inst_prop_sim_given                   true
% 3.15/1.00  --inst_prop_sim_new                     false
% 3.15/1.00  --inst_subs_new                         false
% 3.15/1.00  --inst_eq_res_simp                      false
% 3.15/1.00  --inst_subs_given                       false
% 3.15/1.00  --inst_orphan_elimination               true
% 3.15/1.00  --inst_learning_loop_flag               true
% 3.15/1.00  --inst_learning_start                   3000
% 3.15/1.00  --inst_learning_factor                  2
% 3.15/1.00  --inst_start_prop_sim_after_learn       3
% 3.15/1.00  --inst_sel_renew                        solver
% 3.15/1.00  --inst_lit_activity_flag                true
% 3.15/1.00  --inst_restr_to_given                   false
% 3.15/1.00  --inst_activity_threshold               500
% 3.15/1.00  --inst_out_proof                        true
% 3.15/1.00  
% 3.15/1.00  ------ Resolution Options
% 3.15/1.00  
% 3.15/1.00  --resolution_flag                       false
% 3.15/1.00  --res_lit_sel                           adaptive
% 3.15/1.00  --res_lit_sel_side                      none
% 3.15/1.00  --res_ordering                          kbo
% 3.15/1.00  --res_to_prop_solver                    active
% 3.15/1.00  --res_prop_simpl_new                    false
% 3.15/1.00  --res_prop_simpl_given                  true
% 3.15/1.00  --res_passive_queue_type                priority_queues
% 3.15/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.15/1.00  --res_passive_queues_freq               [15;5]
% 3.15/1.00  --res_forward_subs                      full
% 3.15/1.00  --res_backward_subs                     full
% 3.15/1.00  --res_forward_subs_resolution           true
% 3.15/1.00  --res_backward_subs_resolution          true
% 3.15/1.00  --res_orphan_elimination                true
% 3.15/1.00  --res_time_limit                        2.
% 3.15/1.00  --res_out_proof                         true
% 3.15/1.00  
% 3.15/1.00  ------ Superposition Options
% 3.15/1.00  
% 3.15/1.00  --superposition_flag                    true
% 3.15/1.00  --sup_passive_queue_type                priority_queues
% 3.15/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.15/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.15/1.00  --demod_completeness_check              fast
% 3.15/1.00  --demod_use_ground                      true
% 3.15/1.00  --sup_to_prop_solver                    passive
% 3.15/1.00  --sup_prop_simpl_new                    true
% 3.15/1.00  --sup_prop_simpl_given                  true
% 3.15/1.00  --sup_fun_splitting                     false
% 3.15/1.00  --sup_smt_interval                      50000
% 3.15/1.00  
% 3.15/1.00  ------ Superposition Simplification Setup
% 3.15/1.00  
% 3.15/1.00  --sup_indices_passive                   []
% 3.15/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.15/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/1.00  --sup_full_bw                           [BwDemod]
% 3.15/1.00  --sup_immed_triv                        [TrivRules]
% 3.15/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/1.00  --sup_immed_bw_main                     []
% 3.15/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.15/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.15/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.15/1.00  
% 3.15/1.00  ------ Combination Options
% 3.15/1.00  
% 3.15/1.00  --comb_res_mult                         3
% 3.15/1.00  --comb_sup_mult                         2
% 3.15/1.00  --comb_inst_mult                        10
% 3.15/1.00  
% 3.15/1.00  ------ Debug Options
% 3.15/1.00  
% 3.15/1.00  --dbg_backtrace                         false
% 3.15/1.00  --dbg_dump_prop_clauses                 false
% 3.15/1.00  --dbg_dump_prop_clauses_file            -
% 3.15/1.00  --dbg_out_stat                          false
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  ------ Proving...
% 3.15/1.00  
% 3.15/1.00  
% 3.15/1.00  % SZS status Theorem for theBenchmark.p
% 3.15/1.00  
% 3.15/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.15/1.00  
% 3.15/1.00  fof(f19,conjecture,(
% 3.15/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f20,negated_conjecture,(
% 3.15/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.15/1.00    inference(negated_conjecture,[],[f19])).
% 3.15/1.00  
% 3.15/1.00  fof(f49,plain,(
% 3.15/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.15/1.00    inference(ennf_transformation,[],[f20])).
% 3.15/1.00  
% 3.15/1.00  fof(f50,plain,(
% 3.15/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.15/1.00    inference(flattening,[],[f49])).
% 3.15/1.00  
% 3.15/1.00  fof(f56,plain,(
% 3.15/1.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.15/1.00    introduced(choice_axiom,[])).
% 3.15/1.00  
% 3.15/1.00  fof(f55,plain,(
% 3.15/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.15/1.00    introduced(choice_axiom,[])).
% 3.15/1.00  
% 3.15/1.00  fof(f54,plain,(
% 3.15/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.15/1.00    introduced(choice_axiom,[])).
% 3.15/1.00  
% 3.15/1.00  fof(f57,plain,(
% 3.15/1.00    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.15/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f56,f55,f54])).
% 3.15/1.00  
% 3.15/1.00  fof(f90,plain,(
% 3.15/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.15/1.00    inference(cnf_transformation,[],[f57])).
% 3.15/1.00  
% 3.15/1.00  fof(f16,axiom,(
% 3.15/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f44,plain,(
% 3.15/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.15/1.00    inference(ennf_transformation,[],[f16])).
% 3.15/1.00  
% 3.15/1.00  fof(f82,plain,(
% 3.15/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f44])).
% 3.15/1.00  
% 3.15/1.00  fof(f87,plain,(
% 3.15/1.00    l1_struct_0(sK1)),
% 3.15/1.00    inference(cnf_transformation,[],[f57])).
% 3.15/1.00  
% 3.15/1.00  fof(f85,plain,(
% 3.15/1.00    l1_struct_0(sK0)),
% 3.15/1.00    inference(cnf_transformation,[],[f57])).
% 3.15/1.00  
% 3.15/1.00  fof(f12,axiom,(
% 3.15/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f36,plain,(
% 3.15/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.15/1.00    inference(ennf_transformation,[],[f12])).
% 3.15/1.00  
% 3.15/1.00  fof(f37,plain,(
% 3.15/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.15/1.00    inference(flattening,[],[f36])).
% 3.15/1.00  
% 3.15/1.00  fof(f75,plain,(
% 3.15/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f37])).
% 3.15/1.00  
% 3.15/1.00  fof(f17,axiom,(
% 3.15/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f45,plain,(
% 3.15/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.15/1.00    inference(ennf_transformation,[],[f17])).
% 3.15/1.00  
% 3.15/1.00  fof(f46,plain,(
% 3.15/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.15/1.00    inference(flattening,[],[f45])).
% 3.15/1.00  
% 3.15/1.00  fof(f83,plain,(
% 3.15/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f46])).
% 3.15/1.00  
% 3.15/1.00  fof(f86,plain,(
% 3.15/1.00    ~v2_struct_0(sK1)),
% 3.15/1.00    inference(cnf_transformation,[],[f57])).
% 3.15/1.00  
% 3.15/1.00  fof(f10,axiom,(
% 3.15/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f21,plain,(
% 3.15/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.15/1.00    inference(pure_predicate_removal,[],[f10])).
% 3.15/1.00  
% 3.15/1.00  fof(f34,plain,(
% 3.15/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.00    inference(ennf_transformation,[],[f21])).
% 3.15/1.00  
% 3.15/1.00  fof(f72,plain,(
% 3.15/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/1.00    inference(cnf_transformation,[],[f34])).
% 3.15/1.00  
% 3.15/1.00  fof(f13,axiom,(
% 3.15/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f38,plain,(
% 3.15/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.15/1.00    inference(ennf_transformation,[],[f13])).
% 3.15/1.00  
% 3.15/1.00  fof(f39,plain,(
% 3.15/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.15/1.00    inference(flattening,[],[f38])).
% 3.15/1.00  
% 3.15/1.00  fof(f53,plain,(
% 3.15/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.15/1.00    inference(nnf_transformation,[],[f39])).
% 3.15/1.00  
% 3.15/1.00  fof(f76,plain,(
% 3.15/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f53])).
% 3.15/1.00  
% 3.15/1.00  fof(f9,axiom,(
% 3.15/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f33,plain,(
% 3.15/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.00    inference(ennf_transformation,[],[f9])).
% 3.15/1.00  
% 3.15/1.00  fof(f71,plain,(
% 3.15/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/1.00    inference(cnf_transformation,[],[f33])).
% 3.15/1.00  
% 3.15/1.00  fof(f88,plain,(
% 3.15/1.00    v1_funct_1(sK2)),
% 3.15/1.00    inference(cnf_transformation,[],[f57])).
% 3.15/1.00  
% 3.15/1.00  fof(f89,plain,(
% 3.15/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.15/1.00    inference(cnf_transformation,[],[f57])).
% 3.15/1.00  
% 3.15/1.00  fof(f11,axiom,(
% 3.15/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f35,plain,(
% 3.15/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.00    inference(ennf_transformation,[],[f11])).
% 3.15/1.00  
% 3.15/1.00  fof(f73,plain,(
% 3.15/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/1.00    inference(cnf_transformation,[],[f35])).
% 3.15/1.00  
% 3.15/1.00  fof(f91,plain,(
% 3.15/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.15/1.00    inference(cnf_transformation,[],[f57])).
% 3.15/1.00  
% 3.15/1.00  fof(f15,axiom,(
% 3.15/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f42,plain,(
% 3.15/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.15/1.00    inference(ennf_transformation,[],[f15])).
% 3.15/1.00  
% 3.15/1.00  fof(f43,plain,(
% 3.15/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.15/1.00    inference(flattening,[],[f42])).
% 3.15/1.00  
% 3.15/1.00  fof(f81,plain,(
% 3.15/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f43])).
% 3.15/1.00  
% 3.15/1.00  fof(f92,plain,(
% 3.15/1.00    v2_funct_1(sK2)),
% 3.15/1.00    inference(cnf_transformation,[],[f57])).
% 3.15/1.00  
% 3.15/1.00  fof(f5,axiom,(
% 3.15/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f25,plain,(
% 3.15/1.00    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.15/1.00    inference(ennf_transformation,[],[f5])).
% 3.15/1.00  
% 3.15/1.00  fof(f26,plain,(
% 3.15/1.00    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/1.00    inference(flattening,[],[f25])).
% 3.15/1.00  
% 3.15/1.00  fof(f65,plain,(
% 3.15/1.00    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f26])).
% 3.15/1.00  
% 3.15/1.00  fof(f4,axiom,(
% 3.15/1.00    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f24,plain,(
% 3.15/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k1_relat_1(k4_relat_1(X0)) = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.15/1.00    inference(ennf_transformation,[],[f4])).
% 3.15/1.00  
% 3.15/1.00  fof(f64,plain,(
% 3.15/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f24])).
% 3.15/1.00  
% 3.15/1.00  fof(f18,axiom,(
% 3.15/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f47,plain,(
% 3.15/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.15/1.00    inference(ennf_transformation,[],[f18])).
% 3.15/1.00  
% 3.15/1.00  fof(f48,plain,(
% 3.15/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.15/1.00    inference(flattening,[],[f47])).
% 3.15/1.00  
% 3.15/1.00  fof(f84,plain,(
% 3.15/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f48])).
% 3.15/1.00  
% 3.15/1.00  fof(f8,axiom,(
% 3.15/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f31,plain,(
% 3.15/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.15/1.00    inference(ennf_transformation,[],[f8])).
% 3.15/1.00  
% 3.15/1.00  fof(f32,plain,(
% 3.15/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/1.00    inference(flattening,[],[f31])).
% 3.15/1.00  
% 3.15/1.00  fof(f70,plain,(
% 3.15/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f32])).
% 3.15/1.00  
% 3.15/1.00  fof(f79,plain,(
% 3.15/1.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f43])).
% 3.15/1.00  
% 3.15/1.00  fof(f6,axiom,(
% 3.15/1.00    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f27,plain,(
% 3.15/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.15/1.00    inference(ennf_transformation,[],[f6])).
% 3.15/1.00  
% 3.15/1.00  fof(f28,plain,(
% 3.15/1.00    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/1.00    inference(flattening,[],[f27])).
% 3.15/1.00  
% 3.15/1.00  fof(f67,plain,(
% 3.15/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f28])).
% 3.15/1.00  
% 3.15/1.00  fof(f68,plain,(
% 3.15/1.00    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f28])).
% 3.15/1.00  
% 3.15/1.00  fof(f80,plain,(
% 3.15/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f43])).
% 3.15/1.00  
% 3.15/1.00  fof(f14,axiom,(
% 3.15/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 3.15/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.15/1.00  
% 3.15/1.00  fof(f40,plain,(
% 3.15/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.15/1.00    inference(ennf_transformation,[],[f14])).
% 3.15/1.00  
% 3.15/1.00  fof(f41,plain,(
% 3.15/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.15/1.00    inference(flattening,[],[f40])).
% 3.15/1.00  
% 3.15/1.00  fof(f78,plain,(
% 3.15/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.15/1.00    inference(cnf_transformation,[],[f41])).
% 3.15/1.00  
% 3.15/1.00  fof(f93,plain,(
% 3.15/1.00    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.15/1.00    inference(cnf_transformation,[],[f57])).
% 3.15/1.00  
% 3.15/1.00  cnf(c_30,negated_conjecture,
% 3.15/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.15/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1207,plain,
% 3.15/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_24,plain,
% 3.15/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.15/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_33,negated_conjecture,
% 3.15/1.00      ( l1_struct_0(sK1) ),
% 3.15/1.00      inference(cnf_transformation,[],[f87]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_409,plain,
% 3.15/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.15/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_410,plain,
% 3.15/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.15/1.00      inference(unflattening,[status(thm)],[c_409]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_35,negated_conjecture,
% 3.15/1.00      ( l1_struct_0(sK0) ),
% 3.15/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_414,plain,
% 3.15/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.15/1.00      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_415,plain,
% 3.15/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.15/1.00      inference(unflattening,[status(thm)],[c_414]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1242,plain,
% 3.15/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.15/1.00      inference(light_normalisation,[status(thm)],[c_1207,c_410,c_415]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_16,plain,
% 3.15/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.15/1.00      | v1_partfun1(X0,X1)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | v1_xboole_0(X2)
% 3.15/1.00      | ~ v1_funct_1(X0) ),
% 3.15/1.00      inference(cnf_transformation,[],[f75]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_25,plain,
% 3.15/1.00      ( v2_struct_0(X0)
% 3.15/1.00      | ~ l1_struct_0(X0)
% 3.15/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.15/1.00      inference(cnf_transformation,[],[f83]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_34,negated_conjecture,
% 3.15/1.00      ( ~ v2_struct_0(sK1) ),
% 3.15/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_396,plain,
% 3.15/1.00      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 3.15/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_397,plain,
% 3.15/1.00      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.15/1.00      inference(unflattening,[status(thm)],[c_396]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_48,plain,
% 3.15/1.00      ( v2_struct_0(sK1)
% 3.15/1.00      | ~ l1_struct_0(sK1)
% 3.15/1.00      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.15/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_399,plain,
% 3.15/1.00      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.15/1.00      inference(global_propositional_subsumption,
% 3.15/1.00                [status(thm)],
% 3.15/1.00                [c_397,c_34,c_33,c_48]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_421,plain,
% 3.15/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.15/1.00      | v1_partfun1(X0,X1)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | ~ v1_funct_1(X0)
% 3.15/1.00      | u1_struct_0(sK1) != X2 ),
% 3.15/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_399]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_422,plain,
% 3.15/1.00      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.15/1.00      | v1_partfun1(X0,X1)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.15/1.00      | ~ v1_funct_1(X0) ),
% 3.15/1.00      inference(unflattening,[status(thm)],[c_421]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_14,plain,
% 3.15/1.00      ( v4_relat_1(X0,X1)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.15/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_19,plain,
% 3.15/1.00      ( ~ v1_partfun1(X0,X1)
% 3.15/1.00      | ~ v4_relat_1(X0,X1)
% 3.15/1.00      | ~ v1_relat_1(X0)
% 3.15/1.00      | k1_relat_1(X0) = X1 ),
% 3.15/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_479,plain,
% 3.15/1.00      ( ~ v1_partfun1(X0,X1)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | ~ v1_relat_1(X0)
% 3.15/1.00      | k1_relat_1(X0) = X1 ),
% 3.15/1.00      inference(resolution,[status(thm)],[c_14,c_19]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_13,plain,
% 3.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | v1_relat_1(X0) ),
% 3.15/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_483,plain,
% 3.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | ~ v1_partfun1(X0,X1)
% 3.15/1.00      | k1_relat_1(X0) = X1 ),
% 3.15/1.00      inference(global_propositional_subsumption,
% 3.15/1.00                [status(thm)],
% 3.15/1.00                [c_479,c_19,c_14,c_13]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_484,plain,
% 3.15/1.00      ( ~ v1_partfun1(X0,X1)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | k1_relat_1(X0) = X1 ),
% 3.15/1.00      inference(renaming,[status(thm)],[c_483]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_523,plain,
% 3.15/1.00      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.15/1.00      | ~ v1_funct_1(X0)
% 3.15/1.00      | k1_relat_1(X0) = X1 ),
% 3.15/1.00      inference(resolution,[status(thm)],[c_422,c_484]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1201,plain,
% 3.15/1.00      ( k1_relat_1(X0) = X1
% 3.15/1.00      | v1_funct_2(X0,X1,u1_struct_0(sK1)) != iProver_top
% 3.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) != iProver_top
% 3.15/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1342,plain,
% 3.15/1.00      ( k1_relat_1(X0) = X1
% 3.15/1.00      | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
% 3.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.15/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
% 3.15/1.00      | v1_funct_1(X0) != iProver_top ),
% 3.15/1.00      inference(light_normalisation,[status(thm)],[c_1201,c_410]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1866,plain,
% 3.15/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.15/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.15/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
% 3.15/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_1242,c_1342]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_32,negated_conjecture,
% 3.15/1.00      ( v1_funct_1(sK2) ),
% 3.15/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_39,plain,
% 3.15/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_31,negated_conjecture,
% 3.15/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.15/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1206,plain,
% 3.15/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1236,plain,
% 3.15/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.15/1.00      inference(light_normalisation,[status(thm)],[c_1206,c_410,c_415]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2007,plain,
% 3.15/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
% 3.15/1.00      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.15/1.00      inference(global_propositional_subsumption,
% 3.15/1.00                [status(thm)],
% 3.15/1.00                [c_1866,c_39,c_1236]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2008,plain,
% 3.15/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.15/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top ),
% 3.15/1.00      inference(renaming,[status(thm)],[c_2007]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2015,plain,
% 3.15/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_1242,c_2008]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2018,plain,
% 3.15/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 3.15/1.00      inference(demodulation,[status(thm)],[c_2015,c_1242]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_15,plain,
% 3.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.15/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1212,plain,
% 3.15/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.15/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2371,plain,
% 3.15/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_2018,c_1212]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_29,negated_conjecture,
% 3.15/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.15/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1239,plain,
% 3.15/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.15/1.00      inference(light_normalisation,[status(thm)],[c_29,c_410,c_415]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2020,plain,
% 3.15/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.15/1.00      inference(demodulation,[status(thm)],[c_2015,c_1239]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2570,plain,
% 3.15/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.15/1.00      inference(demodulation,[status(thm)],[c_2371,c_2020]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2573,plain,
% 3.15/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.15/1.00      inference(demodulation,[status(thm)],[c_2570,c_2371]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_21,plain,
% 3.15/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.15/1.00      | ~ v1_funct_1(X0)
% 3.15/1.00      | ~ v2_funct_1(X0)
% 3.15/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.15/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1211,plain,
% 3.15/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 3.15/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.15/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.15/1.00      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.15/1.00      | v1_funct_1(X2) != iProver_top
% 3.15/1.00      | v2_funct_1(X2) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3251,plain,
% 3.15/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.15/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 3.15/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.15/1.00      | v1_funct_1(sK2) != iProver_top
% 3.15/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_2573,c_1211]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_28,negated_conjecture,
% 3.15/1.00      ( v2_funct_1(sK2) ),
% 3.15/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_42,plain,
% 3.15/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2576,plain,
% 3.15/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 3.15/1.00      inference(demodulation,[status(thm)],[c_2570,c_2018]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2019,plain,
% 3.15/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
% 3.15/1.00      inference(demodulation,[status(thm)],[c_2015,c_1236]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2577,plain,
% 3.15/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 3.15/1.00      inference(demodulation,[status(thm)],[c_2570,c_2019]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_4242,plain,
% 3.15/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 3.15/1.00      inference(global_propositional_subsumption,
% 3.15/1.00                [status(thm)],
% 3.15/1.00                [c_3251,c_39,c_42,c_2576,c_2577]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1205,plain,
% 3.15/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_7,plain,
% 3.15/1.00      ( ~ v1_funct_1(X0)
% 3.15/1.00      | ~ v2_funct_1(X0)
% 3.15/1.00      | ~ v1_relat_1(X0)
% 3.15/1.00      | k2_funct_1(X0) = k4_relat_1(X0) ),
% 3.15/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1219,plain,
% 3.15/1.00      ( k2_funct_1(X0) = k4_relat_1(X0)
% 3.15/1.00      | v1_funct_1(X0) != iProver_top
% 3.15/1.00      | v2_funct_1(X0) != iProver_top
% 3.15/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3259,plain,
% 3.15/1.00      ( k2_funct_1(sK2) = k4_relat_1(sK2)
% 3.15/1.00      | v2_funct_1(sK2) != iProver_top
% 3.15/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_1205,c_1219]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1478,plain,
% 3.15/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.15/1.00      | v1_relat_1(sK2) ),
% 3.15/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1493,plain,
% 3.15/1.00      ( ~ v1_funct_1(sK2)
% 3.15/1.00      | ~ v2_funct_1(sK2)
% 3.15/1.00      | ~ v1_relat_1(sK2)
% 3.15/1.00      | k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.15/1.00      inference(instantiation,[status(thm)],[c_7]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3458,plain,
% 3.15/1.00      ( k2_funct_1(sK2) = k4_relat_1(sK2) ),
% 3.15/1.00      inference(global_propositional_subsumption,
% 3.15/1.00                [status(thm)],
% 3.15/1.00                [c_3259,c_32,c_30,c_28,c_1478,c_1493]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_4246,plain,
% 3.15/1.00      ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 3.15/1.00      inference(light_normalisation,[status(thm)],[c_4242,c_3458]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_4249,plain,
% 3.15/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_4246,c_1212]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1213,plain,
% 3.15/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.15/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2372,plain,
% 3.15/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_2018,c_1213]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_5,plain,
% 3.15/1.00      ( ~ v1_relat_1(X0) | k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0) ),
% 3.15/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1221,plain,
% 3.15/1.00      ( k2_relat_1(k4_relat_1(X0)) = k1_relat_1(X0)
% 3.15/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2471,plain,
% 3.15/1.00      ( k2_relat_1(k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_2372,c_1221]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_4259,plain,
% 3.15/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.15/1.00      inference(light_normalisation,[status(thm)],[c_4249,c_2471]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_26,plain,
% 3.15/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | ~ v1_funct_1(X0)
% 3.15/1.00      | ~ v2_funct_1(X0)
% 3.15/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.15/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.15/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1209,plain,
% 3.15/1.00      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 3.15/1.00      | k2_relset_1(X0,X1,X2) != X1
% 3.15/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.15/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.15/1.00      | v1_funct_1(X2) != iProver_top
% 3.15/1.00      | v2_funct_1(X2) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_4366,plain,
% 3.15/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_funct_1(k4_relat_1(sK2))
% 3.15/1.00      | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.15/1.00      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.15/1.00      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.15/1.00      | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_4259,c_1209]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_12,plain,
% 3.15/1.00      ( ~ v1_funct_1(X0)
% 3.15/1.00      | ~ v2_funct_1(X0)
% 3.15/1.00      | ~ v1_relat_1(X0)
% 3.15/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.15/1.00      inference(cnf_transformation,[],[f70]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1214,plain,
% 3.15/1.00      ( k2_funct_1(k2_funct_1(X0)) = X0
% 3.15/1.00      | v1_funct_1(X0) != iProver_top
% 3.15/1.00      | v2_funct_1(X0) != iProver_top
% 3.15/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2743,plain,
% 3.15/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.15/1.00      | v2_funct_1(sK2) != iProver_top
% 3.15/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_1205,c_1214]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1496,plain,
% 3.15/1.00      ( ~ v1_funct_1(sK2)
% 3.15/1.00      | ~ v2_funct_1(sK2)
% 3.15/1.00      | ~ v1_relat_1(sK2)
% 3.15/1.00      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.15/1.00      inference(instantiation,[status(thm)],[c_12]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_2987,plain,
% 3.15/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.15/1.00      inference(global_propositional_subsumption,
% 3.15/1.00                [status(thm)],
% 3.15/1.00                [c_2743,c_32,c_30,c_28,c_1478,c_1496]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3463,plain,
% 3.15/1.00      ( k2_funct_1(k4_relat_1(sK2)) = sK2 ),
% 3.15/1.00      inference(demodulation,[status(thm)],[c_3458,c_2987]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_4372,plain,
% 3.15/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2
% 3.15/1.00      | v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.15/1.00      | m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.15/1.00      | v1_funct_1(k4_relat_1(sK2)) != iProver_top
% 3.15/1.00      | v2_funct_1(k4_relat_1(sK2)) != iProver_top ),
% 3.15/1.00      inference(light_normalisation,[status(thm)],[c_4366,c_3463]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_41,plain,
% 3.15/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1479,plain,
% 3.15/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.15/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_1478]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_23,plain,
% 3.15/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | ~ v1_funct_1(X0)
% 3.15/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.15/1.00      | ~ v2_funct_1(X0)
% 3.15/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.15/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_9,plain,
% 3.15/1.00      ( ~ v1_funct_1(X0)
% 3.15/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.15/1.00      | ~ v2_funct_1(X0)
% 3.15/1.00      | ~ v1_relat_1(X0) ),
% 3.15/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_203,plain,
% 3.15/1.00      ( ~ v2_funct_1(X0)
% 3.15/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.15/1.00      | ~ v1_funct_1(X0)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.15/1.00      inference(global_propositional_subsumption,
% 3.15/1.00                [status(thm)],
% 3.15/1.00                [c_23,c_13,c_9]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_204,plain,
% 3.15/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | ~ v1_funct_1(X0)
% 3.15/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.15/1.00      | ~ v2_funct_1(X0) ),
% 3.15/1.00      inference(renaming,[status(thm)],[c_203]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1204,plain,
% 3.15/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.15/1.00      | v1_funct_1(X0) != iProver_top
% 3.15/1.00      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.15/1.00      | v2_funct_1(X0) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_204]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1626,plain,
% 3.15/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.15/1.00      | v1_funct_1(sK2) != iProver_top
% 3.15/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_1242,c_1204]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1472,plain,
% 3.15/1.00      ( v1_funct_1(k2_funct_1(sK2))
% 3.15/1.00      | ~ v1_funct_1(sK2)
% 3.15/1.00      | ~ v2_funct_1(sK2)
% 3.15/1.00      | ~ v1_relat_1(sK2) ),
% 3.15/1.00      inference(instantiation,[status(thm)],[c_9]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1473,plain,
% 3.15/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.15/1.00      | v1_funct_1(sK2) != iProver_top
% 3.15/1.00      | v2_funct_1(sK2) != iProver_top
% 3.15/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_1472]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1901,plain,
% 3.15/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.15/1.00      inference(global_propositional_subsumption,
% 3.15/1.00                [status(thm)],
% 3.15/1.00                [c_1626,c_39,c_41,c_42,c_1473,c_1479]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3464,plain,
% 3.15/1.00      ( v1_funct_1(k4_relat_1(sK2)) = iProver_top ),
% 3.15/1.00      inference(demodulation,[status(thm)],[c_3458,c_1901]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_8,plain,
% 3.15/1.00      ( ~ v1_funct_1(X0)
% 3.15/1.00      | ~ v2_funct_1(X0)
% 3.15/1.00      | v2_funct_1(k2_funct_1(X0))
% 3.15/1.00      | ~ v1_relat_1(X0) ),
% 3.15/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1218,plain,
% 3.15/1.00      ( v1_funct_1(X0) != iProver_top
% 3.15/1.00      | v2_funct_1(X0) != iProver_top
% 3.15/1.00      | v2_funct_1(k2_funct_1(X0)) = iProver_top
% 3.15/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3481,plain,
% 3.15/1.00      ( v1_funct_1(sK2) != iProver_top
% 3.15/1.00      | v2_funct_1(k4_relat_1(sK2)) = iProver_top
% 3.15/1.00      | v2_funct_1(sK2) != iProver_top
% 3.15/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_3458,c_1218]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_22,plain,
% 3.15/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.15/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | ~ v1_funct_1(X0)
% 3.15/1.00      | ~ v2_funct_1(X0)
% 3.15/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.15/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1210,plain,
% 3.15/1.00      ( k2_relset_1(X0,X1,X2) != X1
% 3.15/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.15/1.00      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 3.15/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.15/1.00      | v1_funct_1(X2) != iProver_top
% 3.15/1.00      | v2_funct_1(X2) != iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_3043,plain,
% 3.15/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 3.15/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.15/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.15/1.00      | v1_funct_1(sK2) != iProver_top
% 3.15/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.15/1.00      inference(superposition,[status(thm)],[c_2573,c_1210]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_4234,plain,
% 3.15/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 3.15/1.00      inference(global_propositional_subsumption,
% 3.15/1.00                [status(thm)],
% 3.15/1.00                [c_3043,c_39,c_42,c_2576,c_2577]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_4238,plain,
% 3.15/1.00      ( v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 3.15/1.00      inference(light_normalisation,[status(thm)],[c_4234,c_3458]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_4426,plain,
% 3.15/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = sK2 ),
% 3.15/1.00      inference(global_propositional_subsumption,
% 3.15/1.00                [status(thm)],
% 3.15/1.00                [c_4372,c_39,c_41,c_42,c_1479,c_3464,c_3481,c_4238,
% 3.15/1.00                 c_4246]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_20,plain,
% 3.15/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 3.15/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.15/1.00      | ~ v1_funct_2(X3,X0,X1)
% 3.15/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.15/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.15/1.00      | ~ v1_funct_1(X2)
% 3.15/1.00      | ~ v1_funct_1(X3) ),
% 3.15/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_27,negated_conjecture,
% 3.15/1.00      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.15/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_444,plain,
% 3.15/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.15/1.00      | ~ v1_funct_2(X3,X1,X2)
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.00      | ~ v1_funct_1(X0)
% 3.15/1.00      | ~ v1_funct_1(X3)
% 3.15/1.00      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 3.15/1.00      | u1_struct_0(sK1) != X2
% 3.15/1.00      | u1_struct_0(sK0) != X1
% 3.15/1.00      | sK2 != X0 ),
% 3.15/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_445,plain,
% 3.15/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.15/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.15/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.15/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.15/1.00      | ~ v1_funct_1(X0)
% 3.15/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.15/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.15/1.00      inference(unflattening,[status(thm)],[c_444]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_721,plain,
% 3.15/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.15/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.15/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.15/1.00      | sP0_iProver_split
% 3.15/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.15/1.00      inference(splitting,
% 3.15/1.00                [splitting(split),new_symbols(definition,[])],
% 3.15/1.00                [c_445]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1202,plain,
% 3.15/1.00      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.15/1.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.15/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.15/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 3.15/1.00      | sP0_iProver_split = iProver_top ),
% 3.15/1.00      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 3.15/1.00  
% 3.15/1.00  cnf(c_1389,plain,
% 3.15/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.15/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.15/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.15/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 3.15/1.00      | sP0_iProver_split = iProver_top ),
% 3.15/1.00      inference(light_normalisation,[status(thm)],[c_1202,c_410,c_415]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_720,plain,
% 3.15/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.15/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.15/1.01      | ~ v1_funct_1(X0)
% 3.15/1.01      | ~ sP0_iProver_split ),
% 3.15/1.01      inference(splitting,
% 3.15/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.15/1.01                [c_445]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1203,plain,
% 3.15/1.01      ( v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.15/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.15/1.01      | v1_funct_1(X0) != iProver_top
% 3.15/1.01      | sP0_iProver_split != iProver_top ),
% 3.15/1.01      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1323,plain,
% 3.15/1.01      ( v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.15/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.15/1.01      | v1_funct_1(X0) != iProver_top
% 3.15/1.01      | sP0_iProver_split != iProver_top ),
% 3.15/1.01      inference(light_normalisation,[status(thm)],[c_1203,c_410,c_415]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1395,plain,
% 3.15/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.15/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.15/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.15/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.15/1.01      inference(forward_subsumption_resolution,
% 3.15/1.01                [status(thm)],
% 3.15/1.01                [c_1389,c_1323]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_2173,plain,
% 3.15/1.01      ( k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.15/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
% 3.15/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
% 3.15/1.01      | v1_funct_1(sK2) != iProver_top
% 3.15/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.15/1.01      inference(superposition,[status(thm)],[c_2020,c_1209]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_2381,plain,
% 3.15/1.01      ( k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.15/1.01      inference(global_propositional_subsumption,
% 3.15/1.01                [status(thm)],
% 3.15/1.01                [c_2173,c_39,c_42,c_2018,c_2019]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_2462,plain,
% 3.15/1.01      ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 3.15/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
% 3.15/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
% 3.15/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.15/1.01      inference(light_normalisation,[status(thm)],[c_1395,c_2015,c_2381]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_2574,plain,
% 3.15/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 3.15/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.15/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.15/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.15/1.01      inference(demodulation,[status(thm)],[c_2570,c_2462]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_3461,plain,
% 3.15/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) != sK2
% 3.15/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.15/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.15/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))) != iProver_top ),
% 3.15/1.01      inference(demodulation,[status(thm)],[c_3458,c_2574]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_4429,plain,
% 3.15/1.01      ( sK2 != sK2
% 3.15/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.15/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.15/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.15/1.01      inference(demodulation,[status(thm)],[c_4426,c_3461]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_723,plain,( X0 = X0 ),theory(equality) ).
% 3.15/1.01  
% 3.15/1.01  cnf(c_1689,plain,
% 3.15/1.01      ( sK2 = sK2 ),
% 3.15/1.01      inference(instantiation,[status(thm)],[c_723]) ).
% 3.15/1.01  
% 3.15/1.01  cnf(contradiction,plain,
% 3.15/1.01      ( $false ),
% 3.15/1.01      inference(minisat,[status(thm)],[c_4429,c_2577,c_2576,c_1689,c_39]) ).
% 3.15/1.01  
% 3.15/1.01  
% 3.15/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.15/1.01  
% 3.15/1.01  ------                               Statistics
% 3.15/1.01  
% 3.15/1.01  ------ General
% 3.15/1.01  
% 3.15/1.01  abstr_ref_over_cycles:                  0
% 3.15/1.01  abstr_ref_under_cycles:                 0
% 3.15/1.01  gc_basic_clause_elim:                   0
% 3.15/1.01  forced_gc_time:                         0
% 3.15/1.01  parsing_time:                           0.015
% 3.15/1.01  unif_index_cands_time:                  0.
% 3.15/1.01  unif_index_add_time:                    0.
% 3.15/1.01  orderings_time:                         0.
% 3.15/1.01  out_proof_time:                         0.023
% 3.15/1.01  total_time:                             0.218
% 3.15/1.01  num_of_symbols:                         58
% 3.15/1.01  num_of_terms:                           3462
% 3.15/1.01  
% 3.15/1.01  ------ Preprocessing
% 3.15/1.01  
% 3.15/1.01  num_of_splits:                          1
% 3.15/1.01  num_of_split_atoms:                     1
% 3.15/1.01  num_of_reused_defs:                     0
% 3.15/1.01  num_eq_ax_congr_red:                    8
% 3.15/1.01  num_of_sem_filtered_clauses:            1
% 3.15/1.01  num_of_subtypes:                        0
% 3.15/1.01  monotx_restored_types:                  0
% 3.15/1.01  sat_num_of_epr_types:                   0
% 3.15/1.01  sat_num_of_non_cyclic_types:            0
% 3.15/1.01  sat_guarded_non_collapsed_types:        0
% 3.15/1.01  num_pure_diseq_elim:                    0
% 3.15/1.01  simp_replaced_by:                       0
% 3.15/1.01  res_preprocessed:                       154
% 3.15/1.01  prep_upred:                             0
% 3.15/1.01  prep_unflattend:                        11
% 3.15/1.01  smt_new_axioms:                         0
% 3.15/1.01  pred_elim_cands:                        6
% 3.15/1.01  pred_elim:                              6
% 3.15/1.01  pred_elim_cl:                           7
% 3.15/1.01  pred_elim_cycles:                       8
% 3.15/1.01  merged_defs:                            0
% 3.15/1.01  merged_defs_ncl:                        0
% 3.15/1.01  bin_hyper_res:                          0
% 3.15/1.01  prep_cycles:                            4
% 3.15/1.01  pred_elim_time:                         0.005
% 3.15/1.01  splitting_time:                         0.
% 3.15/1.01  sem_filter_time:                        0.
% 3.15/1.01  monotx_time:                            0.
% 3.15/1.01  subtype_inf_time:                       0.
% 3.15/1.01  
% 3.15/1.01  ------ Problem properties
% 3.15/1.01  
% 3.15/1.01  clauses:                                28
% 3.15/1.01  conjectures:                            5
% 3.15/1.01  epr:                                    4
% 3.15/1.01  horn:                                   28
% 3.15/1.01  ground:                                 8
% 3.15/1.01  unary:                                  8
% 3.15/1.01  binary:                                 6
% 3.15/1.01  lits:                                   84
% 3.15/1.01  lits_eq:                                17
% 3.15/1.01  fd_pure:                                0
% 3.15/1.01  fd_pseudo:                              0
% 3.15/1.01  fd_cond:                                0
% 3.15/1.01  fd_pseudo_cond:                         2
% 3.15/1.01  ac_symbols:                             0
% 3.15/1.01  
% 3.15/1.01  ------ Propositional Solver
% 3.15/1.01  
% 3.15/1.01  prop_solver_calls:                      27
% 3.15/1.01  prop_fast_solver_calls:                 1133
% 3.15/1.01  smt_solver_calls:                       0
% 3.15/1.01  smt_fast_solver_calls:                  0
% 3.15/1.01  prop_num_of_clauses:                    1605
% 3.15/1.01  prop_preprocess_simplified:             5769
% 3.15/1.01  prop_fo_subsumed:                       37
% 3.15/1.01  prop_solver_time:                       0.
% 3.15/1.01  smt_solver_time:                        0.
% 3.15/1.01  smt_fast_solver_time:                   0.
% 3.15/1.01  prop_fast_solver_time:                  0.
% 3.15/1.01  prop_unsat_core_time:                   0.
% 3.15/1.01  
% 3.15/1.01  ------ QBF
% 3.15/1.01  
% 3.15/1.01  qbf_q_res:                              0
% 3.15/1.01  qbf_num_tautologies:                    0
% 3.15/1.01  qbf_prep_cycles:                        0
% 3.15/1.01  
% 3.15/1.01  ------ BMC1
% 3.15/1.01  
% 3.15/1.01  bmc1_current_bound:                     -1
% 3.15/1.01  bmc1_last_solved_bound:                 -1
% 3.15/1.01  bmc1_unsat_core_size:                   -1
% 3.15/1.01  bmc1_unsat_core_parents_size:           -1
% 3.15/1.01  bmc1_merge_next_fun:                    0
% 3.15/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.15/1.01  
% 3.15/1.01  ------ Instantiation
% 3.15/1.01  
% 3.15/1.01  inst_num_of_clauses:                    535
% 3.15/1.01  inst_num_in_passive:                    73
% 3.15/1.01  inst_num_in_active:                     320
% 3.15/1.01  inst_num_in_unprocessed:                142
% 3.15/1.01  inst_num_of_loops:                      340
% 3.15/1.01  inst_num_of_learning_restarts:          0
% 3.15/1.01  inst_num_moves_active_passive:          16
% 3.15/1.01  inst_lit_activity:                      0
% 3.15/1.01  inst_lit_activity_moves:                0
% 3.15/1.01  inst_num_tautologies:                   0
% 3.15/1.01  inst_num_prop_implied:                  0
% 3.15/1.01  inst_num_existing_simplified:           0
% 3.15/1.01  inst_num_eq_res_simplified:             0
% 3.15/1.01  inst_num_child_elim:                    0
% 3.15/1.01  inst_num_of_dismatching_blockings:      55
% 3.15/1.01  inst_num_of_non_proper_insts:           479
% 3.15/1.01  inst_num_of_duplicates:                 0
% 3.15/1.01  inst_inst_num_from_inst_to_res:         0
% 3.15/1.01  inst_dismatching_checking_time:         0.
% 3.15/1.01  
% 3.15/1.01  ------ Resolution
% 3.15/1.01  
% 3.15/1.01  res_num_of_clauses:                     0
% 3.15/1.01  res_num_in_passive:                     0
% 3.15/1.01  res_num_in_active:                      0
% 3.15/1.01  res_num_of_loops:                       158
% 3.15/1.01  res_forward_subset_subsumed:            43
% 3.15/1.01  res_backward_subset_subsumed:           6
% 3.15/1.01  res_forward_subsumed:                   0
% 3.15/1.01  res_backward_subsumed:                  0
% 3.15/1.01  res_forward_subsumption_resolution:     1
% 3.15/1.01  res_backward_subsumption_resolution:    0
% 3.15/1.01  res_clause_to_clause_subsumption:       154
% 3.15/1.01  res_orphan_elimination:                 0
% 3.15/1.01  res_tautology_del:                      88
% 3.15/1.01  res_num_eq_res_simplified:              0
% 3.15/1.01  res_num_sel_changes:                    0
% 3.15/1.01  res_moves_from_active_to_pass:          0
% 3.15/1.01  
% 3.15/1.01  ------ Superposition
% 3.15/1.01  
% 3.15/1.01  sup_time_total:                         0.
% 3.15/1.01  sup_time_generating:                    0.
% 3.15/1.01  sup_time_sim_full:                      0.
% 3.15/1.01  sup_time_sim_immed:                     0.
% 3.15/1.01  
% 3.15/1.01  sup_num_of_clauses:                     64
% 3.15/1.01  sup_num_in_active:                      47
% 3.15/1.01  sup_num_in_passive:                     17
% 3.15/1.01  sup_num_of_loops:                       66
% 3.15/1.01  sup_fw_superposition:                   28
% 3.15/1.01  sup_bw_superposition:                   43
% 3.15/1.01  sup_immediate_simplified:               29
% 3.15/1.01  sup_given_eliminated:                   0
% 3.15/1.01  comparisons_done:                       0
% 3.15/1.01  comparisons_avoided:                    0
% 3.15/1.01  
% 3.15/1.01  ------ Simplifications
% 3.15/1.01  
% 3.15/1.01  
% 3.15/1.01  sim_fw_subset_subsumed:                 11
% 3.15/1.01  sim_bw_subset_subsumed:                 4
% 3.15/1.01  sim_fw_subsumed:                        4
% 3.15/1.01  sim_bw_subsumed:                        0
% 3.15/1.01  sim_fw_subsumption_res:                 1
% 3.15/1.01  sim_bw_subsumption_res:                 0
% 3.15/1.01  sim_tautology_del:                      0
% 3.15/1.01  sim_eq_tautology_del:                   11
% 3.15/1.01  sim_eq_res_simp:                        0
% 3.15/1.01  sim_fw_demodulated:                     0
% 3.15/1.01  sim_bw_demodulated:                     18
% 3.15/1.01  sim_light_normalised:                   27
% 3.15/1.01  sim_joinable_taut:                      0
% 3.15/1.01  sim_joinable_simp:                      0
% 3.15/1.01  sim_ac_normalised:                      0
% 3.15/1.01  sim_smt_subsumption:                    0
% 3.15/1.01  
%------------------------------------------------------------------------------
