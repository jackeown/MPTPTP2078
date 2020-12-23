%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:34 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :  231 (11496 expanded)
%              Number of clauses        :  149 (3655 expanded)
%              Number of leaves         :   22 (3182 expanded)
%              Depth                    :   31
%              Number of atoms          :  879 (71950 expanded)
%              Number of equality atoms :  348 (11570 expanded)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f85,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f77,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f80,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f70,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f78,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f81,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f71,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f83,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f84,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f86,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f87,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f63,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f62,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f5])).

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

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f73,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f88,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_699,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1228,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_23,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_34,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_393,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_394,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_695,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_394])).

cnf(c_32,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_388,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_389,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_696,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_389])).

cnf(c_1254,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1228,c_695,c_696])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_24,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_375,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_376,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_47,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_378,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_33,c_32,c_47])).

cnf(c_400,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_378])).

cnf(c_401,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_400])).

cnf(c_18,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_497,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_401,c_18])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_513,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_497,c_13])).

cnf(c_693,plain,
    ( ~ v1_funct_2(X0_53,X0_54,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k1_relat_1(X0_53) = X0_54 ),
    inference(subtyping,[status(esa)],[c_513])).

cnf(c_1233,plain,
    ( k1_relat_1(X0_53) = X0_54
    | v1_funct_2(X0_53,X0_54,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_693])).

cnf(c_1320,plain,
    ( k1_relat_1(X0_53) = X0_54
    | v1_funct_2(X0_53,X0_54,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1233,c_696])).

cnf(c_1755,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1254,c_1320])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_698,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1229,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_1248,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1229,c_695,c_696])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_719,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1509,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(instantiation,[status(thm)],[c_719])).

cnf(c_1704,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1509])).

cnf(c_1705,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1704])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_718,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1742,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_718])).

cnf(c_1743,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1742])).

cnf(c_1810,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1755,c_38,c_40,c_1248,c_1705,c_1743])).

cnf(c_1813,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1810,c_1254])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_706,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1222,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_706])).

cnf(c_2067,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1813,c_1222])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_700,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1251,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_700,c_695,c_696])).

cnf(c_1815,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1810,c_1251])).

cnf(c_2229,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2067,c_1815])).

cnf(c_2264,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2229,c_2067])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_705,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
    | ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1223,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54))) = iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_3832,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2264,c_1223])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_41,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2266,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2229,c_1813])).

cnf(c_1814,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1810,c_1248])).

cnf(c_2267,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2229,c_1814])).

cnf(c_4812,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3832,c_38,c_41,c_2266,c_2267])).

cnf(c_4818,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4812,c_1222])).

cnf(c_701,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1227,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_711,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1217,plain,
    ( k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53)
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_711])).

cnf(c_2073,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_1217])).

cnf(c_777,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_711])).

cnf(c_2200,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2073,c_31,c_29,c_27,c_777,c_1704,c_1742])).

cnf(c_4825,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4818,c_2200])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_702,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1226,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53)
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_4833,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4825,c_1226])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_708,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k5_relat_1(X0_53,k2_funct_1(X0_53)) = k6_relat_1(k1_relat_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1220,plain,
    ( k5_relat_1(X0_53,k2_funct_1(X0_53)) = k6_relat_1(k1_relat_1(X0_53))
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_708])).

cnf(c_2546,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_1220])).

cnf(c_786,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_708])).

cnf(c_2804,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2546,c_31,c_29,c_27,c_786,c_1704,c_1742])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_707,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_relat_1(X0_53)
    | ~ v1_relat_1(X1_53)
    | k1_relat_1(X0_53) != k2_relat_1(X1_53)
    | k5_relat_1(X1_53,X0_53) != k6_relat_1(k2_relat_1(X0_53))
    | k2_funct_1(X0_53) = X1_53 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1221,plain,
    ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
    | k5_relat_1(X1_53,X0_53) != k6_relat_1(k2_relat_1(X0_53))
    | k2_funct_1(X0_53) = X1_53
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_3293,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2804,c_1221])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_710,plain,
    ( ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k1_relat_1(k2_funct_1(X0_53)) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1218,plain,
    ( k1_relat_1(k2_funct_1(X0_53)) = k2_relat_1(X0_53)
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_710])).

cnf(c_2123,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_1218])).

cnf(c_780,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_710])).

cnf(c_2204,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2123,c_31,c_29,c_27,c_780,c_1704,c_1742])).

cnf(c_3302,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3293,c_2200,c_2204])).

cnf(c_3303,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3302])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_717,plain,
    ( ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_funct_1(X0_53))
    | ~ v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_762,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_funct_1(X0_53)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_764,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_762])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_716,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | v1_relat_1(k2_funct_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_765,plain,
    ( v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k2_funct_1(X0_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_767,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_765])).

cnf(c_6,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_713,plain,
    ( v2_funct_1(X0_53)
    | ~ v2_funct_1(k5_relat_1(X1_53,X0_53))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | ~ v1_relat_1(X0_53)
    | ~ v1_relat_1(X1_53)
    | k1_relat_1(X0_53) != k2_relat_1(X1_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1215,plain,
    ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
    | v2_funct_1(X0_53) = iProver_top
    | v2_funct_1(k5_relat_1(X1_53,X0_53)) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(X1_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_2507,plain,
    ( k2_relat_1(X0_53) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2204,c_1215])).

cnf(c_2976,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | k2_relat_1(X0_53) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2507,c_38,c_40,c_764,c_767,c_1705,c_1743])).

cnf(c_2977,plain,
    ( k2_relat_1(X0_53) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_2976])).

cnf(c_2988,plain,
    ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2977])).

cnf(c_2993,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2988,c_2804])).

cnf(c_3071,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2993,c_38,c_40,c_1705,c_1743])).

cnf(c_4,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_715,plain,
    ( v2_funct_1(k6_relat_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1213,plain,
    ( v2_funct_1(k6_relat_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_715])).

cnf(c_3077,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3071,c_1213])).

cnf(c_4564,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3303,c_38,c_40,c_764,c_767,c_1705,c_1743,c_3077])).

cnf(c_4846,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4833,c_4564])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_704,plain,
    ( ~ v1_funct_2(X0_53,X0_54,X1_54)
    | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
    | ~ v2_funct_1(X0_53)
    | ~ v1_funct_1(X0_53)
    | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1224,plain,
    ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
    | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
    | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_704])).

cnf(c_3834,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2264,c_1224])).

cnf(c_4907,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4846,c_38,c_40,c_41,c_764,c_1705,c_1743,c_2266,c_2267,c_3077,c_3832,c_3834])).

cnf(c_19,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_423,plain,
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
    inference(resolution_lifted,[status(thm)],[c_19,c_26])).

cnf(c_424,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_423])).

cnf(c_694,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_424])).

cnf(c_721,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_694])).

cnf(c_1231,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_1423,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1231,c_695,c_696])).

cnf(c_720,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_694])).

cnf(c_1232,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_720])).

cnf(c_1311,plain,
    ( v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1232,c_695,c_696])).

cnf(c_1429,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1423,c_1311])).

cnf(c_2002,plain,
    ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1429,c_1810])).

cnf(c_2265,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2229,c_2002])).

cnf(c_3833,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2264,c_1226])).

cnf(c_4370,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3833,c_38,c_41,c_2266,c_2267])).

cnf(c_4702,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2265,c_4370])).

cnf(c_4910,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4907,c_4702])).

cnf(c_723,plain,
    ( X0_53 = X0_53 ),
    theory(equality)).

cnf(c_755,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_723])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4910,c_2267,c_2266,c_755,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:29:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.49/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.02  
% 2.49/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.49/1.02  
% 2.49/1.02  ------  iProver source info
% 2.49/1.02  
% 2.49/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.49/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.49/1.02  git: non_committed_changes: false
% 2.49/1.02  git: last_make_outside_of_git: false
% 2.49/1.02  
% 2.49/1.02  ------ 
% 2.49/1.02  
% 2.49/1.02  ------ Input Options
% 2.49/1.02  
% 2.49/1.02  --out_options                           all
% 2.49/1.02  --tptp_safe_out                         true
% 2.49/1.02  --problem_path                          ""
% 2.49/1.02  --include_path                          ""
% 2.49/1.02  --clausifier                            res/vclausify_rel
% 2.49/1.02  --clausifier_options                    --mode clausify
% 2.49/1.02  --stdin                                 false
% 2.49/1.02  --stats_out                             all
% 2.49/1.02  
% 2.49/1.02  ------ General Options
% 2.49/1.02  
% 2.49/1.02  --fof                                   false
% 2.49/1.02  --time_out_real                         305.
% 2.49/1.02  --time_out_virtual                      -1.
% 2.49/1.02  --symbol_type_check                     false
% 2.49/1.02  --clausify_out                          false
% 2.49/1.02  --sig_cnt_out                           false
% 2.49/1.02  --trig_cnt_out                          false
% 2.49/1.02  --trig_cnt_out_tolerance                1.
% 2.49/1.02  --trig_cnt_out_sk_spl                   false
% 2.49/1.02  --abstr_cl_out                          false
% 2.49/1.02  
% 2.49/1.02  ------ Global Options
% 2.49/1.02  
% 2.49/1.02  --schedule                              default
% 2.49/1.02  --add_important_lit                     false
% 2.49/1.02  --prop_solver_per_cl                    1000
% 2.49/1.02  --min_unsat_core                        false
% 2.49/1.02  --soft_assumptions                      false
% 2.49/1.02  --soft_lemma_size                       3
% 2.49/1.02  --prop_impl_unit_size                   0
% 2.49/1.02  --prop_impl_unit                        []
% 2.49/1.02  --share_sel_clauses                     true
% 2.49/1.02  --reset_solvers                         false
% 2.49/1.02  --bc_imp_inh                            [conj_cone]
% 2.49/1.02  --conj_cone_tolerance                   3.
% 2.49/1.02  --extra_neg_conj                        none
% 2.49/1.02  --large_theory_mode                     true
% 2.49/1.02  --prolific_symb_bound                   200
% 2.49/1.02  --lt_threshold                          2000
% 2.49/1.02  --clause_weak_htbl                      true
% 2.49/1.02  --gc_record_bc_elim                     false
% 2.49/1.02  
% 2.49/1.02  ------ Preprocessing Options
% 2.49/1.02  
% 2.49/1.02  --preprocessing_flag                    true
% 2.49/1.02  --time_out_prep_mult                    0.1
% 2.49/1.02  --splitting_mode                        input
% 2.49/1.02  --splitting_grd                         true
% 2.49/1.02  --splitting_cvd                         false
% 2.49/1.02  --splitting_cvd_svl                     false
% 2.49/1.02  --splitting_nvd                         32
% 2.49/1.02  --sub_typing                            true
% 2.49/1.02  --prep_gs_sim                           true
% 2.49/1.02  --prep_unflatten                        true
% 2.49/1.02  --prep_res_sim                          true
% 2.49/1.02  --prep_upred                            true
% 2.49/1.02  --prep_sem_filter                       exhaustive
% 2.49/1.02  --prep_sem_filter_out                   false
% 2.49/1.02  --pred_elim                             true
% 2.49/1.02  --res_sim_input                         true
% 2.49/1.02  --eq_ax_congr_red                       true
% 2.49/1.02  --pure_diseq_elim                       true
% 2.49/1.02  --brand_transform                       false
% 2.49/1.02  --non_eq_to_eq                          false
% 2.49/1.02  --prep_def_merge                        true
% 2.49/1.02  --prep_def_merge_prop_impl              false
% 2.49/1.02  --prep_def_merge_mbd                    true
% 2.49/1.02  --prep_def_merge_tr_red                 false
% 2.49/1.02  --prep_def_merge_tr_cl                  false
% 2.49/1.02  --smt_preprocessing                     true
% 2.49/1.02  --smt_ac_axioms                         fast
% 2.49/1.02  --preprocessed_out                      false
% 2.49/1.02  --preprocessed_stats                    false
% 2.49/1.02  
% 2.49/1.02  ------ Abstraction refinement Options
% 2.49/1.02  
% 2.49/1.02  --abstr_ref                             []
% 2.49/1.02  --abstr_ref_prep                        false
% 2.49/1.02  --abstr_ref_until_sat                   false
% 2.49/1.02  --abstr_ref_sig_restrict                funpre
% 2.49/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/1.02  --abstr_ref_under                       []
% 2.49/1.02  
% 2.49/1.02  ------ SAT Options
% 2.49/1.02  
% 2.49/1.02  --sat_mode                              false
% 2.49/1.02  --sat_fm_restart_options                ""
% 2.49/1.02  --sat_gr_def                            false
% 2.49/1.02  --sat_epr_types                         true
% 2.49/1.02  --sat_non_cyclic_types                  false
% 2.49/1.02  --sat_finite_models                     false
% 2.49/1.02  --sat_fm_lemmas                         false
% 2.49/1.02  --sat_fm_prep                           false
% 2.49/1.03  --sat_fm_uc_incr                        true
% 2.49/1.03  --sat_out_model                         small
% 2.49/1.03  --sat_out_clauses                       false
% 2.49/1.03  
% 2.49/1.03  ------ QBF Options
% 2.49/1.03  
% 2.49/1.03  --qbf_mode                              false
% 2.49/1.03  --qbf_elim_univ                         false
% 2.49/1.03  --qbf_dom_inst                          none
% 2.49/1.03  --qbf_dom_pre_inst                      false
% 2.49/1.03  --qbf_sk_in                             false
% 2.49/1.03  --qbf_pred_elim                         true
% 2.49/1.03  --qbf_split                             512
% 2.49/1.03  
% 2.49/1.03  ------ BMC1 Options
% 2.49/1.03  
% 2.49/1.03  --bmc1_incremental                      false
% 2.49/1.03  --bmc1_axioms                           reachable_all
% 2.49/1.03  --bmc1_min_bound                        0
% 2.49/1.03  --bmc1_max_bound                        -1
% 2.49/1.03  --bmc1_max_bound_default                -1
% 2.49/1.03  --bmc1_symbol_reachability              true
% 2.49/1.03  --bmc1_property_lemmas                  false
% 2.49/1.03  --bmc1_k_induction                      false
% 2.49/1.03  --bmc1_non_equiv_states                 false
% 2.49/1.03  --bmc1_deadlock                         false
% 2.49/1.03  --bmc1_ucm                              false
% 2.49/1.03  --bmc1_add_unsat_core                   none
% 2.49/1.03  --bmc1_unsat_core_children              false
% 2.49/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/1.03  --bmc1_out_stat                         full
% 2.49/1.03  --bmc1_ground_init                      false
% 2.49/1.03  --bmc1_pre_inst_next_state              false
% 2.49/1.03  --bmc1_pre_inst_state                   false
% 2.49/1.03  --bmc1_pre_inst_reach_state             false
% 2.49/1.03  --bmc1_out_unsat_core                   false
% 2.49/1.03  --bmc1_aig_witness_out                  false
% 2.49/1.03  --bmc1_verbose                          false
% 2.49/1.03  --bmc1_dump_clauses_tptp                false
% 2.49/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.49/1.03  --bmc1_dump_file                        -
% 2.49/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.49/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.49/1.03  --bmc1_ucm_extend_mode                  1
% 2.49/1.03  --bmc1_ucm_init_mode                    2
% 2.49/1.03  --bmc1_ucm_cone_mode                    none
% 2.49/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.49/1.03  --bmc1_ucm_relax_model                  4
% 2.49/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.49/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/1.03  --bmc1_ucm_layered_model                none
% 2.49/1.03  --bmc1_ucm_max_lemma_size               10
% 2.49/1.03  
% 2.49/1.03  ------ AIG Options
% 2.49/1.03  
% 2.49/1.03  --aig_mode                              false
% 2.49/1.03  
% 2.49/1.03  ------ Instantiation Options
% 2.49/1.03  
% 2.49/1.03  --instantiation_flag                    true
% 2.49/1.03  --inst_sos_flag                         false
% 2.49/1.03  --inst_sos_phase                        true
% 2.49/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/1.03  --inst_lit_sel_side                     num_symb
% 2.49/1.03  --inst_solver_per_active                1400
% 2.49/1.03  --inst_solver_calls_frac                1.
% 2.49/1.03  --inst_passive_queue_type               priority_queues
% 2.49/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/1.03  --inst_passive_queues_freq              [25;2]
% 2.49/1.03  --inst_dismatching                      true
% 2.49/1.03  --inst_eager_unprocessed_to_passive     true
% 2.49/1.03  --inst_prop_sim_given                   true
% 2.49/1.03  --inst_prop_sim_new                     false
% 2.49/1.03  --inst_subs_new                         false
% 2.49/1.03  --inst_eq_res_simp                      false
% 2.49/1.03  --inst_subs_given                       false
% 2.49/1.03  --inst_orphan_elimination               true
% 2.49/1.03  --inst_learning_loop_flag               true
% 2.49/1.03  --inst_learning_start                   3000
% 2.49/1.03  --inst_learning_factor                  2
% 2.49/1.03  --inst_start_prop_sim_after_learn       3
% 2.49/1.03  --inst_sel_renew                        solver
% 2.49/1.03  --inst_lit_activity_flag                true
% 2.49/1.03  --inst_restr_to_given                   false
% 2.49/1.03  --inst_activity_threshold               500
% 2.49/1.03  --inst_out_proof                        true
% 2.49/1.03  
% 2.49/1.03  ------ Resolution Options
% 2.49/1.03  
% 2.49/1.03  --resolution_flag                       true
% 2.49/1.03  --res_lit_sel                           adaptive
% 2.49/1.03  --res_lit_sel_side                      none
% 2.49/1.03  --res_ordering                          kbo
% 2.49/1.03  --res_to_prop_solver                    active
% 2.49/1.03  --res_prop_simpl_new                    false
% 2.49/1.03  --res_prop_simpl_given                  true
% 2.49/1.03  --res_passive_queue_type                priority_queues
% 2.49/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/1.03  --res_passive_queues_freq               [15;5]
% 2.49/1.03  --res_forward_subs                      full
% 2.49/1.03  --res_backward_subs                     full
% 2.49/1.03  --res_forward_subs_resolution           true
% 2.49/1.03  --res_backward_subs_resolution          true
% 2.49/1.03  --res_orphan_elimination                true
% 2.49/1.03  --res_time_limit                        2.
% 2.49/1.03  --res_out_proof                         true
% 2.49/1.03  
% 2.49/1.03  ------ Superposition Options
% 2.49/1.03  
% 2.49/1.03  --superposition_flag                    true
% 2.49/1.03  --sup_passive_queue_type                priority_queues
% 2.49/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.49/1.03  --demod_completeness_check              fast
% 2.49/1.03  --demod_use_ground                      true
% 2.49/1.03  --sup_to_prop_solver                    passive
% 2.49/1.03  --sup_prop_simpl_new                    true
% 2.49/1.03  --sup_prop_simpl_given                  true
% 2.49/1.03  --sup_fun_splitting                     false
% 2.49/1.03  --sup_smt_interval                      50000
% 2.49/1.03  
% 2.49/1.03  ------ Superposition Simplification Setup
% 2.49/1.03  
% 2.49/1.03  --sup_indices_passive                   []
% 2.49/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.03  --sup_full_bw                           [BwDemod]
% 2.49/1.03  --sup_immed_triv                        [TrivRules]
% 2.49/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.03  --sup_immed_bw_main                     []
% 2.49/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.03  
% 2.49/1.03  ------ Combination Options
% 2.49/1.03  
% 2.49/1.03  --comb_res_mult                         3
% 2.49/1.03  --comb_sup_mult                         2
% 2.49/1.03  --comb_inst_mult                        10
% 2.49/1.03  
% 2.49/1.03  ------ Debug Options
% 2.49/1.03  
% 2.49/1.03  --dbg_backtrace                         false
% 2.49/1.03  --dbg_dump_prop_clauses                 false
% 2.49/1.03  --dbg_dump_prop_clauses_file            -
% 2.49/1.03  --dbg_out_stat                          false
% 2.49/1.03  ------ Parsing...
% 2.49/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.49/1.03  
% 2.49/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.49/1.03  
% 2.49/1.03  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.49/1.03  
% 2.49/1.03  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.49/1.03  ------ Proving...
% 2.49/1.03  ------ Problem Properties 
% 2.49/1.03  
% 2.49/1.03  
% 2.49/1.03  clauses                                 28
% 2.49/1.03  conjectures                             5
% 2.49/1.03  EPR                                     2
% 2.49/1.03  Horn                                    28
% 2.49/1.03  unary                                   10
% 2.49/1.03  binary                                  1
% 2.49/1.03  lits                                    97
% 2.49/1.03  lits eq                                 20
% 2.49/1.03  fd_pure                                 0
% 2.49/1.03  fd_pseudo                               0
% 2.49/1.03  fd_cond                                 0
% 2.49/1.03  fd_pseudo_cond                          2
% 2.49/1.03  AC symbols                              0
% 2.49/1.03  
% 2.49/1.03  ------ Schedule dynamic 5 is on 
% 2.49/1.03  
% 2.49/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.49/1.03  
% 2.49/1.03  
% 2.49/1.03  ------ 
% 2.49/1.03  Current options:
% 2.49/1.03  ------ 
% 2.49/1.03  
% 2.49/1.03  ------ Input Options
% 2.49/1.03  
% 2.49/1.03  --out_options                           all
% 2.49/1.03  --tptp_safe_out                         true
% 2.49/1.03  --problem_path                          ""
% 2.49/1.03  --include_path                          ""
% 2.49/1.03  --clausifier                            res/vclausify_rel
% 2.49/1.03  --clausifier_options                    --mode clausify
% 2.49/1.03  --stdin                                 false
% 2.49/1.03  --stats_out                             all
% 2.49/1.03  
% 2.49/1.03  ------ General Options
% 2.49/1.03  
% 2.49/1.03  --fof                                   false
% 2.49/1.03  --time_out_real                         305.
% 2.49/1.03  --time_out_virtual                      -1.
% 2.49/1.03  --symbol_type_check                     false
% 2.49/1.03  --clausify_out                          false
% 2.49/1.03  --sig_cnt_out                           false
% 2.49/1.03  --trig_cnt_out                          false
% 2.49/1.03  --trig_cnt_out_tolerance                1.
% 2.49/1.03  --trig_cnt_out_sk_spl                   false
% 2.49/1.03  --abstr_cl_out                          false
% 2.49/1.03  
% 2.49/1.03  ------ Global Options
% 2.49/1.03  
% 2.49/1.03  --schedule                              default
% 2.49/1.03  --add_important_lit                     false
% 2.49/1.03  --prop_solver_per_cl                    1000
% 2.49/1.03  --min_unsat_core                        false
% 2.49/1.03  --soft_assumptions                      false
% 2.49/1.03  --soft_lemma_size                       3
% 2.49/1.03  --prop_impl_unit_size                   0
% 2.49/1.03  --prop_impl_unit                        []
% 2.49/1.03  --share_sel_clauses                     true
% 2.49/1.03  --reset_solvers                         false
% 2.49/1.03  --bc_imp_inh                            [conj_cone]
% 2.49/1.03  --conj_cone_tolerance                   3.
% 2.49/1.03  --extra_neg_conj                        none
% 2.49/1.03  --large_theory_mode                     true
% 2.49/1.03  --prolific_symb_bound                   200
% 2.49/1.03  --lt_threshold                          2000
% 2.49/1.03  --clause_weak_htbl                      true
% 2.49/1.03  --gc_record_bc_elim                     false
% 2.49/1.03  
% 2.49/1.03  ------ Preprocessing Options
% 2.49/1.03  
% 2.49/1.03  --preprocessing_flag                    true
% 2.49/1.03  --time_out_prep_mult                    0.1
% 2.49/1.03  --splitting_mode                        input
% 2.49/1.03  --splitting_grd                         true
% 2.49/1.03  --splitting_cvd                         false
% 2.49/1.03  --splitting_cvd_svl                     false
% 2.49/1.03  --splitting_nvd                         32
% 2.49/1.03  --sub_typing                            true
% 2.49/1.03  --prep_gs_sim                           true
% 2.49/1.03  --prep_unflatten                        true
% 2.49/1.03  --prep_res_sim                          true
% 2.49/1.03  --prep_upred                            true
% 2.49/1.03  --prep_sem_filter                       exhaustive
% 2.49/1.03  --prep_sem_filter_out                   false
% 2.49/1.03  --pred_elim                             true
% 2.49/1.03  --res_sim_input                         true
% 2.49/1.03  --eq_ax_congr_red                       true
% 2.49/1.03  --pure_diseq_elim                       true
% 2.49/1.03  --brand_transform                       false
% 2.49/1.03  --non_eq_to_eq                          false
% 2.49/1.03  --prep_def_merge                        true
% 2.49/1.03  --prep_def_merge_prop_impl              false
% 2.49/1.03  --prep_def_merge_mbd                    true
% 2.49/1.03  --prep_def_merge_tr_red                 false
% 2.49/1.03  --prep_def_merge_tr_cl                  false
% 2.49/1.03  --smt_preprocessing                     true
% 2.49/1.03  --smt_ac_axioms                         fast
% 2.49/1.03  --preprocessed_out                      false
% 2.49/1.03  --preprocessed_stats                    false
% 2.49/1.03  
% 2.49/1.03  ------ Abstraction refinement Options
% 2.49/1.03  
% 2.49/1.03  --abstr_ref                             []
% 2.49/1.03  --abstr_ref_prep                        false
% 2.49/1.03  --abstr_ref_until_sat                   false
% 2.49/1.03  --abstr_ref_sig_restrict                funpre
% 2.49/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.49/1.03  --abstr_ref_under                       []
% 2.49/1.03  
% 2.49/1.03  ------ SAT Options
% 2.49/1.03  
% 2.49/1.03  --sat_mode                              false
% 2.49/1.03  --sat_fm_restart_options                ""
% 2.49/1.03  --sat_gr_def                            false
% 2.49/1.03  --sat_epr_types                         true
% 2.49/1.03  --sat_non_cyclic_types                  false
% 2.49/1.03  --sat_finite_models                     false
% 2.49/1.03  --sat_fm_lemmas                         false
% 2.49/1.03  --sat_fm_prep                           false
% 2.49/1.03  --sat_fm_uc_incr                        true
% 2.49/1.03  --sat_out_model                         small
% 2.49/1.03  --sat_out_clauses                       false
% 2.49/1.03  
% 2.49/1.03  ------ QBF Options
% 2.49/1.03  
% 2.49/1.03  --qbf_mode                              false
% 2.49/1.03  --qbf_elim_univ                         false
% 2.49/1.03  --qbf_dom_inst                          none
% 2.49/1.03  --qbf_dom_pre_inst                      false
% 2.49/1.03  --qbf_sk_in                             false
% 2.49/1.03  --qbf_pred_elim                         true
% 2.49/1.03  --qbf_split                             512
% 2.49/1.03  
% 2.49/1.03  ------ BMC1 Options
% 2.49/1.03  
% 2.49/1.03  --bmc1_incremental                      false
% 2.49/1.03  --bmc1_axioms                           reachable_all
% 2.49/1.03  --bmc1_min_bound                        0
% 2.49/1.03  --bmc1_max_bound                        -1
% 2.49/1.03  --bmc1_max_bound_default                -1
% 2.49/1.03  --bmc1_symbol_reachability              true
% 2.49/1.03  --bmc1_property_lemmas                  false
% 2.49/1.03  --bmc1_k_induction                      false
% 2.49/1.03  --bmc1_non_equiv_states                 false
% 2.49/1.03  --bmc1_deadlock                         false
% 2.49/1.03  --bmc1_ucm                              false
% 2.49/1.03  --bmc1_add_unsat_core                   none
% 2.49/1.03  --bmc1_unsat_core_children              false
% 2.49/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.49/1.03  --bmc1_out_stat                         full
% 2.49/1.03  --bmc1_ground_init                      false
% 2.49/1.03  --bmc1_pre_inst_next_state              false
% 2.49/1.03  --bmc1_pre_inst_state                   false
% 2.49/1.03  --bmc1_pre_inst_reach_state             false
% 2.49/1.03  --bmc1_out_unsat_core                   false
% 2.49/1.03  --bmc1_aig_witness_out                  false
% 2.49/1.03  --bmc1_verbose                          false
% 2.49/1.03  --bmc1_dump_clauses_tptp                false
% 2.49/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.49/1.03  --bmc1_dump_file                        -
% 2.49/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.49/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.49/1.03  --bmc1_ucm_extend_mode                  1
% 2.49/1.03  --bmc1_ucm_init_mode                    2
% 2.49/1.03  --bmc1_ucm_cone_mode                    none
% 2.49/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.49/1.03  --bmc1_ucm_relax_model                  4
% 2.49/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.49/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.49/1.03  --bmc1_ucm_layered_model                none
% 2.49/1.03  --bmc1_ucm_max_lemma_size               10
% 2.49/1.03  
% 2.49/1.03  ------ AIG Options
% 2.49/1.03  
% 2.49/1.03  --aig_mode                              false
% 2.49/1.03  
% 2.49/1.03  ------ Instantiation Options
% 2.49/1.03  
% 2.49/1.03  --instantiation_flag                    true
% 2.49/1.03  --inst_sos_flag                         false
% 2.49/1.03  --inst_sos_phase                        true
% 2.49/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.49/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.49/1.03  --inst_lit_sel_side                     none
% 2.49/1.03  --inst_solver_per_active                1400
% 2.49/1.03  --inst_solver_calls_frac                1.
% 2.49/1.03  --inst_passive_queue_type               priority_queues
% 2.49/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.49/1.03  --inst_passive_queues_freq              [25;2]
% 2.49/1.03  --inst_dismatching                      true
% 2.49/1.03  --inst_eager_unprocessed_to_passive     true
% 2.49/1.03  --inst_prop_sim_given                   true
% 2.49/1.03  --inst_prop_sim_new                     false
% 2.49/1.03  --inst_subs_new                         false
% 2.49/1.03  --inst_eq_res_simp                      false
% 2.49/1.03  --inst_subs_given                       false
% 2.49/1.03  --inst_orphan_elimination               true
% 2.49/1.03  --inst_learning_loop_flag               true
% 2.49/1.03  --inst_learning_start                   3000
% 2.49/1.03  --inst_learning_factor                  2
% 2.49/1.03  --inst_start_prop_sim_after_learn       3
% 2.49/1.03  --inst_sel_renew                        solver
% 2.49/1.03  --inst_lit_activity_flag                true
% 2.49/1.03  --inst_restr_to_given                   false
% 2.49/1.03  --inst_activity_threshold               500
% 2.49/1.03  --inst_out_proof                        true
% 2.49/1.03  
% 2.49/1.03  ------ Resolution Options
% 2.49/1.03  
% 2.49/1.03  --resolution_flag                       false
% 2.49/1.03  --res_lit_sel                           adaptive
% 2.49/1.03  --res_lit_sel_side                      none
% 2.49/1.03  --res_ordering                          kbo
% 2.49/1.03  --res_to_prop_solver                    active
% 2.49/1.03  --res_prop_simpl_new                    false
% 2.49/1.03  --res_prop_simpl_given                  true
% 2.49/1.03  --res_passive_queue_type                priority_queues
% 2.49/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.49/1.03  --res_passive_queues_freq               [15;5]
% 2.49/1.03  --res_forward_subs                      full
% 2.49/1.03  --res_backward_subs                     full
% 2.49/1.03  --res_forward_subs_resolution           true
% 2.49/1.03  --res_backward_subs_resolution          true
% 2.49/1.03  --res_orphan_elimination                true
% 2.49/1.03  --res_time_limit                        2.
% 2.49/1.03  --res_out_proof                         true
% 2.49/1.03  
% 2.49/1.03  ------ Superposition Options
% 2.49/1.03  
% 2.49/1.03  --superposition_flag                    true
% 2.49/1.03  --sup_passive_queue_type                priority_queues
% 2.49/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.49/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.49/1.03  --demod_completeness_check              fast
% 2.49/1.03  --demod_use_ground                      true
% 2.49/1.03  --sup_to_prop_solver                    passive
% 2.49/1.03  --sup_prop_simpl_new                    true
% 2.49/1.03  --sup_prop_simpl_given                  true
% 2.49/1.03  --sup_fun_splitting                     false
% 2.49/1.03  --sup_smt_interval                      50000
% 2.49/1.03  
% 2.49/1.03  ------ Superposition Simplification Setup
% 2.49/1.03  
% 2.49/1.03  --sup_indices_passive                   []
% 2.49/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.49/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.49/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.03  --sup_full_bw                           [BwDemod]
% 2.49/1.03  --sup_immed_triv                        [TrivRules]
% 2.49/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.49/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.03  --sup_immed_bw_main                     []
% 2.49/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.49/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.49/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.49/1.03  
% 2.49/1.03  ------ Combination Options
% 2.49/1.03  
% 2.49/1.03  --comb_res_mult                         3
% 2.49/1.03  --comb_sup_mult                         2
% 2.49/1.03  --comb_inst_mult                        10
% 2.49/1.03  
% 2.49/1.03  ------ Debug Options
% 2.49/1.03  
% 2.49/1.03  --dbg_backtrace                         false
% 2.49/1.03  --dbg_dump_prop_clauses                 false
% 2.49/1.03  --dbg_dump_prop_clauses_file            -
% 2.49/1.03  --dbg_out_stat                          false
% 2.49/1.03  
% 2.49/1.03  
% 2.49/1.03  
% 2.49/1.03  
% 2.49/1.03  ------ Proving...
% 2.49/1.03  
% 2.49/1.03  
% 2.49/1.03  % SZS status Theorem for theBenchmark.p
% 2.49/1.03  
% 2.49/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.49/1.03  
% 2.49/1.03  fof(f18,conjecture,(
% 2.49/1.03    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f19,negated_conjecture,(
% 2.49/1.03    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.49/1.03    inference(negated_conjecture,[],[f18])).
% 2.49/1.03  
% 2.49/1.03  fof(f47,plain,(
% 2.49/1.03    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.49/1.03    inference(ennf_transformation,[],[f19])).
% 2.49/1.03  
% 2.49/1.03  fof(f48,plain,(
% 2.49/1.03    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.49/1.03    inference(flattening,[],[f47])).
% 2.49/1.03  
% 2.49/1.03  fof(f52,plain,(
% 2.49/1.03    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.49/1.03    introduced(choice_axiom,[])).
% 2.49/1.03  
% 2.49/1.03  fof(f51,plain,(
% 2.49/1.03    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.49/1.03    introduced(choice_axiom,[])).
% 2.49/1.03  
% 2.49/1.03  fof(f50,plain,(
% 2.49/1.03    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.49/1.03    introduced(choice_axiom,[])).
% 2.49/1.03  
% 2.49/1.03  fof(f53,plain,(
% 2.49/1.03    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.49/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f48,f52,f51,f50])).
% 2.49/1.03  
% 2.49/1.03  fof(f85,plain,(
% 2.49/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.49/1.03    inference(cnf_transformation,[],[f53])).
% 2.49/1.03  
% 2.49/1.03  fof(f15,axiom,(
% 2.49/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f42,plain,(
% 2.49/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.49/1.03    inference(ennf_transformation,[],[f15])).
% 2.49/1.03  
% 2.49/1.03  fof(f77,plain,(
% 2.49/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f42])).
% 2.49/1.03  
% 2.49/1.03  fof(f80,plain,(
% 2.49/1.03    l1_struct_0(sK0)),
% 2.49/1.03    inference(cnf_transformation,[],[f53])).
% 2.49/1.03  
% 2.49/1.03  fof(f82,plain,(
% 2.49/1.03    l1_struct_0(sK1)),
% 2.49/1.03    inference(cnf_transformation,[],[f53])).
% 2.49/1.03  
% 2.49/1.03  fof(f11,axiom,(
% 2.49/1.03    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f34,plain,(
% 2.49/1.03    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.49/1.03    inference(ennf_transformation,[],[f11])).
% 2.49/1.03  
% 2.49/1.03  fof(f35,plain,(
% 2.49/1.03    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.49/1.03    inference(flattening,[],[f34])).
% 2.49/1.03  
% 2.49/1.03  fof(f70,plain,(
% 2.49/1.03    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f35])).
% 2.49/1.03  
% 2.49/1.03  fof(f16,axiom,(
% 2.49/1.03    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f43,plain,(
% 2.49/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.49/1.03    inference(ennf_transformation,[],[f16])).
% 2.49/1.03  
% 2.49/1.03  fof(f44,plain,(
% 2.49/1.03    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.49/1.03    inference(flattening,[],[f43])).
% 2.49/1.03  
% 2.49/1.03  fof(f78,plain,(
% 2.49/1.03    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f44])).
% 2.49/1.03  
% 2.49/1.03  fof(f81,plain,(
% 2.49/1.03    ~v2_struct_0(sK1)),
% 2.49/1.03    inference(cnf_transformation,[],[f53])).
% 2.49/1.03  
% 2.49/1.03  fof(f12,axiom,(
% 2.49/1.03    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f36,plain,(
% 2.49/1.03    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.49/1.03    inference(ennf_transformation,[],[f12])).
% 2.49/1.03  
% 2.49/1.03  fof(f37,plain,(
% 2.49/1.03    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.49/1.03    inference(flattening,[],[f36])).
% 2.49/1.03  
% 2.49/1.03  fof(f49,plain,(
% 2.49/1.03    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.49/1.03    inference(nnf_transformation,[],[f37])).
% 2.49/1.03  
% 2.49/1.03  fof(f71,plain,(
% 2.49/1.03    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f49])).
% 2.49/1.03  
% 2.49/1.03  fof(f9,axiom,(
% 2.49/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f20,plain,(
% 2.49/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.49/1.03    inference(pure_predicate_removal,[],[f9])).
% 2.49/1.03  
% 2.49/1.03  fof(f32,plain,(
% 2.49/1.03    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.49/1.03    inference(ennf_transformation,[],[f20])).
% 2.49/1.03  
% 2.49/1.03  fof(f67,plain,(
% 2.49/1.03    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.49/1.03    inference(cnf_transformation,[],[f32])).
% 2.49/1.03  
% 2.49/1.03  fof(f83,plain,(
% 2.49/1.03    v1_funct_1(sK2)),
% 2.49/1.03    inference(cnf_transformation,[],[f53])).
% 2.49/1.03  
% 2.49/1.03  fof(f84,plain,(
% 2.49/1.03    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.49/1.03    inference(cnf_transformation,[],[f53])).
% 2.49/1.03  
% 2.49/1.03  fof(f1,axiom,(
% 2.49/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f21,plain,(
% 2.49/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.49/1.03    inference(ennf_transformation,[],[f1])).
% 2.49/1.03  
% 2.49/1.03  fof(f54,plain,(
% 2.49/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f21])).
% 2.49/1.03  
% 2.49/1.03  fof(f2,axiom,(
% 2.49/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f55,plain,(
% 2.49/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.49/1.03    inference(cnf_transformation,[],[f2])).
% 2.49/1.03  
% 2.49/1.03  fof(f10,axiom,(
% 2.49/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f33,plain,(
% 2.49/1.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.49/1.03    inference(ennf_transformation,[],[f10])).
% 2.49/1.03  
% 2.49/1.03  fof(f68,plain,(
% 2.49/1.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.49/1.03    inference(cnf_transformation,[],[f33])).
% 2.49/1.03  
% 2.49/1.03  fof(f86,plain,(
% 2.49/1.03    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.49/1.03    inference(cnf_transformation,[],[f53])).
% 2.49/1.03  
% 2.49/1.03  fof(f14,axiom,(
% 2.49/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f40,plain,(
% 2.49/1.03    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.49/1.03    inference(ennf_transformation,[],[f14])).
% 2.49/1.03  
% 2.49/1.03  fof(f41,plain,(
% 2.49/1.03    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.49/1.03    inference(flattening,[],[f40])).
% 2.49/1.03  
% 2.49/1.03  fof(f76,plain,(
% 2.49/1.03    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f41])).
% 2.49/1.03  
% 2.49/1.03  fof(f87,plain,(
% 2.49/1.03    v2_funct_1(sK2)),
% 2.49/1.03    inference(cnf_transformation,[],[f53])).
% 2.49/1.03  
% 2.49/1.03  fof(f6,axiom,(
% 2.49/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f26,plain,(
% 2.49/1.03    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.49/1.03    inference(ennf_transformation,[],[f6])).
% 2.49/1.03  
% 2.49/1.03  fof(f27,plain,(
% 2.49/1.03    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.49/1.03    inference(flattening,[],[f26])).
% 2.49/1.03  
% 2.49/1.03  fof(f63,plain,(
% 2.49/1.03    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f27])).
% 2.49/1.03  
% 2.49/1.03  fof(f17,axiom,(
% 2.49/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f45,plain,(
% 2.49/1.03    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.49/1.03    inference(ennf_transformation,[],[f17])).
% 2.49/1.03  
% 2.49/1.03  fof(f46,plain,(
% 2.49/1.03    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.49/1.03    inference(flattening,[],[f45])).
% 2.49/1.03  
% 2.49/1.03  fof(f79,plain,(
% 2.49/1.03    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f46])).
% 2.49/1.03  
% 2.49/1.03  fof(f7,axiom,(
% 2.49/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f28,plain,(
% 2.49/1.03    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.49/1.03    inference(ennf_transformation,[],[f7])).
% 2.49/1.03  
% 2.49/1.03  fof(f29,plain,(
% 2.49/1.03    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.49/1.03    inference(flattening,[],[f28])).
% 2.49/1.03  
% 2.49/1.03  fof(f64,plain,(
% 2.49/1.03    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f29])).
% 2.49/1.03  
% 2.49/1.03  fof(f8,axiom,(
% 2.49/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f30,plain,(
% 2.49/1.03    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.49/1.03    inference(ennf_transformation,[],[f8])).
% 2.49/1.03  
% 2.49/1.03  fof(f31,plain,(
% 2.49/1.03    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.49/1.03    inference(flattening,[],[f30])).
% 2.49/1.03  
% 2.49/1.03  fof(f66,plain,(
% 2.49/1.03    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f31])).
% 2.49/1.03  
% 2.49/1.03  fof(f62,plain,(
% 2.49/1.03    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f27])).
% 2.49/1.03  
% 2.49/1.03  fof(f3,axiom,(
% 2.49/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f22,plain,(
% 2.49/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.49/1.03    inference(ennf_transformation,[],[f3])).
% 2.49/1.03  
% 2.49/1.03  fof(f23,plain,(
% 2.49/1.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.49/1.03    inference(flattening,[],[f22])).
% 2.49/1.03  
% 2.49/1.03  fof(f57,plain,(
% 2.49/1.03    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f23])).
% 2.49/1.03  
% 2.49/1.03  fof(f56,plain,(
% 2.49/1.03    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f23])).
% 2.49/1.03  
% 2.49/1.03  fof(f5,axiom,(
% 2.49/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f24,plain,(
% 2.49/1.03    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.49/1.03    inference(ennf_transformation,[],[f5])).
% 2.49/1.03  
% 2.49/1.03  fof(f25,plain,(
% 2.49/1.03    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.49/1.03    inference(flattening,[],[f24])).
% 2.49/1.03  
% 2.49/1.03  fof(f61,plain,(
% 2.49/1.03    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f25])).
% 2.49/1.03  
% 2.49/1.03  fof(f4,axiom,(
% 2.49/1.03    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f59,plain,(
% 2.49/1.03    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.49/1.03    inference(cnf_transformation,[],[f4])).
% 2.49/1.03  
% 2.49/1.03  fof(f75,plain,(
% 2.49/1.03    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f41])).
% 2.49/1.03  
% 2.49/1.03  fof(f13,axiom,(
% 2.49/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.49/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.49/1.03  
% 2.49/1.03  fof(f38,plain,(
% 2.49/1.03    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.49/1.03    inference(ennf_transformation,[],[f13])).
% 2.49/1.03  
% 2.49/1.03  fof(f39,plain,(
% 2.49/1.03    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.49/1.03    inference(flattening,[],[f38])).
% 2.49/1.03  
% 2.49/1.03  fof(f73,plain,(
% 2.49/1.03    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.49/1.03    inference(cnf_transformation,[],[f39])).
% 2.49/1.03  
% 2.49/1.03  fof(f88,plain,(
% 2.49/1.03    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.49/1.03    inference(cnf_transformation,[],[f53])).
% 2.49/1.03  
% 2.49/1.03  cnf(c_29,negated_conjecture,
% 2.49/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.49/1.03      inference(cnf_transformation,[],[f85]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_699,negated_conjecture,
% 2.49/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_29]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1228,plain,
% 2.49/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_23,plain,
% 2.49/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.49/1.03      inference(cnf_transformation,[],[f77]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_34,negated_conjecture,
% 2.49/1.03      ( l1_struct_0(sK0) ),
% 2.49/1.03      inference(cnf_transformation,[],[f80]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_393,plain,
% 2.49/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.49/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_394,plain,
% 2.49/1.03      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.49/1.03      inference(unflattening,[status(thm)],[c_393]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_695,plain,
% 2.49/1.03      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_394]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_32,negated_conjecture,
% 2.49/1.03      ( l1_struct_0(sK1) ),
% 2.49/1.03      inference(cnf_transformation,[],[f82]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_388,plain,
% 2.49/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.49/1.03      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_389,plain,
% 2.49/1.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.49/1.03      inference(unflattening,[status(thm)],[c_388]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_696,plain,
% 2.49/1.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_389]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1254,plain,
% 2.49/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.49/1.03      inference(light_normalisation,[status(thm)],[c_1228,c_695,c_696]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_15,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.49/1.03      | v1_partfun1(X0,X1)
% 2.49/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/1.03      | v1_xboole_0(X2)
% 2.49/1.03      | ~ v1_funct_1(X0) ),
% 2.49/1.03      inference(cnf_transformation,[],[f70]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_24,plain,
% 2.49/1.03      ( v2_struct_0(X0)
% 2.49/1.03      | ~ l1_struct_0(X0)
% 2.49/1.03      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.49/1.03      inference(cnf_transformation,[],[f78]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_33,negated_conjecture,
% 2.49/1.03      ( ~ v2_struct_0(sK1) ),
% 2.49/1.03      inference(cnf_transformation,[],[f81]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_375,plain,
% 2.49/1.03      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.49/1.03      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_376,plain,
% 2.49/1.03      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.49/1.03      inference(unflattening,[status(thm)],[c_375]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_47,plain,
% 2.49/1.03      ( v2_struct_0(sK1)
% 2.49/1.03      | ~ l1_struct_0(sK1)
% 2.49/1.03      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.49/1.03      inference(instantiation,[status(thm)],[c_24]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_378,plain,
% 2.49/1.03      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.49/1.03      inference(global_propositional_subsumption,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_376,c_33,c_32,c_47]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_400,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.49/1.03      | v1_partfun1(X0,X1)
% 2.49/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | u1_struct_0(sK1) != X2 ),
% 2.49/1.03      inference(resolution_lifted,[status(thm)],[c_15,c_378]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_401,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.49/1.03      | v1_partfun1(X0,X1)
% 2.49/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.49/1.03      | ~ v1_funct_1(X0) ),
% 2.49/1.03      inference(unflattening,[status(thm)],[c_400]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_18,plain,
% 2.49/1.03      ( ~ v1_partfun1(X0,X1)
% 2.49/1.03      | ~ v4_relat_1(X0,X1)
% 2.49/1.03      | ~ v1_relat_1(X0)
% 2.49/1.03      | k1_relat_1(X0) = X1 ),
% 2.49/1.03      inference(cnf_transformation,[],[f71]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_497,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.49/1.03      | ~ v4_relat_1(X0,X1)
% 2.49/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | ~ v1_relat_1(X0)
% 2.49/1.03      | k1_relat_1(X0) = X1 ),
% 2.49/1.03      inference(resolution,[status(thm)],[c_401,c_18]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_13,plain,
% 2.49/1.03      ( v4_relat_1(X0,X1)
% 2.49/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.49/1.03      inference(cnf_transformation,[],[f67]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_513,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.49/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | ~ v1_relat_1(X0)
% 2.49/1.03      | k1_relat_1(X0) = X1 ),
% 2.49/1.03      inference(forward_subsumption_resolution,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_497,c_13]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_693,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0_53,X0_54,u1_struct_0(sK1))
% 2.49/1.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,u1_struct_0(sK1))))
% 2.49/1.03      | ~ v1_funct_1(X0_53)
% 2.49/1.03      | ~ v1_relat_1(X0_53)
% 2.49/1.03      | k1_relat_1(X0_53) = X0_54 ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_513]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1233,plain,
% 2.49/1.03      ( k1_relat_1(X0_53) = X0_54
% 2.49/1.03      | v1_funct_2(X0_53,X0_54,u1_struct_0(sK1)) != iProver_top
% 2.49/1.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,u1_struct_0(sK1)))) != iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_relat_1(X0_53) != iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_693]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1320,plain,
% 2.49/1.03      ( k1_relat_1(X0_53) = X0_54
% 2.49/1.03      | v1_funct_2(X0_53,X0_54,k2_struct_0(sK1)) != iProver_top
% 2.49/1.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,k2_struct_0(sK1)))) != iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_relat_1(X0_53) != iProver_top ),
% 2.49/1.03      inference(light_normalisation,[status(thm)],[c_1233,c_696]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1755,plain,
% 2.49/1.03      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.49/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.49/1.03      inference(superposition,[status(thm)],[c_1254,c_1320]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_31,negated_conjecture,
% 2.49/1.03      ( v1_funct_1(sK2) ),
% 2.49/1.03      inference(cnf_transformation,[],[f83]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_38,plain,
% 2.49/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_40,plain,
% 2.49/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_30,negated_conjecture,
% 2.49/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.49/1.03      inference(cnf_transformation,[],[f84]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_698,negated_conjecture,
% 2.49/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_30]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1229,plain,
% 2.49/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1248,plain,
% 2.49/1.03      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.49/1.03      inference(light_normalisation,[status(thm)],[c_1229,c_695,c_696]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_0,plain,
% 2.49/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.49/1.03      | ~ v1_relat_1(X1)
% 2.49/1.03      | v1_relat_1(X0) ),
% 2.49/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_719,plain,
% 2.49/1.03      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 2.49/1.03      | ~ v1_relat_1(X1_53)
% 2.49/1.03      | v1_relat_1(X0_53) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1509,plain,
% 2.49/1.03      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.49/1.03      | v1_relat_1(X0_53)
% 2.49/1.03      | ~ v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 2.49/1.03      inference(instantiation,[status(thm)],[c_719]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1704,plain,
% 2.49/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.49/1.03      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.49/1.03      | v1_relat_1(sK2) ),
% 2.49/1.03      inference(instantiation,[status(thm)],[c_1509]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1705,plain,
% 2.49/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.49/1.03      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.49/1.03      | v1_relat_1(sK2) = iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_1704]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1,plain,
% 2.49/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.49/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_718,plain,
% 2.49/1.03      ( v1_relat_1(k2_zfmisc_1(X0_54,X1_54)) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1742,plain,
% 2.49/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.49/1.03      inference(instantiation,[status(thm)],[c_718]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1743,plain,
% 2.49/1.03      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_1742]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1810,plain,
% 2.49/1.03      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.49/1.03      inference(global_propositional_subsumption,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_1755,c_38,c_40,c_1248,c_1705,c_1743]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1813,plain,
% 2.49/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 2.49/1.03      inference(demodulation,[status(thm)],[c_1810,c_1254]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_14,plain,
% 2.49/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/1.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.49/1.03      inference(cnf_transformation,[],[f68]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_706,plain,
% 2.49/1.03      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.49/1.03      | k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_14]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1222,plain,
% 2.49/1.03      ( k2_relset_1(X0_54,X1_54,X0_53) = k2_relat_1(X0_53)
% 2.49/1.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_706]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2067,plain,
% 2.49/1.03      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.49/1.03      inference(superposition,[status(thm)],[c_1813,c_1222]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_28,negated_conjecture,
% 2.49/1.03      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.49/1.03      inference(cnf_transformation,[],[f86]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_700,negated_conjecture,
% 2.49/1.03      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_28]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1251,plain,
% 2.49/1.03      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.49/1.03      inference(light_normalisation,[status(thm)],[c_700,c_695,c_696]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1815,plain,
% 2.49/1.03      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.49/1.03      inference(demodulation,[status(thm)],[c_1810,c_1251]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2229,plain,
% 2.49/1.03      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.49/1.03      inference(demodulation,[status(thm)],[c_2067,c_1815]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2264,plain,
% 2.49/1.03      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.49/1.03      inference(demodulation,[status(thm)],[c_2229,c_2067]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_20,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.49/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/1.03      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.49/1.03      | ~ v2_funct_1(X0)
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.49/1.03      inference(cnf_transformation,[],[f76]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_705,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.49/1.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.49/1.03      | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54)))
% 2.49/1.03      | ~ v2_funct_1(X0_53)
% 2.49/1.03      | ~ v1_funct_1(X0_53)
% 2.49/1.03      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_20]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1223,plain,
% 2.49/1.03      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.49/1.03      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.49/1.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.49/1.03      | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_54,X0_54))) = iProver_top
% 2.49/1.03      | v2_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_3832,plain,
% 2.49/1.03      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.49/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.49/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.49/1.03      | v2_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top ),
% 2.49/1.03      inference(superposition,[status(thm)],[c_2264,c_1223]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_27,negated_conjecture,
% 2.49/1.03      ( v2_funct_1(sK2) ),
% 2.49/1.03      inference(cnf_transformation,[],[f87]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_41,plain,
% 2.49/1.03      ( v2_funct_1(sK2) = iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2266,plain,
% 2.49/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.49/1.03      inference(demodulation,[status(thm)],[c_2229,c_1813]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1814,plain,
% 2.49/1.03      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
% 2.49/1.03      inference(demodulation,[status(thm)],[c_1810,c_1248]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2267,plain,
% 2.49/1.03      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.49/1.03      inference(demodulation,[status(thm)],[c_2229,c_1814]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_4812,plain,
% 2.49/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.49/1.03      inference(global_propositional_subsumption,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_3832,c_38,c_41,c_2266,c_2267]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_4818,plain,
% 2.49/1.03      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.49/1.03      inference(superposition,[status(thm)],[c_4812,c_1222]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_701,negated_conjecture,
% 2.49/1.03      ( v2_funct_1(sK2) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_27]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1227,plain,
% 2.49/1.03      ( v2_funct_1(sK2) = iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_8,plain,
% 2.49/1.03      ( ~ v2_funct_1(X0)
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | ~ v1_relat_1(X0)
% 2.49/1.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.49/1.03      inference(cnf_transformation,[],[f63]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_711,plain,
% 2.49/1.03      ( ~ v2_funct_1(X0_53)
% 2.49/1.03      | ~ v1_funct_1(X0_53)
% 2.49/1.03      | ~ v1_relat_1(X0_53)
% 2.49/1.03      | k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1217,plain,
% 2.49/1.03      ( k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53)
% 2.49/1.03      | v2_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_relat_1(X0_53) != iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_711]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2073,plain,
% 2.49/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.49/1.03      inference(superposition,[status(thm)],[c_1227,c_1217]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_777,plain,
% 2.49/1.03      ( ~ v2_funct_1(sK2)
% 2.49/1.03      | ~ v1_funct_1(sK2)
% 2.49/1.03      | ~ v1_relat_1(sK2)
% 2.49/1.03      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.49/1.03      inference(instantiation,[status(thm)],[c_711]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2200,plain,
% 2.49/1.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.49/1.03      inference(global_propositional_subsumption,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_2073,c_31,c_29,c_27,c_777,c_1704,c_1742]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_4825,plain,
% 2.49/1.03      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.49/1.03      inference(light_normalisation,[status(thm)],[c_4818,c_2200]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_25,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.49/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/1.03      | ~ v2_funct_1(X0)
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.49/1.03      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.49/1.03      inference(cnf_transformation,[],[f79]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_702,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.49/1.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.49/1.03      | ~ v2_funct_1(X0_53)
% 2.49/1.03      | ~ v1_funct_1(X0_53)
% 2.49/1.03      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.49/1.03      | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_25]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1226,plain,
% 2.49/1.03      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.49/1.03      | k2_tops_2(X0_54,X1_54,X0_53) = k2_funct_1(X0_53)
% 2.49/1.03      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.49/1.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.49/1.03      | v2_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_4833,plain,
% 2.49/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.49/1.03      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.49/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.49/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.49/1.03      inference(superposition,[status(thm)],[c_4825,c_1226]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_11,plain,
% 2.49/1.03      ( ~ v2_funct_1(X0)
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | ~ v1_relat_1(X0)
% 2.49/1.03      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 2.49/1.03      inference(cnf_transformation,[],[f64]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_708,plain,
% 2.49/1.03      ( ~ v2_funct_1(X0_53)
% 2.49/1.03      | ~ v1_funct_1(X0_53)
% 2.49/1.03      | ~ v1_relat_1(X0_53)
% 2.49/1.03      | k5_relat_1(X0_53,k2_funct_1(X0_53)) = k6_relat_1(k1_relat_1(X0_53)) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1220,plain,
% 2.49/1.03      ( k5_relat_1(X0_53,k2_funct_1(X0_53)) = k6_relat_1(k1_relat_1(X0_53))
% 2.49/1.03      | v2_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_relat_1(X0_53) != iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_708]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2546,plain,
% 2.49/1.03      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.49/1.03      inference(superposition,[status(thm)],[c_1227,c_1220]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_786,plain,
% 2.49/1.03      ( ~ v2_funct_1(sK2)
% 2.49/1.03      | ~ v1_funct_1(sK2)
% 2.49/1.03      | ~ v1_relat_1(sK2)
% 2.49/1.03      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 2.49/1.03      inference(instantiation,[status(thm)],[c_708]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2804,plain,
% 2.49/1.03      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 2.49/1.03      inference(global_propositional_subsumption,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_2546,c_31,c_29,c_27,c_786,c_1704,c_1742]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_12,plain,
% 2.49/1.03      ( ~ v2_funct_1(X0)
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | ~ v1_funct_1(X1)
% 2.49/1.03      | ~ v1_relat_1(X0)
% 2.49/1.03      | ~ v1_relat_1(X1)
% 2.49/1.03      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
% 2.49/1.03      | k1_relat_1(X0) != k2_relat_1(X1)
% 2.49/1.03      | k2_funct_1(X0) = X1 ),
% 2.49/1.03      inference(cnf_transformation,[],[f66]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_707,plain,
% 2.49/1.03      ( ~ v2_funct_1(X0_53)
% 2.49/1.03      | ~ v1_funct_1(X0_53)
% 2.49/1.03      | ~ v1_funct_1(X1_53)
% 2.49/1.03      | ~ v1_relat_1(X0_53)
% 2.49/1.03      | ~ v1_relat_1(X1_53)
% 2.49/1.03      | k1_relat_1(X0_53) != k2_relat_1(X1_53)
% 2.49/1.03      | k5_relat_1(X1_53,X0_53) != k6_relat_1(k2_relat_1(X0_53))
% 2.49/1.03      | k2_funct_1(X0_53) = X1_53 ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1221,plain,
% 2.49/1.03      ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
% 2.49/1.03      | k5_relat_1(X1_53,X0_53) != k6_relat_1(k2_relat_1(X0_53))
% 2.49/1.03      | k2_funct_1(X0_53) = X1_53
% 2.49/1.03      | v2_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_funct_1(X1_53) != iProver_top
% 2.49/1.03      | v1_relat_1(X0_53) != iProver_top
% 2.49/1.03      | v1_relat_1(X1_53) != iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_707]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_3293,plain,
% 2.49/1.03      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.49/1.03      | k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
% 2.49/1.03      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.49/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.49/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.49/1.03      inference(superposition,[status(thm)],[c_2804,c_1221]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_9,plain,
% 2.49/1.03      ( ~ v2_funct_1(X0)
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | ~ v1_relat_1(X0)
% 2.49/1.03      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.49/1.03      inference(cnf_transformation,[],[f62]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_710,plain,
% 2.49/1.03      ( ~ v2_funct_1(X0_53)
% 2.49/1.03      | ~ v1_funct_1(X0_53)
% 2.49/1.03      | ~ v1_relat_1(X0_53)
% 2.49/1.03      | k1_relat_1(k2_funct_1(X0_53)) = k2_relat_1(X0_53) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_9]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1218,plain,
% 2.49/1.03      ( k1_relat_1(k2_funct_1(X0_53)) = k2_relat_1(X0_53)
% 2.49/1.03      | v2_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_relat_1(X0_53) != iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_710]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2123,plain,
% 2.49/1.03      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.49/1.03      inference(superposition,[status(thm)],[c_1227,c_1218]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_780,plain,
% 2.49/1.03      ( ~ v2_funct_1(sK2)
% 2.49/1.03      | ~ v1_funct_1(sK2)
% 2.49/1.03      | ~ v1_relat_1(sK2)
% 2.49/1.03      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.49/1.03      inference(instantiation,[status(thm)],[c_710]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2204,plain,
% 2.49/1.03      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.49/1.03      inference(global_propositional_subsumption,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_2123,c_31,c_29,c_27,c_780,c_1704,c_1742]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_3302,plain,
% 2.49/1.03      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 2.49/1.03      | k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
% 2.49/1.03      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.49/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.49/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.49/1.03      inference(light_normalisation,[status(thm)],[c_3293,c_2200,c_2204]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_3303,plain,
% 2.49/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.49/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.49/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.49/1.03      inference(equality_resolution_simp,[status(thm)],[c_3302]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2,plain,
% 2.49/1.03      ( ~ v1_funct_1(X0)
% 2.49/1.03      | v1_funct_1(k2_funct_1(X0))
% 2.49/1.03      | ~ v1_relat_1(X0) ),
% 2.49/1.03      inference(cnf_transformation,[],[f57]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_717,plain,
% 2.49/1.03      ( ~ v1_funct_1(X0_53)
% 2.49/1.03      | v1_funct_1(k2_funct_1(X0_53))
% 2.49/1.03      | ~ v1_relat_1(X0_53) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_2]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_762,plain,
% 2.49/1.03      ( v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_funct_1(X0_53)) = iProver_top
% 2.49/1.03      | v1_relat_1(X0_53) != iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_764,plain,
% 2.49/1.03      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.49/1.03      inference(instantiation,[status(thm)],[c_762]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_3,plain,
% 2.49/1.03      ( ~ v1_funct_1(X0)
% 2.49/1.03      | ~ v1_relat_1(X0)
% 2.49/1.03      | v1_relat_1(k2_funct_1(X0)) ),
% 2.49/1.03      inference(cnf_transformation,[],[f56]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_716,plain,
% 2.49/1.03      ( ~ v1_funct_1(X0_53)
% 2.49/1.03      | ~ v1_relat_1(X0_53)
% 2.49/1.03      | v1_relat_1(k2_funct_1(X0_53)) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_765,plain,
% 2.49/1.03      ( v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_relat_1(X0_53) != iProver_top
% 2.49/1.03      | v1_relat_1(k2_funct_1(X0_53)) = iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_767,plain,
% 2.49/1.03      ( v1_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.49/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.49/1.03      inference(instantiation,[status(thm)],[c_765]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_6,plain,
% 2.49/1.03      ( v2_funct_1(X0)
% 2.49/1.03      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | ~ v1_funct_1(X1)
% 2.49/1.03      | ~ v1_relat_1(X0)
% 2.49/1.03      | ~ v1_relat_1(X1)
% 2.49/1.03      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 2.49/1.03      inference(cnf_transformation,[],[f61]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_713,plain,
% 2.49/1.03      ( v2_funct_1(X0_53)
% 2.49/1.03      | ~ v2_funct_1(k5_relat_1(X1_53,X0_53))
% 2.49/1.03      | ~ v1_funct_1(X0_53)
% 2.49/1.03      | ~ v1_funct_1(X1_53)
% 2.49/1.03      | ~ v1_relat_1(X0_53)
% 2.49/1.03      | ~ v1_relat_1(X1_53)
% 2.49/1.03      | k1_relat_1(X0_53) != k2_relat_1(X1_53) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_6]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1215,plain,
% 2.49/1.03      ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
% 2.49/1.03      | v2_funct_1(X0_53) = iProver_top
% 2.49/1.03      | v2_funct_1(k5_relat_1(X1_53,X0_53)) != iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_funct_1(X1_53) != iProver_top
% 2.49/1.03      | v1_relat_1(X0_53) != iProver_top
% 2.49/1.03      | v1_relat_1(X1_53) != iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2507,plain,
% 2.49/1.03      ( k2_relat_1(X0_53) != k2_relat_1(sK2)
% 2.49/1.03      | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
% 2.49/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.49/1.03      | v1_relat_1(X0_53) != iProver_top
% 2.49/1.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.49/1.03      inference(superposition,[status(thm)],[c_2204,c_1215]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2976,plain,
% 2.49/1.03      ( v1_relat_1(X0_53) != iProver_top
% 2.49/1.03      | k2_relat_1(X0_53) != k2_relat_1(sK2)
% 2.49/1.03      | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
% 2.49/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top ),
% 2.49/1.03      inference(global_propositional_subsumption,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_2507,c_38,c_40,c_764,c_767,c_1705,c_1743]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2977,plain,
% 2.49/1.03      ( k2_relat_1(X0_53) != k2_relat_1(sK2)
% 2.49/1.03      | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
% 2.49/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_relat_1(X0_53) != iProver_top ),
% 2.49/1.03      inference(renaming,[status(thm)],[c_2976]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2988,plain,
% 2.49/1.03      ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
% 2.49/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.49/1.03      inference(equality_resolution,[status(thm)],[c_2977]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2993,plain,
% 2.49/1.03      ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
% 2.49/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.49/1.03      inference(light_normalisation,[status(thm)],[c_2988,c_2804]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_3071,plain,
% 2.49/1.03      ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
% 2.49/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.49/1.03      inference(global_propositional_subsumption,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_2993,c_38,c_40,c_1705,c_1743]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_4,plain,
% 2.49/1.03      ( v2_funct_1(k6_relat_1(X0)) ),
% 2.49/1.03      inference(cnf_transformation,[],[f59]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_715,plain,
% 2.49/1.03      ( v2_funct_1(k6_relat_1(X0_54)) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1213,plain,
% 2.49/1.03      ( v2_funct_1(k6_relat_1(X0_54)) = iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_715]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_3077,plain,
% 2.49/1.03      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.49/1.03      inference(forward_subsumption_resolution,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_3071,c_1213]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_4564,plain,
% 2.49/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.49/1.03      inference(global_propositional_subsumption,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_3303,c_38,c_40,c_764,c_767,c_1705,c_1743,c_3077]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_4846,plain,
% 2.49/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.49/1.03      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.49/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.49/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.49/1.03      inference(light_normalisation,[status(thm)],[c_4833,c_4564]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_21,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.49/1.03      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.49/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/1.03      | ~ v2_funct_1(X0)
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.49/1.03      inference(cnf_transformation,[],[f75]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_704,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0_53,X0_54,X1_54)
% 2.49/1.03      | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54)
% 2.49/1.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54)))
% 2.49/1.03      | ~ v2_funct_1(X0_53)
% 2.49/1.03      | ~ v1_funct_1(X0_53)
% 2.49/1.03      | k2_relset_1(X0_54,X1_54,X0_53) != X1_54 ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_21]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1224,plain,
% 2.49/1.03      ( k2_relset_1(X0_54,X1_54,X0_53) != X1_54
% 2.49/1.03      | v1_funct_2(X0_53,X0_54,X1_54) != iProver_top
% 2.49/1.03      | v1_funct_2(k2_funct_1(X0_53),X1_54,X0_54) = iProver_top
% 2.49/1.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_54,X1_54))) != iProver_top
% 2.49/1.03      | v2_funct_1(X0_53) != iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_704]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_3834,plain,
% 2.49/1.03      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.49/1.03      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.49/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.49/1.03      | v2_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top ),
% 2.49/1.03      inference(superposition,[status(thm)],[c_2264,c_1224]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_4907,plain,
% 2.49/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.49/1.03      inference(global_propositional_subsumption,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_4846,c_38,c_40,c_41,c_764,c_1705,c_1743,c_2266,c_2267,
% 2.49/1.03                 c_3077,c_3832,c_3834]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_19,plain,
% 2.49/1.03      ( r2_funct_2(X0,X1,X2,X2)
% 2.49/1.03      | ~ v1_funct_2(X2,X0,X1)
% 2.49/1.03      | ~ v1_funct_2(X3,X0,X1)
% 2.49/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.49/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.49/1.03      | ~ v1_funct_1(X2)
% 2.49/1.03      | ~ v1_funct_1(X3) ),
% 2.49/1.03      inference(cnf_transformation,[],[f73]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_26,negated_conjecture,
% 2.49/1.03      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.49/1.03      inference(cnf_transformation,[],[f88]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_423,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.49/1.03      | ~ v1_funct_2(X3,X1,X2)
% 2.49/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/1.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | ~ v1_funct_1(X3)
% 2.49/1.03      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.49/1.03      | u1_struct_0(sK1) != X2
% 2.49/1.03      | u1_struct_0(sK0) != X1
% 2.49/1.03      | sK2 != X0 ),
% 2.49/1.03      inference(resolution_lifted,[status(thm)],[c_19,c_26]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_424,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.49/1.03      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.49/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.49/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.49/1.03      | ~ v1_funct_1(X0)
% 2.49/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.49/1.03      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.49/1.03      inference(unflattening,[status(thm)],[c_423]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_694,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.49/1.03      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.49/1.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.49/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.49/1.03      | ~ v1_funct_1(X0_53)
% 2.49/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.49/1.03      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.49/1.03      inference(subtyping,[status(esa)],[c_424]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_721,plain,
% 2.49/1.03      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.49/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.49/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.49/1.03      | sP0_iProver_split
% 2.49/1.03      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.49/1.03      inference(splitting,
% 2.49/1.03                [splitting(split),new_symbols(definition,[])],
% 2.49/1.03                [c_694]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1231,plain,
% 2.49/1.03      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.49/1.03      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.49/1.03      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.49/1.03      | sP0_iProver_split = iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1423,plain,
% 2.49/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.49/1.03      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.49/1.03      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.49/1.03      | sP0_iProver_split = iProver_top ),
% 2.49/1.03      inference(light_normalisation,[status(thm)],[c_1231,c_695,c_696]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_720,plain,
% 2.49/1.03      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.49/1.03      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.49/1.03      | ~ v1_funct_1(X0_53)
% 2.49/1.03      | ~ sP0_iProver_split ),
% 2.49/1.03      inference(splitting,
% 2.49/1.03                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.49/1.03                [c_694]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1232,plain,
% 2.49/1.03      ( v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.49/1.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | sP0_iProver_split != iProver_top ),
% 2.49/1.03      inference(predicate_to_equality,[status(thm)],[c_720]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1311,plain,
% 2.49/1.03      ( v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.49/1.03      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.49/1.03      | v1_funct_1(X0_53) != iProver_top
% 2.49/1.03      | sP0_iProver_split != iProver_top ),
% 2.49/1.03      inference(light_normalisation,[status(thm)],[c_1232,c_695,c_696]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_1429,plain,
% 2.49/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.49/1.03      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.49/1.03      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.49/1.03      inference(forward_subsumption_resolution,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_1423,c_1311]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2002,plain,
% 2.49/1.03      ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
% 2.49/1.03      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
% 2.49/1.03      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.49/1.03      inference(light_normalisation,[status(thm)],[c_1429,c_1810]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_2265,plain,
% 2.49/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 2.49/1.03      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.49/1.03      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.49/1.03      inference(demodulation,[status(thm)],[c_2229,c_2002]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_3833,plain,
% 2.49/1.03      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.49/1.03      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.49/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.49/1.03      | v2_funct_1(sK2) != iProver_top
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top ),
% 2.49/1.03      inference(superposition,[status(thm)],[c_2264,c_1226]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_4370,plain,
% 2.49/1.03      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.49/1.03      inference(global_propositional_subsumption,
% 2.49/1.03                [status(thm)],
% 2.49/1.03                [c_3833,c_38,c_41,c_2266,c_2267]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_4702,plain,
% 2.49/1.03      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.49/1.03      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.49/1.03      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.49/1.03      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.49/1.03      inference(light_normalisation,[status(thm)],[c_2265,c_4370]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_4910,plain,
% 2.49/1.03      ( sK2 != sK2
% 2.49/1.03      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.49/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.49/1.03      | v1_funct_1(sK2) != iProver_top ),
% 2.49/1.03      inference(demodulation,[status(thm)],[c_4907,c_4702]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_723,plain,( X0_53 = X0_53 ),theory(equality) ).
% 2.49/1.03  
% 2.49/1.03  cnf(c_755,plain,
% 2.49/1.03      ( sK2 = sK2 ),
% 2.49/1.03      inference(instantiation,[status(thm)],[c_723]) ).
% 2.49/1.03  
% 2.49/1.03  cnf(contradiction,plain,
% 2.49/1.03      ( $false ),
% 2.49/1.03      inference(minisat,[status(thm)],[c_4910,c_2267,c_2266,c_755,c_38]) ).
% 2.49/1.03  
% 2.49/1.03  
% 2.49/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.49/1.03  
% 2.49/1.03  ------                               Statistics
% 2.49/1.03  
% 2.49/1.03  ------ General
% 2.49/1.03  
% 2.49/1.03  abstr_ref_over_cycles:                  0
% 2.49/1.03  abstr_ref_under_cycles:                 0
% 2.49/1.03  gc_basic_clause_elim:                   0
% 2.49/1.03  forced_gc_time:                         0
% 2.49/1.03  parsing_time:                           0.008
% 2.49/1.03  unif_index_cands_time:                  0.
% 2.49/1.03  unif_index_add_time:                    0.
% 2.49/1.03  orderings_time:                         0.
% 2.49/1.03  out_proof_time:                         0.014
% 2.49/1.03  total_time:                             0.172
% 2.49/1.03  num_of_symbols:                         61
% 2.49/1.03  num_of_terms:                           4829
% 2.49/1.03  
% 2.49/1.03  ------ Preprocessing
% 2.49/1.03  
% 2.49/1.03  num_of_splits:                          1
% 2.49/1.03  num_of_split_atoms:                     1
% 2.49/1.03  num_of_reused_defs:                     0
% 2.49/1.03  num_eq_ax_congr_red:                    7
% 2.49/1.03  num_of_sem_filtered_clauses:            2
% 2.49/1.03  num_of_subtypes:                        4
% 2.49/1.03  monotx_restored_types:                  1
% 2.49/1.03  sat_num_of_epr_types:                   0
% 2.49/1.03  sat_num_of_non_cyclic_types:            0
% 2.49/1.03  sat_guarded_non_collapsed_types:        1
% 2.49/1.03  num_pure_diseq_elim:                    0
% 2.49/1.03  simp_replaced_by:                       0
% 2.49/1.03  res_preprocessed:                       153
% 2.49/1.03  prep_upred:                             0
% 2.49/1.03  prep_unflattend:                        11
% 2.49/1.03  smt_new_axioms:                         0
% 2.49/1.03  pred_elim_cands:                        5
% 2.49/1.03  pred_elim:                              6
% 2.49/1.03  pred_elim_cl:                           7
% 2.49/1.03  pred_elim_cycles:                       9
% 2.49/1.03  merged_defs:                            0
% 2.49/1.03  merged_defs_ncl:                        0
% 2.49/1.03  bin_hyper_res:                          0
% 2.49/1.03  prep_cycles:                            4
% 2.49/1.03  pred_elim_time:                         0.003
% 2.49/1.03  splitting_time:                         0.
% 2.49/1.03  sem_filter_time:                        0.
% 2.49/1.03  monotx_time:                            0.
% 2.49/1.03  subtype_inf_time:                       0.001
% 2.49/1.03  
% 2.49/1.03  ------ Problem properties
% 2.49/1.03  
% 2.49/1.03  clauses:                                28
% 2.49/1.03  conjectures:                            5
% 2.49/1.03  epr:                                    2
% 2.49/1.03  horn:                                   28
% 2.49/1.03  ground:                                 8
% 2.49/1.03  unary:                                  10
% 2.49/1.03  binary:                                 1
% 2.49/1.03  lits:                                   97
% 2.49/1.03  lits_eq:                                20
% 2.49/1.03  fd_pure:                                0
% 2.49/1.03  fd_pseudo:                              0
% 2.49/1.03  fd_cond:                                0
% 2.49/1.03  fd_pseudo_cond:                         2
% 2.49/1.03  ac_symbols:                             0
% 2.49/1.03  
% 2.49/1.03  ------ Propositional Solver
% 2.49/1.03  
% 2.49/1.03  prop_solver_calls:                      29
% 2.49/1.03  prop_fast_solver_calls:                 1414
% 2.49/1.03  smt_solver_calls:                       0
% 2.49/1.03  smt_fast_solver_calls:                  0
% 2.49/1.03  prop_num_of_clauses:                    1805
% 2.49/1.03  prop_preprocess_simplified:             5925
% 2.49/1.03  prop_fo_subsumed:                       107
% 2.49/1.03  prop_solver_time:                       0.
% 2.49/1.03  smt_solver_time:                        0.
% 2.49/1.03  smt_fast_solver_time:                   0.
% 2.49/1.03  prop_fast_solver_time:                  0.
% 2.49/1.03  prop_unsat_core_time:                   0.
% 2.49/1.03  
% 2.49/1.03  ------ QBF
% 2.49/1.03  
% 2.49/1.03  qbf_q_res:                              0
% 2.49/1.03  qbf_num_tautologies:                    0
% 2.49/1.03  qbf_prep_cycles:                        0
% 2.49/1.03  
% 2.49/1.03  ------ BMC1
% 2.49/1.03  
% 2.49/1.03  bmc1_current_bound:                     -1
% 2.49/1.03  bmc1_last_solved_bound:                 -1
% 2.49/1.03  bmc1_unsat_core_size:                   -1
% 2.49/1.03  bmc1_unsat_core_parents_size:           -1
% 2.49/1.03  bmc1_merge_next_fun:                    0
% 2.49/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.49/1.03  
% 2.49/1.03  ------ Instantiation
% 2.49/1.03  
% 2.49/1.03  inst_num_of_clauses:                    621
% 2.49/1.03  inst_num_in_passive:                    39
% 2.49/1.03  inst_num_in_active:                     348
% 2.49/1.03  inst_num_in_unprocessed:                234
% 2.49/1.03  inst_num_of_loops:                      380
% 2.49/1.03  inst_num_of_learning_restarts:          0
% 2.49/1.03  inst_num_moves_active_passive:          28
% 2.49/1.03  inst_lit_activity:                      0
% 2.49/1.03  inst_lit_activity_moves:                0
% 2.49/1.03  inst_num_tautologies:                   0
% 2.49/1.03  inst_num_prop_implied:                  0
% 2.49/1.03  inst_num_existing_simplified:           0
% 2.49/1.03  inst_num_eq_res_simplified:             0
% 2.49/1.03  inst_num_child_elim:                    0
% 2.49/1.03  inst_num_of_dismatching_blockings:      162
% 2.49/1.03  inst_num_of_non_proper_insts:           645
% 2.49/1.03  inst_num_of_duplicates:                 0
% 2.49/1.03  inst_inst_num_from_inst_to_res:         0
% 2.49/1.03  inst_dismatching_checking_time:         0.
% 2.49/1.03  
% 2.49/1.03  ------ Resolution
% 2.49/1.03  
% 2.49/1.03  res_num_of_clauses:                     0
% 2.49/1.03  res_num_in_passive:                     0
% 2.49/1.03  res_num_in_active:                      0
% 2.49/1.03  res_num_of_loops:                       157
% 2.49/1.03  res_forward_subset_subsumed:            71
% 2.49/1.03  res_backward_subset_subsumed:           0
% 2.49/1.03  res_forward_subsumed:                   0
% 2.49/1.03  res_backward_subsumed:                  0
% 2.49/1.03  res_forward_subsumption_resolution:     1
% 2.49/1.03  res_backward_subsumption_resolution:    0
% 2.49/1.03  res_clause_to_clause_subsumption:       123
% 2.49/1.03  res_orphan_elimination:                 0
% 2.49/1.03  res_tautology_del:                      70
% 2.49/1.03  res_num_eq_res_simplified:              0
% 2.49/1.03  res_num_sel_changes:                    0
% 2.49/1.03  res_moves_from_active_to_pass:          0
% 2.49/1.03  
% 2.49/1.03  ------ Superposition
% 2.49/1.03  
% 2.49/1.03  sup_time_total:                         0.
% 2.49/1.03  sup_time_generating:                    0.
% 2.49/1.03  sup_time_sim_full:                      0.
% 2.49/1.03  sup_time_sim_immed:                     0.
% 2.49/1.03  
% 2.49/1.03  sup_num_of_clauses:                     57
% 2.49/1.03  sup_num_in_active:                      51
% 2.49/1.03  sup_num_in_passive:                     6
% 2.49/1.03  sup_num_of_loops:                       74
% 2.49/1.03  sup_fw_superposition:                   27
% 2.49/1.03  sup_bw_superposition:                   38
% 2.49/1.03  sup_immediate_simplified:               30
% 2.49/1.03  sup_given_eliminated:                   0
% 2.49/1.03  comparisons_done:                       0
% 2.49/1.03  comparisons_avoided:                    0
% 2.49/1.03  
% 2.49/1.03  ------ Simplifications
% 2.49/1.03  
% 2.49/1.03  
% 2.49/1.03  sim_fw_subset_subsumed:                 13
% 2.49/1.03  sim_bw_subset_subsumed:                 3
% 2.49/1.03  sim_fw_subsumed:                        3
% 2.49/1.03  sim_bw_subsumed:                        0
% 2.49/1.03  sim_fw_subsumption_res:                 5
% 2.49/1.03  sim_bw_subsumption_res:                 0
% 2.49/1.03  sim_tautology_del:                      0
% 2.49/1.03  sim_eq_tautology_del:                   10
% 2.49/1.03  sim_eq_res_simp:                        2
% 2.49/1.03  sim_fw_demodulated:                     0
% 2.49/1.03  sim_bw_demodulated:                     21
% 2.49/1.03  sim_light_normalised:                   33
% 2.49/1.03  sim_joinable_taut:                      0
% 2.49/1.03  sim_joinable_simp:                      0
% 2.49/1.03  sim_ac_normalised:                      0
% 2.49/1.03  sim_smt_subsumption:                    0
% 2.49/1.03  
%------------------------------------------------------------------------------
