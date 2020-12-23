%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:32 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :  240 (23397 expanded)
%              Number of clauses        :  154 (7414 expanded)
%              Number of leaves         :   25 (6488 expanded)
%              Depth                    :   33
%              Number of atoms          :  857 (146273 expanded)
%              Number of equality atoms :  339 (23467 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f20,conjecture,(
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

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

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
    inference(ennf_transformation,[],[f21])).

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

fof(f54,plain,(
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

fof(f53,plain,(
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

fof(f52,plain,
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

fof(f55,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f54,f53,f52])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f81,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f84,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f86,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f85,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

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

fof(f51,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f88,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f90,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f91,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f14,axiom,(
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
    inference(ennf_transformation,[],[f14])).

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

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f92,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f60,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(ennf_transformation,[],[f15])).

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

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f29,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f66,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f67,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f42])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f59,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f13,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f13])).

fof(f93,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f62,f74])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_714,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1239,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_714])).

cnf(c_24,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_35,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_402,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_403,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_710,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_403])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_397,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_398,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_397])).

cnf(c_711,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_398])).

cnf(c_1268,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1239,c_710,c_711])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_25,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_384,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_385,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_384])).

cnf(c_48,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_387,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_385,c_34,c_33,c_48])).

cnf(c_413,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_387])).

cnf(c_414,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_17,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_511,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_414,c_17])).

cnf(c_12,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_527,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_511,c_12])).

cnf(c_707,plain,
    ( ~ v1_funct_2(X0_54,X0_55,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k1_relat_1(X0_54) = X0_55 ),
    inference(subtyping,[status(esa)],[c_527])).

cnf(c_1244,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_707])).

cnf(c_1326,plain,
    ( k1_relat_1(X0_54) = X0_55
    | v1_funct_2(X0_54,X0_55,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1244,c_711])).

cnf(c_1825,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1268,c_1326])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_41,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_713,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1240,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_713])).

cnf(c_1262,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1240,c_710,c_711])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_734,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1527,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_relat_1(X0_54)
    | ~ v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(instantiation,[status(thm)],[c_734])).

cnf(c_1710,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1527])).

cnf(c_1711,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1710])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_733,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1758,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_733])).

cnf(c_1759,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1758])).

cnf(c_1879,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1825,c_39,c_41,c_1262,c_1711,c_1759])).

cnf(c_1882,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1879,c_1268])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_723,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1231,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_723])).

cnf(c_2047,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1882,c_1231])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_715,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1265,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_715,c_710,c_711])).

cnf(c_1884,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1879,c_1265])).

cnf(c_2294,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2047,c_1884])).

cnf(c_2296,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2294,c_2047])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_717,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1237,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_717])).

cnf(c_3166,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_1237])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_42,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2298,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2294,c_1882])).

cnf(c_1883,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1879,c_1262])).

cnf(c_2299,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2294,c_1883])).

cnf(c_3804,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3166,c_39,c_42,c_2298,c_2299])).

cnf(c_18,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_27,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_437,plain,
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
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_438,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_437])).

cnf(c_708,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_438])).

cnf(c_736,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_708])).

cnf(c_1242,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_1441,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1242,c_710,c_711])).

cnf(c_735,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_708])).

cnf(c_1243,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_1317,plain,
    ( v1_funct_2(X0_54,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1243,c_710,c_711])).

cnf(c_1447,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1441,c_1317])).

cnf(c_2229,plain,
    ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1447,c_1879])).

cnf(c_2297,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2294,c_2229])).

cnf(c_3807,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3804,c_2297])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_732,plain,
    ( ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_funct_1(X0_54))
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_777,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_funct_1(X0_54)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_732])).

cnf(c_779,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_777])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_721,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1233,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_721])).

cnf(c_3167,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_1233])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_722,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1232,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_3197,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_1232])).

cnf(c_3967,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3197,c_39,c_42,c_2298,c_2299])).

cnf(c_3973,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3967,c_1231])).

cnf(c_716,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1238,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_716])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_726,plain,
    ( ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1228,plain,
    ( k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54)
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_726])).

cnf(c_2114,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_1228])).

cnf(c_792,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_726])).

cnf(c_2201,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2114,c_32,c_30,c_28,c_792,c_1710,c_1758])).

cnf(c_3980,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3973,c_2201])).

cnf(c_4242,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3980,c_1237])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_724,plain,
    ( ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1230,plain,
    ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_724])).

cnf(c_2053,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1238,c_1230])).

cnf(c_798,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_724])).

cnf(c_2195,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2053,c_32,c_30,c_28,c_798,c_1710,c_1758])).

cnf(c_4255,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4242,c_2195])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_719,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k1_xboole_0 = X1_55
    | k5_relat_1(k2_funct_1(X0_54),X0_54) = k6_partfun1(X1_55) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1235,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k1_xboole_0 = X1_55
    | k5_relat_1(k2_funct_1(X0_54),X0_54) = k6_partfun1(X1_55)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_719])).

cnf(c_3274,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2296,c_1235])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_409,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_387])).

cnf(c_709,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_409])).

cnf(c_1257,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_709,c_711])).

cnf(c_2301,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2294,c_1257])).

cnf(c_4153,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3274,c_39,c_42,c_2298,c_2299,c_2301])).

cnf(c_8,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_727,plain,
    ( v2_funct_1(X0_54)
    | ~ v2_funct_1(k5_relat_1(X0_54,X1_54))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | ~ v1_relat_1(X0_54)
    | ~ v1_relat_1(X1_54)
    | k1_relat_1(X1_54) != k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1227,plain,
    ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
    | v2_funct_1(X1_54) = iProver_top
    | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_2604,plain,
    ( k1_relat_1(X0_54) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_54)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2201,c_1227])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_731,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | v1_relat_1(k2_funct_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_780,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k2_funct_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_782,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_780])).

cnf(c_3093,plain,
    ( v1_relat_1(X0_54) != iProver_top
    | k1_relat_1(X0_54) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_54)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2604,c_39,c_41,c_779,c_782,c_1711,c_1759])).

cnf(c_3094,plain,
    ( k1_relat_1(X0_54) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_54)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3093])).

cnf(c_3105,plain,
    ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3094])).

cnf(c_751,plain,
    ( k1_relat_1(X0_54) = k1_relat_1(X1_54)
    | X0_54 != X1_54 ),
    theory(equality)).

cnf(c_764,plain,
    ( k1_relat_1(sK2) = k1_relat_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_738,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_770,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_738])).

cnf(c_3096,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3094])).

cnf(c_3736,plain,
    ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3105,c_39,c_41,c_764,c_770,c_1711,c_1759,c_3096])).

cnf(c_4156,plain,
    ( v2_funct_1(k6_partfun1(k2_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4153,c_3736])).

cnf(c_5,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_730,plain,
    ( v2_funct_1(k6_partfun1(X0_55)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1224,plain,
    ( v2_funct_1(k6_partfun1(X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_730])).

cnf(c_4398,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4156,c_1224])).

cnf(c_4482,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3807,c_39,c_41,c_42,c_779,c_1711,c_1759,c_2298,c_2299,c_3167,c_3197,c_4255,c_4398])).

cnf(c_4283,plain,
    ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4255,c_39,c_41,c_42,c_779,c_1711,c_1759,c_2298,c_2299,c_3167,c_3197])).

cnf(c_4284,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_4283])).

cnf(c_4403,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_4398,c_4284])).

cnf(c_4486,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4482,c_4403])).

cnf(c_712,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_32])).

cnf(c_1241,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_712])).

cnf(c_4490,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4486,c_1241,c_2298,c_2299])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.31  % Computer   : n013.cluster.edu
% 0.13/0.31  % Model      : x86_64 x86_64
% 0.13/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.31  % Memory     : 8042.1875MB
% 0.13/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.31  % CPULimit   : 60
% 0.13/0.31  % WCLimit    : 600
% 0.13/0.31  % DateTime   : Tue Dec  1 17:27:24 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.32  % Running in FOF mode
% 2.50/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/0.96  
% 2.50/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.50/0.96  
% 2.50/0.96  ------  iProver source info
% 2.50/0.96  
% 2.50/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.50/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.50/0.96  git: non_committed_changes: false
% 2.50/0.96  git: last_make_outside_of_git: false
% 2.50/0.96  
% 2.50/0.96  ------ 
% 2.50/0.96  
% 2.50/0.96  ------ Input Options
% 2.50/0.96  
% 2.50/0.96  --out_options                           all
% 2.50/0.96  --tptp_safe_out                         true
% 2.50/0.96  --problem_path                          ""
% 2.50/0.96  --include_path                          ""
% 2.50/0.96  --clausifier                            res/vclausify_rel
% 2.50/0.96  --clausifier_options                    --mode clausify
% 2.50/0.96  --stdin                                 false
% 2.50/0.96  --stats_out                             all
% 2.50/0.96  
% 2.50/0.96  ------ General Options
% 2.50/0.96  
% 2.50/0.96  --fof                                   false
% 2.50/0.96  --time_out_real                         305.
% 2.50/0.96  --time_out_virtual                      -1.
% 2.50/0.96  --symbol_type_check                     false
% 2.50/0.96  --clausify_out                          false
% 2.50/0.96  --sig_cnt_out                           false
% 2.50/0.96  --trig_cnt_out                          false
% 2.50/0.96  --trig_cnt_out_tolerance                1.
% 2.50/0.96  --trig_cnt_out_sk_spl                   false
% 2.50/0.96  --abstr_cl_out                          false
% 2.50/0.96  
% 2.50/0.96  ------ Global Options
% 2.50/0.96  
% 2.50/0.96  --schedule                              default
% 2.50/0.96  --add_important_lit                     false
% 2.50/0.96  --prop_solver_per_cl                    1000
% 2.50/0.96  --min_unsat_core                        false
% 2.50/0.96  --soft_assumptions                      false
% 2.50/0.96  --soft_lemma_size                       3
% 2.50/0.96  --prop_impl_unit_size                   0
% 2.50/0.96  --prop_impl_unit                        []
% 2.50/0.96  --share_sel_clauses                     true
% 2.50/0.96  --reset_solvers                         false
% 2.50/0.96  --bc_imp_inh                            [conj_cone]
% 2.50/0.96  --conj_cone_tolerance                   3.
% 2.50/0.96  --extra_neg_conj                        none
% 2.50/0.96  --large_theory_mode                     true
% 2.50/0.96  --prolific_symb_bound                   200
% 2.50/0.96  --lt_threshold                          2000
% 2.50/0.96  --clause_weak_htbl                      true
% 2.50/0.96  --gc_record_bc_elim                     false
% 2.50/0.96  
% 2.50/0.96  ------ Preprocessing Options
% 2.50/0.96  
% 2.50/0.96  --preprocessing_flag                    true
% 2.50/0.96  --time_out_prep_mult                    0.1
% 2.50/0.96  --splitting_mode                        input
% 2.50/0.96  --splitting_grd                         true
% 2.50/0.96  --splitting_cvd                         false
% 2.50/0.96  --splitting_cvd_svl                     false
% 2.50/0.96  --splitting_nvd                         32
% 2.50/0.96  --sub_typing                            true
% 2.50/0.96  --prep_gs_sim                           true
% 2.50/0.96  --prep_unflatten                        true
% 2.50/0.96  --prep_res_sim                          true
% 2.50/0.96  --prep_upred                            true
% 2.50/0.96  --prep_sem_filter                       exhaustive
% 2.50/0.96  --prep_sem_filter_out                   false
% 2.50/0.96  --pred_elim                             true
% 2.50/0.96  --res_sim_input                         true
% 2.50/0.96  --eq_ax_congr_red                       true
% 2.50/0.96  --pure_diseq_elim                       true
% 2.50/0.96  --brand_transform                       false
% 2.50/0.96  --non_eq_to_eq                          false
% 2.50/0.96  --prep_def_merge                        true
% 2.50/0.96  --prep_def_merge_prop_impl              false
% 2.50/0.96  --prep_def_merge_mbd                    true
% 2.50/0.96  --prep_def_merge_tr_red                 false
% 2.50/0.96  --prep_def_merge_tr_cl                  false
% 2.50/0.96  --smt_preprocessing                     true
% 2.50/0.96  --smt_ac_axioms                         fast
% 2.50/0.96  --preprocessed_out                      false
% 2.50/0.96  --preprocessed_stats                    false
% 2.50/0.96  
% 2.50/0.96  ------ Abstraction refinement Options
% 2.50/0.96  
% 2.50/0.96  --abstr_ref                             []
% 2.50/0.96  --abstr_ref_prep                        false
% 2.50/0.96  --abstr_ref_until_sat                   false
% 2.50/0.96  --abstr_ref_sig_restrict                funpre
% 2.50/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.96  --abstr_ref_under                       []
% 2.50/0.96  
% 2.50/0.96  ------ SAT Options
% 2.50/0.96  
% 2.50/0.96  --sat_mode                              false
% 2.50/0.96  --sat_fm_restart_options                ""
% 2.50/0.96  --sat_gr_def                            false
% 2.50/0.96  --sat_epr_types                         true
% 2.50/0.96  --sat_non_cyclic_types                  false
% 2.50/0.96  --sat_finite_models                     false
% 2.50/0.96  --sat_fm_lemmas                         false
% 2.50/0.96  --sat_fm_prep                           false
% 2.50/0.96  --sat_fm_uc_incr                        true
% 2.50/0.96  --sat_out_model                         small
% 2.50/0.96  --sat_out_clauses                       false
% 2.50/0.96  
% 2.50/0.96  ------ QBF Options
% 2.50/0.96  
% 2.50/0.96  --qbf_mode                              false
% 2.50/0.96  --qbf_elim_univ                         false
% 2.50/0.96  --qbf_dom_inst                          none
% 2.50/0.96  --qbf_dom_pre_inst                      false
% 2.50/0.96  --qbf_sk_in                             false
% 2.50/0.96  --qbf_pred_elim                         true
% 2.50/0.96  --qbf_split                             512
% 2.50/0.96  
% 2.50/0.96  ------ BMC1 Options
% 2.50/0.96  
% 2.50/0.96  --bmc1_incremental                      false
% 2.50/0.96  --bmc1_axioms                           reachable_all
% 2.50/0.96  --bmc1_min_bound                        0
% 2.50/0.96  --bmc1_max_bound                        -1
% 2.50/0.96  --bmc1_max_bound_default                -1
% 2.50/0.96  --bmc1_symbol_reachability              true
% 2.50/0.96  --bmc1_property_lemmas                  false
% 2.50/0.96  --bmc1_k_induction                      false
% 2.50/0.96  --bmc1_non_equiv_states                 false
% 2.50/0.96  --bmc1_deadlock                         false
% 2.50/0.96  --bmc1_ucm                              false
% 2.50/0.96  --bmc1_add_unsat_core                   none
% 2.50/0.96  --bmc1_unsat_core_children              false
% 2.50/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.96  --bmc1_out_stat                         full
% 2.50/0.96  --bmc1_ground_init                      false
% 2.50/0.96  --bmc1_pre_inst_next_state              false
% 2.50/0.96  --bmc1_pre_inst_state                   false
% 2.50/0.96  --bmc1_pre_inst_reach_state             false
% 2.50/0.96  --bmc1_out_unsat_core                   false
% 2.50/0.96  --bmc1_aig_witness_out                  false
% 2.50/0.96  --bmc1_verbose                          false
% 2.50/0.96  --bmc1_dump_clauses_tptp                false
% 2.50/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.96  --bmc1_dump_file                        -
% 2.50/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.96  --bmc1_ucm_extend_mode                  1
% 2.50/0.96  --bmc1_ucm_init_mode                    2
% 2.50/0.96  --bmc1_ucm_cone_mode                    none
% 2.50/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.96  --bmc1_ucm_relax_model                  4
% 2.50/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.96  --bmc1_ucm_layered_model                none
% 2.50/0.96  --bmc1_ucm_max_lemma_size               10
% 2.50/0.96  
% 2.50/0.96  ------ AIG Options
% 2.50/0.96  
% 2.50/0.96  --aig_mode                              false
% 2.50/0.96  
% 2.50/0.96  ------ Instantiation Options
% 2.50/0.96  
% 2.50/0.96  --instantiation_flag                    true
% 2.50/0.96  --inst_sos_flag                         false
% 2.50/0.96  --inst_sos_phase                        true
% 2.50/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.96  --inst_lit_sel_side                     num_symb
% 2.50/0.96  --inst_solver_per_active                1400
% 2.50/0.96  --inst_solver_calls_frac                1.
% 2.50/0.96  --inst_passive_queue_type               priority_queues
% 2.50/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.96  --inst_passive_queues_freq              [25;2]
% 2.50/0.96  --inst_dismatching                      true
% 2.50/0.96  --inst_eager_unprocessed_to_passive     true
% 2.50/0.96  --inst_prop_sim_given                   true
% 2.50/0.96  --inst_prop_sim_new                     false
% 2.50/0.96  --inst_subs_new                         false
% 2.50/0.96  --inst_eq_res_simp                      false
% 2.50/0.96  --inst_subs_given                       false
% 2.50/0.96  --inst_orphan_elimination               true
% 2.50/0.96  --inst_learning_loop_flag               true
% 2.50/0.96  --inst_learning_start                   3000
% 2.50/0.96  --inst_learning_factor                  2
% 2.50/0.96  --inst_start_prop_sim_after_learn       3
% 2.50/0.96  --inst_sel_renew                        solver
% 2.50/0.96  --inst_lit_activity_flag                true
% 2.50/0.96  --inst_restr_to_given                   false
% 2.50/0.96  --inst_activity_threshold               500
% 2.50/0.96  --inst_out_proof                        true
% 2.50/0.96  
% 2.50/0.96  ------ Resolution Options
% 2.50/0.96  
% 2.50/0.96  --resolution_flag                       true
% 2.50/0.96  --res_lit_sel                           adaptive
% 2.50/0.96  --res_lit_sel_side                      none
% 2.50/0.96  --res_ordering                          kbo
% 2.50/0.96  --res_to_prop_solver                    active
% 2.50/0.96  --res_prop_simpl_new                    false
% 2.50/0.96  --res_prop_simpl_given                  true
% 2.50/0.96  --res_passive_queue_type                priority_queues
% 2.50/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.96  --res_passive_queues_freq               [15;5]
% 2.50/0.96  --res_forward_subs                      full
% 2.50/0.96  --res_backward_subs                     full
% 2.50/0.96  --res_forward_subs_resolution           true
% 2.50/0.96  --res_backward_subs_resolution          true
% 2.50/0.96  --res_orphan_elimination                true
% 2.50/0.96  --res_time_limit                        2.
% 2.50/0.96  --res_out_proof                         true
% 2.50/0.96  
% 2.50/0.96  ------ Superposition Options
% 2.50/0.96  
% 2.50/0.96  --superposition_flag                    true
% 2.50/0.96  --sup_passive_queue_type                priority_queues
% 2.50/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.96  --demod_completeness_check              fast
% 2.50/0.96  --demod_use_ground                      true
% 2.50/0.96  --sup_to_prop_solver                    passive
% 2.50/0.96  --sup_prop_simpl_new                    true
% 2.50/0.96  --sup_prop_simpl_given                  true
% 2.50/0.96  --sup_fun_splitting                     false
% 2.50/0.96  --sup_smt_interval                      50000
% 2.50/0.96  
% 2.50/0.96  ------ Superposition Simplification Setup
% 2.50/0.96  
% 2.50/0.96  --sup_indices_passive                   []
% 2.50/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.96  --sup_full_bw                           [BwDemod]
% 2.50/0.96  --sup_immed_triv                        [TrivRules]
% 2.50/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.96  --sup_immed_bw_main                     []
% 2.50/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.96  
% 2.50/0.96  ------ Combination Options
% 2.50/0.96  
% 2.50/0.96  --comb_res_mult                         3
% 2.50/0.96  --comb_sup_mult                         2
% 2.50/0.96  --comb_inst_mult                        10
% 2.50/0.96  
% 2.50/0.96  ------ Debug Options
% 2.50/0.96  
% 2.50/0.96  --dbg_backtrace                         false
% 2.50/0.96  --dbg_dump_prop_clauses                 false
% 2.50/0.96  --dbg_dump_prop_clauses_file            -
% 2.50/0.96  --dbg_out_stat                          false
% 2.50/0.96  ------ Parsing...
% 2.50/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.50/0.96  
% 2.50/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.50/0.96  
% 2.50/0.96  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.50/0.96  
% 2.50/0.96  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.50/0.96  ------ Proving...
% 2.50/0.96  ------ Problem Properties 
% 2.50/0.96  
% 2.50/0.96  
% 2.50/0.96  clauses                                 29
% 2.50/0.96  conjectures                             5
% 2.50/0.96  EPR                                     2
% 2.50/0.96  Horn                                    27
% 2.50/0.96  unary                                   11
% 2.50/0.96  binary                                  1
% 2.50/0.96  lits                                    100
% 2.50/0.96  lits eq                                 23
% 2.50/0.96  fd_pure                                 0
% 2.50/0.96  fd_pseudo                               0
% 2.50/0.96  fd_cond                                 2
% 2.50/0.96  fd_pseudo_cond                          1
% 2.50/0.96  AC symbols                              0
% 2.50/0.96  
% 2.50/0.96  ------ Schedule dynamic 5 is on 
% 2.50/0.96  
% 2.50/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.50/0.96  
% 2.50/0.96  
% 2.50/0.96  ------ 
% 2.50/0.96  Current options:
% 2.50/0.96  ------ 
% 2.50/0.96  
% 2.50/0.96  ------ Input Options
% 2.50/0.96  
% 2.50/0.96  --out_options                           all
% 2.50/0.96  --tptp_safe_out                         true
% 2.50/0.96  --problem_path                          ""
% 2.50/0.96  --include_path                          ""
% 2.50/0.96  --clausifier                            res/vclausify_rel
% 2.50/0.96  --clausifier_options                    --mode clausify
% 2.50/0.96  --stdin                                 false
% 2.50/0.96  --stats_out                             all
% 2.50/0.96  
% 2.50/0.96  ------ General Options
% 2.50/0.96  
% 2.50/0.96  --fof                                   false
% 2.50/0.96  --time_out_real                         305.
% 2.50/0.96  --time_out_virtual                      -1.
% 2.50/0.96  --symbol_type_check                     false
% 2.50/0.96  --clausify_out                          false
% 2.50/0.96  --sig_cnt_out                           false
% 2.50/0.96  --trig_cnt_out                          false
% 2.50/0.96  --trig_cnt_out_tolerance                1.
% 2.50/0.96  --trig_cnt_out_sk_spl                   false
% 2.50/0.96  --abstr_cl_out                          false
% 2.50/0.96  
% 2.50/0.96  ------ Global Options
% 2.50/0.96  
% 2.50/0.96  --schedule                              default
% 2.50/0.96  --add_important_lit                     false
% 2.50/0.96  --prop_solver_per_cl                    1000
% 2.50/0.96  --min_unsat_core                        false
% 2.50/0.96  --soft_assumptions                      false
% 2.50/0.96  --soft_lemma_size                       3
% 2.50/0.96  --prop_impl_unit_size                   0
% 2.50/0.96  --prop_impl_unit                        []
% 2.50/0.96  --share_sel_clauses                     true
% 2.50/0.96  --reset_solvers                         false
% 2.50/0.96  --bc_imp_inh                            [conj_cone]
% 2.50/0.96  --conj_cone_tolerance                   3.
% 2.50/0.96  --extra_neg_conj                        none
% 2.50/0.96  --large_theory_mode                     true
% 2.50/0.96  --prolific_symb_bound                   200
% 2.50/0.96  --lt_threshold                          2000
% 2.50/0.96  --clause_weak_htbl                      true
% 2.50/0.96  --gc_record_bc_elim                     false
% 2.50/0.96  
% 2.50/0.96  ------ Preprocessing Options
% 2.50/0.96  
% 2.50/0.96  --preprocessing_flag                    true
% 2.50/0.96  --time_out_prep_mult                    0.1
% 2.50/0.96  --splitting_mode                        input
% 2.50/0.96  --splitting_grd                         true
% 2.50/0.96  --splitting_cvd                         false
% 2.50/0.96  --splitting_cvd_svl                     false
% 2.50/0.96  --splitting_nvd                         32
% 2.50/0.96  --sub_typing                            true
% 2.50/0.96  --prep_gs_sim                           true
% 2.50/0.96  --prep_unflatten                        true
% 2.50/0.96  --prep_res_sim                          true
% 2.50/0.96  --prep_upred                            true
% 2.50/0.96  --prep_sem_filter                       exhaustive
% 2.50/0.96  --prep_sem_filter_out                   false
% 2.50/0.96  --pred_elim                             true
% 2.50/0.96  --res_sim_input                         true
% 2.50/0.96  --eq_ax_congr_red                       true
% 2.50/0.96  --pure_diseq_elim                       true
% 2.50/0.96  --brand_transform                       false
% 2.50/0.96  --non_eq_to_eq                          false
% 2.50/0.96  --prep_def_merge                        true
% 2.50/0.96  --prep_def_merge_prop_impl              false
% 2.50/0.96  --prep_def_merge_mbd                    true
% 2.50/0.96  --prep_def_merge_tr_red                 false
% 2.50/0.96  --prep_def_merge_tr_cl                  false
% 2.50/0.96  --smt_preprocessing                     true
% 2.50/0.96  --smt_ac_axioms                         fast
% 2.50/0.96  --preprocessed_out                      false
% 2.50/0.96  --preprocessed_stats                    false
% 2.50/0.96  
% 2.50/0.96  ------ Abstraction refinement Options
% 2.50/0.96  
% 2.50/0.96  --abstr_ref                             []
% 2.50/0.96  --abstr_ref_prep                        false
% 2.50/0.96  --abstr_ref_until_sat                   false
% 2.50/0.96  --abstr_ref_sig_restrict                funpre
% 2.50/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.50/0.96  --abstr_ref_under                       []
% 2.50/0.96  
% 2.50/0.96  ------ SAT Options
% 2.50/0.96  
% 2.50/0.96  --sat_mode                              false
% 2.50/0.96  --sat_fm_restart_options                ""
% 2.50/0.96  --sat_gr_def                            false
% 2.50/0.96  --sat_epr_types                         true
% 2.50/0.96  --sat_non_cyclic_types                  false
% 2.50/0.96  --sat_finite_models                     false
% 2.50/0.96  --sat_fm_lemmas                         false
% 2.50/0.96  --sat_fm_prep                           false
% 2.50/0.96  --sat_fm_uc_incr                        true
% 2.50/0.96  --sat_out_model                         small
% 2.50/0.96  --sat_out_clauses                       false
% 2.50/0.96  
% 2.50/0.96  ------ QBF Options
% 2.50/0.96  
% 2.50/0.96  --qbf_mode                              false
% 2.50/0.96  --qbf_elim_univ                         false
% 2.50/0.96  --qbf_dom_inst                          none
% 2.50/0.96  --qbf_dom_pre_inst                      false
% 2.50/0.96  --qbf_sk_in                             false
% 2.50/0.96  --qbf_pred_elim                         true
% 2.50/0.96  --qbf_split                             512
% 2.50/0.96  
% 2.50/0.96  ------ BMC1 Options
% 2.50/0.96  
% 2.50/0.96  --bmc1_incremental                      false
% 2.50/0.96  --bmc1_axioms                           reachable_all
% 2.50/0.96  --bmc1_min_bound                        0
% 2.50/0.96  --bmc1_max_bound                        -1
% 2.50/0.96  --bmc1_max_bound_default                -1
% 2.50/0.96  --bmc1_symbol_reachability              true
% 2.50/0.96  --bmc1_property_lemmas                  false
% 2.50/0.96  --bmc1_k_induction                      false
% 2.50/0.96  --bmc1_non_equiv_states                 false
% 2.50/0.96  --bmc1_deadlock                         false
% 2.50/0.96  --bmc1_ucm                              false
% 2.50/0.96  --bmc1_add_unsat_core                   none
% 2.50/0.96  --bmc1_unsat_core_children              false
% 2.50/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.50/0.96  --bmc1_out_stat                         full
% 2.50/0.96  --bmc1_ground_init                      false
% 2.50/0.96  --bmc1_pre_inst_next_state              false
% 2.50/0.96  --bmc1_pre_inst_state                   false
% 2.50/0.96  --bmc1_pre_inst_reach_state             false
% 2.50/0.96  --bmc1_out_unsat_core                   false
% 2.50/0.96  --bmc1_aig_witness_out                  false
% 2.50/0.96  --bmc1_verbose                          false
% 2.50/0.96  --bmc1_dump_clauses_tptp                false
% 2.50/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.50/0.96  --bmc1_dump_file                        -
% 2.50/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.50/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.50/0.96  --bmc1_ucm_extend_mode                  1
% 2.50/0.96  --bmc1_ucm_init_mode                    2
% 2.50/0.96  --bmc1_ucm_cone_mode                    none
% 2.50/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.50/0.96  --bmc1_ucm_relax_model                  4
% 2.50/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.50/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.50/0.96  --bmc1_ucm_layered_model                none
% 2.50/0.96  --bmc1_ucm_max_lemma_size               10
% 2.50/0.96  
% 2.50/0.96  ------ AIG Options
% 2.50/0.96  
% 2.50/0.96  --aig_mode                              false
% 2.50/0.96  
% 2.50/0.96  ------ Instantiation Options
% 2.50/0.96  
% 2.50/0.96  --instantiation_flag                    true
% 2.50/0.96  --inst_sos_flag                         false
% 2.50/0.96  --inst_sos_phase                        true
% 2.50/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.50/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.50/0.96  --inst_lit_sel_side                     none
% 2.50/0.96  --inst_solver_per_active                1400
% 2.50/0.96  --inst_solver_calls_frac                1.
% 2.50/0.96  --inst_passive_queue_type               priority_queues
% 2.50/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.50/0.96  --inst_passive_queues_freq              [25;2]
% 2.50/0.96  --inst_dismatching                      true
% 2.50/0.96  --inst_eager_unprocessed_to_passive     true
% 2.50/0.96  --inst_prop_sim_given                   true
% 2.50/0.96  --inst_prop_sim_new                     false
% 2.50/0.96  --inst_subs_new                         false
% 2.50/0.96  --inst_eq_res_simp                      false
% 2.50/0.96  --inst_subs_given                       false
% 2.50/0.96  --inst_orphan_elimination               true
% 2.50/0.96  --inst_learning_loop_flag               true
% 2.50/0.96  --inst_learning_start                   3000
% 2.50/0.96  --inst_learning_factor                  2
% 2.50/0.96  --inst_start_prop_sim_after_learn       3
% 2.50/0.96  --inst_sel_renew                        solver
% 2.50/0.96  --inst_lit_activity_flag                true
% 2.50/0.96  --inst_restr_to_given                   false
% 2.50/0.96  --inst_activity_threshold               500
% 2.50/0.96  --inst_out_proof                        true
% 2.50/0.96  
% 2.50/0.96  ------ Resolution Options
% 2.50/0.96  
% 2.50/0.96  --resolution_flag                       false
% 2.50/0.96  --res_lit_sel                           adaptive
% 2.50/0.96  --res_lit_sel_side                      none
% 2.50/0.96  --res_ordering                          kbo
% 2.50/0.96  --res_to_prop_solver                    active
% 2.50/0.96  --res_prop_simpl_new                    false
% 2.50/0.96  --res_prop_simpl_given                  true
% 2.50/0.96  --res_passive_queue_type                priority_queues
% 2.50/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.50/0.96  --res_passive_queues_freq               [15;5]
% 2.50/0.96  --res_forward_subs                      full
% 2.50/0.96  --res_backward_subs                     full
% 2.50/0.96  --res_forward_subs_resolution           true
% 2.50/0.96  --res_backward_subs_resolution          true
% 2.50/0.96  --res_orphan_elimination                true
% 2.50/0.96  --res_time_limit                        2.
% 2.50/0.96  --res_out_proof                         true
% 2.50/0.96  
% 2.50/0.96  ------ Superposition Options
% 2.50/0.96  
% 2.50/0.96  --superposition_flag                    true
% 2.50/0.96  --sup_passive_queue_type                priority_queues
% 2.50/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.50/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.50/0.96  --demod_completeness_check              fast
% 2.50/0.96  --demod_use_ground                      true
% 2.50/0.96  --sup_to_prop_solver                    passive
% 2.50/0.96  --sup_prop_simpl_new                    true
% 2.50/0.96  --sup_prop_simpl_given                  true
% 2.50/0.96  --sup_fun_splitting                     false
% 2.50/0.96  --sup_smt_interval                      50000
% 2.50/0.96  
% 2.50/0.96  ------ Superposition Simplification Setup
% 2.50/0.96  
% 2.50/0.96  --sup_indices_passive                   []
% 2.50/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.50/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.50/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.96  --sup_full_bw                           [BwDemod]
% 2.50/0.96  --sup_immed_triv                        [TrivRules]
% 2.50/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.50/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.96  --sup_immed_bw_main                     []
% 2.50/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.50/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.50/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.50/0.96  
% 2.50/0.96  ------ Combination Options
% 2.50/0.96  
% 2.50/0.96  --comb_res_mult                         3
% 2.50/0.96  --comb_sup_mult                         2
% 2.50/0.96  --comb_inst_mult                        10
% 2.50/0.96  
% 2.50/0.96  ------ Debug Options
% 2.50/0.96  
% 2.50/0.96  --dbg_backtrace                         false
% 2.50/0.96  --dbg_dump_prop_clauses                 false
% 2.50/0.96  --dbg_dump_prop_clauses_file            -
% 2.50/0.96  --dbg_out_stat                          false
% 2.50/0.96  
% 2.50/0.96  
% 2.50/0.96  
% 2.50/0.96  
% 2.50/0.96  ------ Proving...
% 2.50/0.96  
% 2.50/0.96  
% 2.50/0.96  % SZS status Theorem for theBenchmark.p
% 2.50/0.96  
% 2.50/0.96   Resolution empty clause
% 2.50/0.96  
% 2.50/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.50/0.96  
% 2.50/0.96  fof(f20,conjecture,(
% 2.50/0.96    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f21,negated_conjecture,(
% 2.50/0.96    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.50/0.96    inference(negated_conjecture,[],[f20])).
% 2.50/0.96  
% 2.50/0.96  fof(f49,plain,(
% 2.50/0.96    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.50/0.96    inference(ennf_transformation,[],[f21])).
% 2.50/0.96  
% 2.50/0.96  fof(f50,plain,(
% 2.50/0.96    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.50/0.96    inference(flattening,[],[f49])).
% 2.50/0.96  
% 2.50/0.96  fof(f54,plain,(
% 2.50/0.96    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.50/0.96    introduced(choice_axiom,[])).
% 2.50/0.96  
% 2.50/0.96  fof(f53,plain,(
% 2.50/0.96    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.50/0.96    introduced(choice_axiom,[])).
% 2.50/0.96  
% 2.50/0.96  fof(f52,plain,(
% 2.50/0.96    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.50/0.96    introduced(choice_axiom,[])).
% 2.50/0.96  
% 2.50/0.96  fof(f55,plain,(
% 2.50/0.96    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.50/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f54,f53,f52])).
% 2.50/0.96  
% 2.50/0.96  fof(f89,plain,(
% 2.50/0.96    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.50/0.96    inference(cnf_transformation,[],[f55])).
% 2.50/0.96  
% 2.50/0.96  fof(f17,axiom,(
% 2.50/0.96    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f44,plain,(
% 2.50/0.96    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.50/0.96    inference(ennf_transformation,[],[f17])).
% 2.50/0.96  
% 2.50/0.96  fof(f81,plain,(
% 2.50/0.96    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f44])).
% 2.50/0.96  
% 2.50/0.96  fof(f84,plain,(
% 2.50/0.96    l1_struct_0(sK0)),
% 2.50/0.96    inference(cnf_transformation,[],[f55])).
% 2.50/0.96  
% 2.50/0.96  fof(f86,plain,(
% 2.50/0.96    l1_struct_0(sK1)),
% 2.50/0.96    inference(cnf_transformation,[],[f55])).
% 2.50/0.96  
% 2.50/0.96  fof(f11,axiom,(
% 2.50/0.96    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f34,plain,(
% 2.50/0.96    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.50/0.96    inference(ennf_transformation,[],[f11])).
% 2.50/0.96  
% 2.50/0.96  fof(f35,plain,(
% 2.50/0.96    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.50/0.96    inference(flattening,[],[f34])).
% 2.50/0.96  
% 2.50/0.96  fof(f71,plain,(
% 2.50/0.96    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f35])).
% 2.50/0.96  
% 2.50/0.96  fof(f18,axiom,(
% 2.50/0.96    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f45,plain,(
% 2.50/0.96    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.50/0.96    inference(ennf_transformation,[],[f18])).
% 2.50/0.96  
% 2.50/0.96  fof(f46,plain,(
% 2.50/0.96    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.50/0.96    inference(flattening,[],[f45])).
% 2.50/0.96  
% 2.50/0.96  fof(f82,plain,(
% 2.50/0.96    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f46])).
% 2.50/0.96  
% 2.50/0.96  fof(f85,plain,(
% 2.50/0.96    ~v2_struct_0(sK1)),
% 2.50/0.96    inference(cnf_transformation,[],[f55])).
% 2.50/0.96  
% 2.50/0.96  fof(f12,axiom,(
% 2.50/0.96    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f36,plain,(
% 2.50/0.96    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.50/0.96    inference(ennf_transformation,[],[f12])).
% 2.50/0.96  
% 2.50/0.96  fof(f37,plain,(
% 2.50/0.96    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.50/0.96    inference(flattening,[],[f36])).
% 2.50/0.96  
% 2.50/0.96  fof(f51,plain,(
% 2.50/0.96    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.50/0.96    inference(nnf_transformation,[],[f37])).
% 2.50/0.96  
% 2.50/0.96  fof(f72,plain,(
% 2.50/0.96    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f51])).
% 2.50/0.96  
% 2.50/0.96  fof(f9,axiom,(
% 2.50/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f22,plain,(
% 2.50/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.50/0.96    inference(pure_predicate_removal,[],[f9])).
% 2.50/0.96  
% 2.50/0.96  fof(f32,plain,(
% 2.50/0.96    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.50/0.96    inference(ennf_transformation,[],[f22])).
% 2.50/0.96  
% 2.50/0.96  fof(f68,plain,(
% 2.50/0.96    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.50/0.96    inference(cnf_transformation,[],[f32])).
% 2.50/0.96  
% 2.50/0.96  fof(f87,plain,(
% 2.50/0.96    v1_funct_1(sK2)),
% 2.50/0.96    inference(cnf_transformation,[],[f55])).
% 2.50/0.96  
% 2.50/0.96  fof(f88,plain,(
% 2.50/0.96    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.50/0.96    inference(cnf_transformation,[],[f55])).
% 2.50/0.96  
% 2.50/0.96  fof(f2,axiom,(
% 2.50/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f23,plain,(
% 2.50/0.96    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.50/0.96    inference(ennf_transformation,[],[f2])).
% 2.50/0.96  
% 2.50/0.96  fof(f57,plain,(
% 2.50/0.96    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f23])).
% 2.50/0.96  
% 2.50/0.96  fof(f3,axiom,(
% 2.50/0.96    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f58,plain,(
% 2.50/0.96    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.50/0.96    inference(cnf_transformation,[],[f3])).
% 2.50/0.96  
% 2.50/0.96  fof(f10,axiom,(
% 2.50/0.96    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f33,plain,(
% 2.50/0.96    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.50/0.96    inference(ennf_transformation,[],[f10])).
% 2.50/0.96  
% 2.50/0.96  fof(f69,plain,(
% 2.50/0.96    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.50/0.96    inference(cnf_transformation,[],[f33])).
% 2.50/0.96  
% 2.50/0.96  fof(f90,plain,(
% 2.50/0.96    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.50/0.96    inference(cnf_transformation,[],[f55])).
% 2.50/0.96  
% 2.50/0.96  fof(f19,axiom,(
% 2.50/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f47,plain,(
% 2.50/0.96    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.50/0.96    inference(ennf_transformation,[],[f19])).
% 2.50/0.96  
% 2.50/0.96  fof(f48,plain,(
% 2.50/0.96    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.50/0.96    inference(flattening,[],[f47])).
% 2.50/0.96  
% 2.50/0.96  fof(f83,plain,(
% 2.50/0.96    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f48])).
% 2.50/0.96  
% 2.50/0.96  fof(f91,plain,(
% 2.50/0.96    v2_funct_1(sK2)),
% 2.50/0.96    inference(cnf_transformation,[],[f55])).
% 2.50/0.96  
% 2.50/0.96  fof(f14,axiom,(
% 2.50/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f38,plain,(
% 2.50/0.96    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.50/0.96    inference(ennf_transformation,[],[f14])).
% 2.50/0.96  
% 2.50/0.96  fof(f39,plain,(
% 2.50/0.96    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.50/0.96    inference(flattening,[],[f38])).
% 2.50/0.96  
% 2.50/0.96  fof(f75,plain,(
% 2.50/0.96    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f39])).
% 2.50/0.96  
% 2.50/0.96  fof(f92,plain,(
% 2.50/0.96    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.50/0.96    inference(cnf_transformation,[],[f55])).
% 2.50/0.96  
% 2.50/0.96  fof(f4,axiom,(
% 2.50/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f24,plain,(
% 2.50/0.96    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.50/0.96    inference(ennf_transformation,[],[f4])).
% 2.50/0.96  
% 2.50/0.96  fof(f25,plain,(
% 2.50/0.96    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.50/0.96    inference(flattening,[],[f24])).
% 2.50/0.96  
% 2.50/0.96  fof(f60,plain,(
% 2.50/0.96    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f25])).
% 2.50/0.96  
% 2.50/0.96  fof(f15,axiom,(
% 2.50/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f40,plain,(
% 2.50/0.96    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.50/0.96    inference(ennf_transformation,[],[f15])).
% 2.50/0.96  
% 2.50/0.96  fof(f41,plain,(
% 2.50/0.96    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.50/0.96    inference(flattening,[],[f40])).
% 2.50/0.96  
% 2.50/0.96  fof(f77,plain,(
% 2.50/0.96    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f41])).
% 2.50/0.96  
% 2.50/0.96  fof(f78,plain,(
% 2.50/0.96    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f41])).
% 2.50/0.96  
% 2.50/0.96  fof(f7,axiom,(
% 2.50/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f28,plain,(
% 2.50/0.96    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.50/0.96    inference(ennf_transformation,[],[f7])).
% 2.50/0.96  
% 2.50/0.96  fof(f29,plain,(
% 2.50/0.96    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.50/0.96    inference(flattening,[],[f28])).
% 2.50/0.96  
% 2.50/0.96  fof(f66,plain,(
% 2.50/0.96    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f29])).
% 2.50/0.96  
% 2.50/0.96  fof(f8,axiom,(
% 2.50/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f30,plain,(
% 2.50/0.96    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.50/0.96    inference(ennf_transformation,[],[f8])).
% 2.50/0.96  
% 2.50/0.96  fof(f31,plain,(
% 2.50/0.96    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.50/0.96    inference(flattening,[],[f30])).
% 2.50/0.96  
% 2.50/0.96  fof(f67,plain,(
% 2.50/0.96    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f31])).
% 2.50/0.96  
% 2.50/0.96  fof(f16,axiom,(
% 2.50/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f42,plain,(
% 2.50/0.96    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.50/0.96    inference(ennf_transformation,[],[f16])).
% 2.50/0.96  
% 2.50/0.96  fof(f43,plain,(
% 2.50/0.96    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.50/0.96    inference(flattening,[],[f42])).
% 2.50/0.96  
% 2.50/0.96  fof(f80,plain,(
% 2.50/0.96    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f43])).
% 2.50/0.96  
% 2.50/0.96  fof(f1,axiom,(
% 2.50/0.96    v1_xboole_0(k1_xboole_0)),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f56,plain,(
% 2.50/0.96    v1_xboole_0(k1_xboole_0)),
% 2.50/0.96    inference(cnf_transformation,[],[f1])).
% 2.50/0.96  
% 2.50/0.96  fof(f6,axiom,(
% 2.50/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f26,plain,(
% 2.50/0.96    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.50/0.96    inference(ennf_transformation,[],[f6])).
% 2.50/0.96  
% 2.50/0.96  fof(f27,plain,(
% 2.50/0.96    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.50/0.96    inference(flattening,[],[f26])).
% 2.50/0.96  
% 2.50/0.96  fof(f63,plain,(
% 2.50/0.96    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f27])).
% 2.50/0.96  
% 2.50/0.96  fof(f59,plain,(
% 2.50/0.96    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f25])).
% 2.50/0.96  
% 2.50/0.96  fof(f5,axiom,(
% 2.50/0.96    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f62,plain,(
% 2.50/0.96    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.50/0.96    inference(cnf_transformation,[],[f5])).
% 2.50/0.96  
% 2.50/0.96  fof(f13,axiom,(
% 2.50/0.96    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.50/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.50/0.96  
% 2.50/0.96  fof(f74,plain,(
% 2.50/0.96    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.50/0.96    inference(cnf_transformation,[],[f13])).
% 2.50/0.96  
% 2.50/0.96  fof(f93,plain,(
% 2.50/0.96    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.50/0.96    inference(definition_unfolding,[],[f62,f74])).
% 2.50/0.96  
% 2.50/0.96  cnf(c_30,negated_conjecture,
% 2.50/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.50/0.96      inference(cnf_transformation,[],[f89]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_714,negated_conjecture,
% 2.50/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.50/0.96      inference(subtyping,[status(esa)],[c_30]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1239,plain,
% 2.50/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.50/0.96      inference(predicate_to_equality,[status(thm)],[c_714]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_24,plain,
% 2.50/0.96      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.50/0.96      inference(cnf_transformation,[],[f81]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_35,negated_conjecture,
% 2.50/0.96      ( l1_struct_0(sK0) ),
% 2.50/0.96      inference(cnf_transformation,[],[f84]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_402,plain,
% 2.50/0.96      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.50/0.96      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_403,plain,
% 2.50/0.96      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.50/0.96      inference(unflattening,[status(thm)],[c_402]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_710,plain,
% 2.50/0.96      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.50/0.96      inference(subtyping,[status(esa)],[c_403]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_33,negated_conjecture,
% 2.50/0.96      ( l1_struct_0(sK1) ),
% 2.50/0.96      inference(cnf_transformation,[],[f86]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_397,plain,
% 2.50/0.96      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.50/0.96      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_398,plain,
% 2.50/0.96      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.50/0.96      inference(unflattening,[status(thm)],[c_397]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_711,plain,
% 2.50/0.96      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.50/0.96      inference(subtyping,[status(esa)],[c_398]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1268,plain,
% 2.50/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.50/0.96      inference(light_normalisation,[status(thm)],[c_1239,c_710,c_711]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_14,plain,
% 2.50/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/0.96      | v1_partfun1(X0,X1)
% 2.50/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.96      | ~ v1_funct_1(X0)
% 2.50/0.96      | v1_xboole_0(X2) ),
% 2.50/0.96      inference(cnf_transformation,[],[f71]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_25,plain,
% 2.50/0.96      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.50/0.96      inference(cnf_transformation,[],[f82]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_34,negated_conjecture,
% 2.50/0.96      ( ~ v2_struct_0(sK1) ),
% 2.50/0.96      inference(cnf_transformation,[],[f85]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_384,plain,
% 2.50/0.96      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.50/0.96      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_385,plain,
% 2.50/0.96      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.50/0.96      inference(unflattening,[status(thm)],[c_384]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_48,plain,
% 2.50/0.96      ( v2_struct_0(sK1)
% 2.50/0.96      | ~ l1_struct_0(sK1)
% 2.50/0.96      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.50/0.96      inference(instantiation,[status(thm)],[c_25]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_387,plain,
% 2.50/0.96      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.50/0.96      inference(global_propositional_subsumption,
% 2.50/0.96                [status(thm)],
% 2.50/0.96                [c_385,c_34,c_33,c_48]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_413,plain,
% 2.50/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/0.96      | v1_partfun1(X0,X1)
% 2.50/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.96      | ~ v1_funct_1(X0)
% 2.50/0.96      | u1_struct_0(sK1) != X2 ),
% 2.50/0.96      inference(resolution_lifted,[status(thm)],[c_14,c_387]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_414,plain,
% 2.50/0.96      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.50/0.96      | v1_partfun1(X0,X1)
% 2.50/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.50/0.96      | ~ v1_funct_1(X0) ),
% 2.50/0.96      inference(unflattening,[status(thm)],[c_413]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_17,plain,
% 2.50/0.96      ( ~ v1_partfun1(X0,X1)
% 2.50/0.96      | ~ v4_relat_1(X0,X1)
% 2.50/0.96      | ~ v1_relat_1(X0)
% 2.50/0.96      | k1_relat_1(X0) = X1 ),
% 2.50/0.96      inference(cnf_transformation,[],[f72]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_511,plain,
% 2.50/0.96      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.50/0.96      | ~ v4_relat_1(X0,X1)
% 2.50/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.50/0.96      | ~ v1_funct_1(X0)
% 2.50/0.96      | ~ v1_relat_1(X0)
% 2.50/0.96      | k1_relat_1(X0) = X1 ),
% 2.50/0.96      inference(resolution,[status(thm)],[c_414,c_17]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_12,plain,
% 2.50/0.96      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.50/0.96      inference(cnf_transformation,[],[f68]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_527,plain,
% 2.50/0.96      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.50/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.50/0.96      | ~ v1_funct_1(X0)
% 2.50/0.96      | ~ v1_relat_1(X0)
% 2.50/0.96      | k1_relat_1(X0) = X1 ),
% 2.50/0.96      inference(forward_subsumption_resolution,[status(thm)],[c_511,c_12]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_707,plain,
% 2.50/0.96      ( ~ v1_funct_2(X0_54,X0_55,u1_struct_0(sK1))
% 2.50/0.96      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1))))
% 2.50/0.96      | ~ v1_funct_1(X0_54)
% 2.50/0.96      | ~ v1_relat_1(X0_54)
% 2.50/0.96      | k1_relat_1(X0_54) = X0_55 ),
% 2.50/0.96      inference(subtyping,[status(esa)],[c_527]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1244,plain,
% 2.50/0.96      ( k1_relat_1(X0_54) = X0_55
% 2.50/0.96      | v1_funct_2(X0_54,X0_55,u1_struct_0(sK1)) != iProver_top
% 2.50/0.96      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,u1_struct_0(sK1)))) != iProver_top
% 2.50/0.96      | v1_funct_1(X0_54) != iProver_top
% 2.50/0.96      | v1_relat_1(X0_54) != iProver_top ),
% 2.50/0.96      inference(predicate_to_equality,[status(thm)],[c_707]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1326,plain,
% 2.50/0.96      ( k1_relat_1(X0_54) = X0_55
% 2.50/0.96      | v1_funct_2(X0_54,X0_55,k2_struct_0(sK1)) != iProver_top
% 2.50/0.96      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,k2_struct_0(sK1)))) != iProver_top
% 2.50/0.96      | v1_funct_1(X0_54) != iProver_top
% 2.50/0.96      | v1_relat_1(X0_54) != iProver_top ),
% 2.50/0.96      inference(light_normalisation,[status(thm)],[c_1244,c_711]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1825,plain,
% 2.50/0.96      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.50/0.96      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.50/0.96      | v1_funct_1(sK2) != iProver_top
% 2.50/0.96      | v1_relat_1(sK2) != iProver_top ),
% 2.50/0.96      inference(superposition,[status(thm)],[c_1268,c_1326]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_32,negated_conjecture,
% 2.50/0.96      ( v1_funct_1(sK2) ),
% 2.50/0.96      inference(cnf_transformation,[],[f87]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_39,plain,
% 2.50/0.96      ( v1_funct_1(sK2) = iProver_top ),
% 2.50/0.96      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_41,plain,
% 2.50/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.50/0.96      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_31,negated_conjecture,
% 2.50/0.96      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.50/0.96      inference(cnf_transformation,[],[f88]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_713,negated_conjecture,
% 2.50/0.96      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.50/0.96      inference(subtyping,[status(esa)],[c_31]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1240,plain,
% 2.50/0.96      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.50/0.96      inference(predicate_to_equality,[status(thm)],[c_713]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1262,plain,
% 2.50/0.96      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.50/0.96      inference(light_normalisation,[status(thm)],[c_1240,c_710,c_711]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1,plain,
% 2.50/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.50/0.96      inference(cnf_transformation,[],[f57]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_734,plain,
% 2.50/0.96      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 2.50/0.96      | ~ v1_relat_1(X1_54)
% 2.50/0.96      | v1_relat_1(X0_54) ),
% 2.50/0.96      inference(subtyping,[status(esa)],[c_1]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1527,plain,
% 2.50/0.96      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.50/0.96      | v1_relat_1(X0_54)
% 2.50/0.96      | ~ v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 2.50/0.96      inference(instantiation,[status(thm)],[c_734]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1710,plain,
% 2.50/0.96      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.50/0.96      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.50/0.96      | v1_relat_1(sK2) ),
% 2.50/0.96      inference(instantiation,[status(thm)],[c_1527]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1711,plain,
% 2.50/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.50/0.96      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.50/0.96      | v1_relat_1(sK2) = iProver_top ),
% 2.50/0.96      inference(predicate_to_equality,[status(thm)],[c_1710]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_2,plain,
% 2.50/0.96      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.50/0.96      inference(cnf_transformation,[],[f58]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_733,plain,
% 2.50/0.96      ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 2.50/0.96      inference(subtyping,[status(esa)],[c_2]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1758,plain,
% 2.50/0.96      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.50/0.96      inference(instantiation,[status(thm)],[c_733]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1759,plain,
% 2.50/0.96      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.50/0.96      inference(predicate_to_equality,[status(thm)],[c_1758]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1879,plain,
% 2.50/0.96      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.50/0.96      inference(global_propositional_subsumption,
% 2.50/0.96                [status(thm)],
% 2.50/0.96                [c_1825,c_39,c_41,c_1262,c_1711,c_1759]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1882,plain,
% 2.50/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 2.50/0.96      inference(demodulation,[status(thm)],[c_1879,c_1268]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_13,plain,
% 2.50/0.96      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.96      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.50/0.96      inference(cnf_transformation,[],[f69]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_723,plain,
% 2.50/0.96      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.50/0.96      | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
% 2.50/0.96      inference(subtyping,[status(esa)],[c_13]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1231,plain,
% 2.50/0.96      ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
% 2.50/0.96      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.50/0.96      inference(predicate_to_equality,[status(thm)],[c_723]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_2047,plain,
% 2.50/0.96      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.50/0.96      inference(superposition,[status(thm)],[c_1882,c_1231]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_29,negated_conjecture,
% 2.50/0.96      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.50/0.96      inference(cnf_transformation,[],[f90]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_715,negated_conjecture,
% 2.50/0.96      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.50/0.96      inference(subtyping,[status(esa)],[c_29]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1265,plain,
% 2.50/0.96      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.50/0.96      inference(light_normalisation,[status(thm)],[c_715,c_710,c_711]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1884,plain,
% 2.50/0.96      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.50/0.96      inference(demodulation,[status(thm)],[c_1879,c_1265]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_2294,plain,
% 2.50/0.96      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.50/0.96      inference(demodulation,[status(thm)],[c_2047,c_1884]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_2296,plain,
% 2.50/0.96      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.50/0.96      inference(demodulation,[status(thm)],[c_2294,c_2047]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_26,plain,
% 2.50/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.96      | ~ v2_funct_1(X0)
% 2.50/0.96      | ~ v1_funct_1(X0)
% 2.50/0.96      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.50/0.96      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.50/0.96      inference(cnf_transformation,[],[f83]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_717,plain,
% 2.50/0.96      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.50/0.96      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.50/0.96      | ~ v2_funct_1(X0_54)
% 2.50/0.96      | ~ v1_funct_1(X0_54)
% 2.50/0.96      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.50/0.96      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
% 2.50/0.96      inference(subtyping,[status(esa)],[c_26]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1237,plain,
% 2.50/0.96      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.50/0.96      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
% 2.50/0.96      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.50/0.96      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.50/0.96      | v2_funct_1(X0_54) != iProver_top
% 2.50/0.96      | v1_funct_1(X0_54) != iProver_top ),
% 2.50/0.96      inference(predicate_to_equality,[status(thm)],[c_717]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_3166,plain,
% 2.50/0.96      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.50/0.96      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.50/0.96      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.50/0.96      | v2_funct_1(sK2) != iProver_top
% 2.50/0.96      | v1_funct_1(sK2) != iProver_top ),
% 2.50/0.96      inference(superposition,[status(thm)],[c_2296,c_1237]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_28,negated_conjecture,
% 2.50/0.96      ( v2_funct_1(sK2) ),
% 2.50/0.96      inference(cnf_transformation,[],[f91]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_42,plain,
% 2.50/0.96      ( v2_funct_1(sK2) = iProver_top ),
% 2.50/0.96      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_2298,plain,
% 2.50/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.50/0.96      inference(demodulation,[status(thm)],[c_2294,c_1882]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_1883,plain,
% 2.50/0.96      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
% 2.50/0.96      inference(demodulation,[status(thm)],[c_1879,c_1262]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_2299,plain,
% 2.50/0.96      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.50/0.96      inference(demodulation,[status(thm)],[c_2294,c_1883]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_3804,plain,
% 2.50/0.96      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.50/0.96      inference(global_propositional_subsumption,
% 2.50/0.96                [status(thm)],
% 2.50/0.96                [c_3166,c_39,c_42,c_2298,c_2299]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_18,plain,
% 2.50/0.96      ( r2_funct_2(X0,X1,X2,X2)
% 2.50/0.96      | ~ v1_funct_2(X2,X0,X1)
% 2.50/0.96      | ~ v1_funct_2(X3,X0,X1)
% 2.50/0.96      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.50/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.50/0.96      | ~ v1_funct_1(X2)
% 2.50/0.96      | ~ v1_funct_1(X3) ),
% 2.50/0.96      inference(cnf_transformation,[],[f75]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_27,negated_conjecture,
% 2.50/0.96      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.50/0.96      inference(cnf_transformation,[],[f92]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_437,plain,
% 2.50/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/0.96      | ~ v1_funct_2(X3,X1,X2)
% 2.50/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.96      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.96      | ~ v1_funct_1(X0)
% 2.50/0.96      | ~ v1_funct_1(X3)
% 2.50/0.96      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.50/0.96      | u1_struct_0(sK1) != X2
% 2.50/0.96      | u1_struct_0(sK0) != X1
% 2.50/0.96      | sK2 != X0 ),
% 2.50/0.96      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_438,plain,
% 2.50/0.96      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.50/0.96      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.50/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.50/0.96      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.50/0.96      | ~ v1_funct_1(X0)
% 2.50/0.96      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.50/0.96      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.50/0.96      inference(unflattening,[status(thm)],[c_437]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_708,plain,
% 2.50/0.96      ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.50/0.96      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.50/0.96      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.50/0.96      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.50/0.96      | ~ v1_funct_1(X0_54)
% 2.50/0.96      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.50/0.96      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.50/0.96      inference(subtyping,[status(esa)],[c_438]) ).
% 2.50/0.96  
% 2.50/0.96  cnf(c_736,plain,
% 2.50/0.96      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.50/0.96      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.50/0.97      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.50/0.97      | sP0_iProver_split
% 2.50/0.97      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.50/0.97      inference(splitting,
% 2.50/0.97                [splitting(split),new_symbols(definition,[])],
% 2.50/0.97                [c_708]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1242,plain,
% 2.50/0.97      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.50/0.97      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.50/0.97      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.50/0.97      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.50/0.97      | sP0_iProver_split = iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1441,plain,
% 2.50/0.97      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.50/0.97      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.50/0.97      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.50/0.97      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.50/0.97      | sP0_iProver_split = iProver_top ),
% 2.50/0.97      inference(light_normalisation,[status(thm)],[c_1242,c_710,c_711]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_735,plain,
% 2.50/0.97      ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.50/0.97      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.50/0.97      | ~ v1_funct_1(X0_54)
% 2.50/0.97      | ~ sP0_iProver_split ),
% 2.50/0.97      inference(splitting,
% 2.50/0.97                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.50/0.97                [c_708]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1243,plain,
% 2.50/0.97      ( v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.50/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.50/0.97      | v1_funct_1(X0_54) != iProver_top
% 2.50/0.97      | sP0_iProver_split != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_735]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1317,plain,
% 2.50/0.97      ( v1_funct_2(X0_54,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.50/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.50/0.97      | v1_funct_1(X0_54) != iProver_top
% 2.50/0.97      | sP0_iProver_split != iProver_top ),
% 2.50/0.97      inference(light_normalisation,[status(thm)],[c_1243,c_710,c_711]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1447,plain,
% 2.50/0.97      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.50/0.97      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.50/0.97      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.50/0.97      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.50/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_1441,c_1317]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_2229,plain,
% 2.50/0.97      ( k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) != sK2
% 2.50/0.97      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_relat_1(sK2),k2_struct_0(sK1)) != iProver_top
% 2.50/0.97      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) != iProver_top
% 2.50/0.97      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.50/0.97      inference(light_normalisation,[status(thm)],[c_1447,c_1879]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_2297,plain,
% 2.50/0.97      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 2.50/0.97      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.50/0.97      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.50/0.97      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.50/0.97      inference(demodulation,[status(thm)],[c_2294,c_2229]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3807,plain,
% 2.50/0.97      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.50/0.97      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.50/0.97      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.50/0.97      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.50/0.97      inference(demodulation,[status(thm)],[c_3804,c_2297]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3,plain,
% 2.50/0.97      ( ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) | ~ v1_relat_1(X0) ),
% 2.50/0.97      inference(cnf_transformation,[],[f60]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_732,plain,
% 2.50/0.97      ( ~ v1_funct_1(X0_54)
% 2.50/0.97      | v1_funct_1(k2_funct_1(X0_54))
% 2.50/0.97      | ~ v1_relat_1(X0_54) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_3]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_777,plain,
% 2.50/0.97      ( v1_funct_1(X0_54) != iProver_top
% 2.50/0.97      | v1_funct_1(k2_funct_1(X0_54)) = iProver_top
% 2.50/0.97      | v1_relat_1(X0_54) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_732]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_779,plain,
% 2.50/0.97      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.50/0.97      | v1_funct_1(sK2) != iProver_top
% 2.50/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_777]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_20,plain,
% 2.50/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/0.97      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.50/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.97      | ~ v2_funct_1(X0)
% 2.50/0.97      | ~ v1_funct_1(X0)
% 2.50/0.97      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.50/0.97      inference(cnf_transformation,[],[f77]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_721,plain,
% 2.50/0.97      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.50/0.97      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
% 2.50/0.97      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.50/0.97      | ~ v2_funct_1(X0_54)
% 2.50/0.97      | ~ v1_funct_1(X0_54)
% 2.50/0.97      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_20]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1233,plain,
% 2.50/0.97      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.50/0.97      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.50/0.97      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
% 2.50/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.50/0.97      | v2_funct_1(X0_54) != iProver_top
% 2.50/0.97      | v1_funct_1(X0_54) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_721]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3167,plain,
% 2.50/0.97      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.50/0.97      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.50/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.50/0.97      | v2_funct_1(sK2) != iProver_top
% 2.50/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_2296,c_1233]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_19,plain,
% 2.50/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.97      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.50/0.97      | ~ v2_funct_1(X0)
% 2.50/0.97      | ~ v1_funct_1(X0)
% 2.50/0.97      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.50/0.97      inference(cnf_transformation,[],[f78]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_722,plain,
% 2.50/0.97      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.50/0.97      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.50/0.97      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
% 2.50/0.97      | ~ v2_funct_1(X0_54)
% 2.50/0.97      | ~ v1_funct_1(X0_54)
% 2.50/0.97      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_19]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1232,plain,
% 2.50/0.97      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.50/0.97      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.50/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.50/0.97      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
% 2.50/0.97      | v2_funct_1(X0_54) != iProver_top
% 2.50/0.97      | v1_funct_1(X0_54) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3197,plain,
% 2.50/0.97      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.50/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.50/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.50/0.97      | v2_funct_1(sK2) != iProver_top
% 2.50/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_2296,c_1232]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3967,plain,
% 2.50/0.97      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_3197,c_39,c_42,c_2298,c_2299]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3973,plain,
% 2.50/0.97      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_3967,c_1231]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_716,negated_conjecture,
% 2.50/0.97      ( v2_funct_1(sK2) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_28]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1238,plain,
% 2.50/0.97      ( v2_funct_1(sK2) = iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_716]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_9,plain,
% 2.50/0.97      ( ~ v2_funct_1(X0)
% 2.50/0.97      | ~ v1_funct_1(X0)
% 2.50/0.97      | ~ v1_relat_1(X0)
% 2.50/0.97      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.50/0.97      inference(cnf_transformation,[],[f66]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_726,plain,
% 2.50/0.97      ( ~ v2_funct_1(X0_54)
% 2.50/0.97      | ~ v1_funct_1(X0_54)
% 2.50/0.97      | ~ v1_relat_1(X0_54)
% 2.50/0.97      | k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_9]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1228,plain,
% 2.50/0.97      ( k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54)
% 2.50/0.97      | v2_funct_1(X0_54) != iProver_top
% 2.50/0.97      | v1_funct_1(X0_54) != iProver_top
% 2.50/0.97      | v1_relat_1(X0_54) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_726]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_2114,plain,
% 2.50/0.97      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.50/0.97      | v1_funct_1(sK2) != iProver_top
% 2.50/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_1238,c_1228]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_792,plain,
% 2.50/0.97      ( ~ v2_funct_1(sK2)
% 2.50/0.97      | ~ v1_funct_1(sK2)
% 2.50/0.97      | ~ v1_relat_1(sK2)
% 2.50/0.97      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_726]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_2201,plain,
% 2.50/0.97      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_2114,c_32,c_30,c_28,c_792,c_1710,c_1758]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3980,plain,
% 2.50/0.97      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.50/0.97      inference(light_normalisation,[status(thm)],[c_3973,c_2201]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4242,plain,
% 2.50/0.97      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.50/0.97      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.50/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.50/0.97      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.50/0.97      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_3980,c_1237]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_11,plain,
% 2.50/0.97      ( ~ v2_funct_1(X0)
% 2.50/0.97      | ~ v1_funct_1(X0)
% 2.50/0.97      | ~ v1_relat_1(X0)
% 2.50/0.97      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.50/0.97      inference(cnf_transformation,[],[f67]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_724,plain,
% 2.50/0.97      ( ~ v2_funct_1(X0_54)
% 2.50/0.97      | ~ v1_funct_1(X0_54)
% 2.50/0.97      | ~ v1_relat_1(X0_54)
% 2.50/0.97      | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_11]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1230,plain,
% 2.50/0.97      ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
% 2.50/0.97      | v2_funct_1(X0_54) != iProver_top
% 2.50/0.97      | v1_funct_1(X0_54) != iProver_top
% 2.50/0.97      | v1_relat_1(X0_54) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_724]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_2053,plain,
% 2.50/0.97      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.50/0.97      | v1_funct_1(sK2) != iProver_top
% 2.50/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_1238,c_1230]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_798,plain,
% 2.50/0.97      ( ~ v2_funct_1(sK2)
% 2.50/0.97      | ~ v1_funct_1(sK2)
% 2.50/0.97      | ~ v1_relat_1(sK2)
% 2.50/0.97      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_724]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_2195,plain,
% 2.50/0.97      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_2053,c_32,c_30,c_28,c_798,c_1710,c_1758]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4255,plain,
% 2.50/0.97      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.50/0.97      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.50/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.50/0.97      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.50/0.97      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.50/0.97      inference(light_normalisation,[status(thm)],[c_4242,c_2195]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_22,plain,
% 2.50/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.50/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.50/0.97      | ~ v2_funct_1(X0)
% 2.50/0.97      | ~ v1_funct_1(X0)
% 2.50/0.97      | k2_relset_1(X1,X2,X0) != X2
% 2.50/0.97      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 2.50/0.97      | k1_xboole_0 = X2 ),
% 2.50/0.97      inference(cnf_transformation,[],[f80]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_719,plain,
% 2.50/0.97      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.50/0.97      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.50/0.97      | ~ v2_funct_1(X0_54)
% 2.50/0.97      | ~ v1_funct_1(X0_54)
% 2.50/0.97      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.50/0.97      | k1_xboole_0 = X1_55
% 2.50/0.97      | k5_relat_1(k2_funct_1(X0_54),X0_54) = k6_partfun1(X1_55) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_22]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1235,plain,
% 2.50/0.97      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.50/0.97      | k1_xboole_0 = X1_55
% 2.50/0.97      | k5_relat_1(k2_funct_1(X0_54),X0_54) = k6_partfun1(X1_55)
% 2.50/0.97      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.50/0.97      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.50/0.97      | v2_funct_1(X0_54) != iProver_top
% 2.50/0.97      | v1_funct_1(X0_54) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_719]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3274,plain,
% 2.50/0.97      ( k2_relat_1(sK2) = k1_xboole_0
% 2.50/0.97      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 2.50/0.97      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.50/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.50/0.97      | v2_funct_1(sK2) != iProver_top
% 2.50/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_2296,c_1235]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_0,plain,
% 2.50/0.97      ( v1_xboole_0(k1_xboole_0) ),
% 2.50/0.97      inference(cnf_transformation,[],[f56]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_409,plain,
% 2.50/0.97      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.50/0.97      inference(resolution_lifted,[status(thm)],[c_0,c_387]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_709,plain,
% 2.50/0.97      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_409]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1257,plain,
% 2.50/0.97      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.50/0.97      inference(light_normalisation,[status(thm)],[c_709,c_711]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_2301,plain,
% 2.50/0.97      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.50/0.97      inference(demodulation,[status(thm)],[c_2294,c_1257]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4153,plain,
% 2.50/0.97      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_3274,c_39,c_42,c_2298,c_2299,c_2301]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_8,plain,
% 2.50/0.97      ( v2_funct_1(X0)
% 2.50/0.97      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 2.50/0.97      | ~ v1_funct_1(X1)
% 2.50/0.97      | ~ v1_funct_1(X0)
% 2.50/0.97      | ~ v1_relat_1(X1)
% 2.50/0.97      | ~ v1_relat_1(X0)
% 2.50/0.97      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 2.50/0.97      inference(cnf_transformation,[],[f63]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_727,plain,
% 2.50/0.97      ( v2_funct_1(X0_54)
% 2.50/0.97      | ~ v2_funct_1(k5_relat_1(X0_54,X1_54))
% 2.50/0.97      | ~ v1_funct_1(X0_54)
% 2.50/0.97      | ~ v1_funct_1(X1_54)
% 2.50/0.97      | ~ v1_relat_1(X0_54)
% 2.50/0.97      | ~ v1_relat_1(X1_54)
% 2.50/0.97      | k1_relat_1(X1_54) != k2_relat_1(X0_54) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_8]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1227,plain,
% 2.50/0.97      ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
% 2.50/0.97      | v2_funct_1(X1_54) = iProver_top
% 2.50/0.97      | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
% 2.50/0.97      | v1_funct_1(X1_54) != iProver_top
% 2.50/0.97      | v1_funct_1(X0_54) != iProver_top
% 2.50/0.97      | v1_relat_1(X1_54) != iProver_top
% 2.50/0.97      | v1_relat_1(X0_54) != iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_2604,plain,
% 2.50/0.97      ( k1_relat_1(X0_54) != k1_relat_1(sK2)
% 2.50/0.97      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_54)) != iProver_top
% 2.50/0.97      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.50/0.97      | v1_funct_1(X0_54) != iProver_top
% 2.50/0.97      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.50/0.97      | v1_relat_1(X0_54) != iProver_top
% 2.50/0.97      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_2201,c_1227]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4,plain,
% 2.50/0.97      ( ~ v1_funct_1(X0) | ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) ),
% 2.50/0.97      inference(cnf_transformation,[],[f59]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_731,plain,
% 2.50/0.97      ( ~ v1_funct_1(X0_54)
% 2.50/0.97      | ~ v1_relat_1(X0_54)
% 2.50/0.97      | v1_relat_1(k2_funct_1(X0_54)) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_4]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_780,plain,
% 2.50/0.97      ( v1_funct_1(X0_54) != iProver_top
% 2.50/0.97      | v1_relat_1(X0_54) != iProver_top
% 2.50/0.97      | v1_relat_1(k2_funct_1(X0_54)) = iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_782,plain,
% 2.50/0.97      ( v1_funct_1(sK2) != iProver_top
% 2.50/0.97      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.50/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_780]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3093,plain,
% 2.50/0.97      ( v1_relat_1(X0_54) != iProver_top
% 2.50/0.97      | k1_relat_1(X0_54) != k1_relat_1(sK2)
% 2.50/0.97      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_54)) != iProver_top
% 2.50/0.97      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.50/0.97      | v1_funct_1(X0_54) != iProver_top ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_2604,c_39,c_41,c_779,c_782,c_1711,c_1759]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3094,plain,
% 2.50/0.97      ( k1_relat_1(X0_54) != k1_relat_1(sK2)
% 2.50/0.97      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0_54)) != iProver_top
% 2.50/0.97      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.50/0.97      | v1_funct_1(X0_54) != iProver_top
% 2.50/0.97      | v1_relat_1(X0_54) != iProver_top ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_3093]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3105,plain,
% 2.50/0.97      ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 2.50/0.97      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.50/0.97      | v1_funct_1(sK2) != iProver_top
% 2.50/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.50/0.97      inference(equality_resolution,[status(thm)],[c_3094]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_751,plain,
% 2.50/0.97      ( k1_relat_1(X0_54) = k1_relat_1(X1_54) | X0_54 != X1_54 ),
% 2.50/0.97      theory(equality) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_764,plain,
% 2.50/0.97      ( k1_relat_1(sK2) = k1_relat_1(sK2) | sK2 != sK2 ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_751]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_738,plain,( X0_54 = X0_54 ),theory(equality) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_770,plain,
% 2.50/0.97      ( sK2 = sK2 ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_738]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3096,plain,
% 2.50/0.97      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 2.50/0.97      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 2.50/0.97      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.50/0.97      | v1_funct_1(sK2) != iProver_top
% 2.50/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.50/0.97      inference(instantiation,[status(thm)],[c_3094]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_3736,plain,
% 2.50/0.97      ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),sK2)) != iProver_top
% 2.50/0.97      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_3105,c_39,c_41,c_764,c_770,c_1711,c_1759,c_3096]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4156,plain,
% 2.50/0.97      ( v2_funct_1(k6_partfun1(k2_relat_1(sK2))) != iProver_top
% 2.50/0.97      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.50/0.97      inference(demodulation,[status(thm)],[c_4153,c_3736]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_5,plain,
% 2.50/0.97      ( v2_funct_1(k6_partfun1(X0)) ),
% 2.50/0.97      inference(cnf_transformation,[],[f93]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_730,plain,
% 2.50/0.97      ( v2_funct_1(k6_partfun1(X0_55)) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_5]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1224,plain,
% 2.50/0.97      ( v2_funct_1(k6_partfun1(X0_55)) = iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_730]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4398,plain,
% 2.50/0.97      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.50/0.97      inference(forward_subsumption_resolution,[status(thm)],[c_4156,c_1224]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4482,plain,
% 2.50/0.97      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.50/0.97      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.50/0.97      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_3807,c_39,c_41,c_42,c_779,c_1711,c_1759,c_2298,c_2299,
% 2.50/0.97                 c_3167,c_3197,c_4255,c_4398]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4283,plain,
% 2.50/0.97      ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.50/0.97      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.50/0.97      inference(global_propositional_subsumption,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_4255,c_39,c_41,c_42,c_779,c_1711,c_1759,c_2298,c_2299,
% 2.50/0.97                 c_3167,c_3197]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4284,plain,
% 2.50/0.97      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.50/0.97      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.50/0.97      inference(renaming,[status(thm)],[c_4283]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4403,plain,
% 2.50/0.97      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.50/0.97      inference(superposition,[status(thm)],[c_4398,c_4284]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4486,plain,
% 2.50/0.97      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.50/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.50/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.50/0.97      inference(light_normalisation,[status(thm)],[c_4482,c_4403]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_712,negated_conjecture,
% 2.50/0.97      ( v1_funct_1(sK2) ),
% 2.50/0.97      inference(subtyping,[status(esa)],[c_32]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_1241,plain,
% 2.50/0.97      ( v1_funct_1(sK2) = iProver_top ),
% 2.50/0.97      inference(predicate_to_equality,[status(thm)],[c_712]) ).
% 2.50/0.97  
% 2.50/0.97  cnf(c_4490,plain,
% 2.50/0.97      ( $false ),
% 2.50/0.97      inference(forward_subsumption_resolution,
% 2.50/0.97                [status(thm)],
% 2.50/0.97                [c_4486,c_1241,c_2298,c_2299]) ).
% 2.50/0.97  
% 2.50/0.97  
% 2.50/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.50/0.97  
% 2.50/0.97  ------                               Statistics
% 2.50/0.97  
% 2.50/0.97  ------ General
% 2.50/0.97  
% 2.50/0.97  abstr_ref_over_cycles:                  0
% 2.50/0.97  abstr_ref_under_cycles:                 0
% 2.50/0.97  gc_basic_clause_elim:                   0
% 2.50/0.97  forced_gc_time:                         0
% 2.50/0.97  parsing_time:                           0.009
% 2.50/0.97  unif_index_cands_time:                  0.
% 2.50/0.97  unif_index_add_time:                    0.
% 2.50/0.97  orderings_time:                         0.
% 2.50/0.97  out_proof_time:                         0.014
% 2.50/0.97  total_time:                             0.214
% 2.50/0.97  num_of_symbols:                         62
% 2.50/0.97  num_of_terms:                           4218
% 2.50/0.97  
% 2.50/0.97  ------ Preprocessing
% 2.50/0.97  
% 2.50/0.97  num_of_splits:                          1
% 2.50/0.97  num_of_split_atoms:                     1
% 2.50/0.97  num_of_reused_defs:                     0
% 2.50/0.97  num_eq_ax_congr_red:                    7
% 2.50/0.97  num_of_sem_filtered_clauses:            2
% 2.50/0.97  num_of_subtypes:                        4
% 2.50/0.97  monotx_restored_types:                  1
% 2.50/0.97  sat_num_of_epr_types:                   0
% 2.50/0.97  sat_num_of_non_cyclic_types:            0
% 2.50/0.97  sat_guarded_non_collapsed_types:        1
% 2.50/0.97  num_pure_diseq_elim:                    0
% 2.50/0.97  simp_replaced_by:                       0
% 2.50/0.97  res_preprocessed:                       157
% 2.50/0.97  prep_upred:                             0
% 2.50/0.97  prep_unflattend:                        11
% 2.50/0.97  smt_new_axioms:                         0
% 2.50/0.97  pred_elim_cands:                        5
% 2.50/0.97  pred_elim:                              6
% 2.50/0.97  pred_elim_cl:                           7
% 2.50/0.97  pred_elim_cycles:                       9
% 2.50/0.97  merged_defs:                            0
% 2.50/0.97  merged_defs_ncl:                        0
% 2.50/0.97  bin_hyper_res:                          0
% 2.50/0.97  prep_cycles:                            4
% 2.50/0.97  pred_elim_time:                         0.011
% 2.50/0.97  splitting_time:                         0.
% 2.50/0.97  sem_filter_time:                        0.
% 2.50/0.97  monotx_time:                            0.
% 2.50/0.97  subtype_inf_time:                       0.001
% 2.50/0.97  
% 2.50/0.97  ------ Problem properties
% 2.50/0.97  
% 2.50/0.97  clauses:                                29
% 2.50/0.97  conjectures:                            5
% 2.50/0.97  epr:                                    2
% 2.50/0.97  horn:                                   27
% 2.50/0.97  ground:                                 9
% 2.50/0.97  unary:                                  11
% 2.50/0.97  binary:                                 1
% 2.50/0.97  lits:                                   100
% 2.50/0.97  lits_eq:                                23
% 2.50/0.97  fd_pure:                                0
% 2.50/0.97  fd_pseudo:                              0
% 2.50/0.97  fd_cond:                                2
% 2.50/0.97  fd_pseudo_cond:                         1
% 2.50/0.97  ac_symbols:                             0
% 2.50/0.97  
% 2.50/0.97  ------ Propositional Solver
% 2.50/0.97  
% 2.50/0.97  prop_solver_calls:                      28
% 2.50/0.97  prop_fast_solver_calls:                 1333
% 2.50/0.97  smt_solver_calls:                       0
% 2.50/0.97  smt_fast_solver_calls:                  0
% 2.50/0.97  prop_num_of_clauses:                    1671
% 2.50/0.97  prop_preprocess_simplified:             5910
% 2.50/0.97  prop_fo_subsumed:                       67
% 2.50/0.97  prop_solver_time:                       0.
% 2.50/0.97  smt_solver_time:                        0.
% 2.50/0.97  smt_fast_solver_time:                   0.
% 2.50/0.97  prop_fast_solver_time:                  0.
% 2.50/0.97  prop_unsat_core_time:                   0.
% 2.50/0.97  
% 2.50/0.97  ------ QBF
% 2.50/0.97  
% 2.50/0.97  qbf_q_res:                              0
% 2.50/0.97  qbf_num_tautologies:                    0
% 2.50/0.97  qbf_prep_cycles:                        0
% 2.50/0.97  
% 2.50/0.97  ------ BMC1
% 2.50/0.97  
% 2.50/0.97  bmc1_current_bound:                     -1
% 2.50/0.97  bmc1_last_solved_bound:                 -1
% 2.50/0.97  bmc1_unsat_core_size:                   -1
% 2.50/0.97  bmc1_unsat_core_parents_size:           -1
% 2.50/0.97  bmc1_merge_next_fun:                    0
% 2.50/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.50/0.97  
% 2.50/0.97  ------ Instantiation
% 2.50/0.97  
% 2.50/0.97  inst_num_of_clauses:                    578
% 2.50/0.97  inst_num_in_passive:                    69
% 2.50/0.97  inst_num_in_active:                     321
% 2.50/0.97  inst_num_in_unprocessed:                188
% 2.50/0.97  inst_num_of_loops:                      350
% 2.50/0.97  inst_num_of_learning_restarts:          0
% 2.50/0.97  inst_num_moves_active_passive:          25
% 2.50/0.97  inst_lit_activity:                      0
% 2.50/0.97  inst_lit_activity_moves:                0
% 2.50/0.97  inst_num_tautologies:                   0
% 2.50/0.97  inst_num_prop_implied:                  0
% 2.50/0.97  inst_num_existing_simplified:           0
% 2.50/0.97  inst_num_eq_res_simplified:             0
% 2.50/0.97  inst_num_child_elim:                    0
% 2.50/0.97  inst_num_of_dismatching_blockings:      118
% 2.50/0.97  inst_num_of_non_proper_insts:           546
% 2.50/0.97  inst_num_of_duplicates:                 0
% 2.50/0.97  inst_inst_num_from_inst_to_res:         0
% 2.50/0.97  inst_dismatching_checking_time:         0.
% 2.50/0.97  
% 2.50/0.97  ------ Resolution
% 2.50/0.97  
% 2.50/0.97  res_num_of_clauses:                     0
% 2.50/0.97  res_num_in_passive:                     0
% 2.50/0.97  res_num_in_active:                      0
% 2.50/0.97  res_num_of_loops:                       161
% 2.50/0.97  res_forward_subset_subsumed:            48
% 2.50/0.97  res_backward_subset_subsumed:           0
% 2.50/0.97  res_forward_subsumed:                   0
% 2.50/0.97  res_backward_subsumed:                  0
% 2.50/0.97  res_forward_subsumption_resolution:     1
% 2.50/0.97  res_backward_subsumption_resolution:    0
% 2.50/0.97  res_clause_to_clause_subsumption:       90
% 2.50/0.97  res_orphan_elimination:                 0
% 2.50/0.97  res_tautology_del:                      60
% 2.50/0.97  res_num_eq_res_simplified:              0
% 2.50/0.97  res_num_sel_changes:                    0
% 2.50/0.97  res_moves_from_active_to_pass:          0
% 2.50/0.97  
% 2.50/0.97  ------ Superposition
% 2.50/0.97  
% 2.50/0.97  sup_time_total:                         0.
% 2.50/0.97  sup_time_generating:                    0.
% 2.50/0.97  sup_time_sim_full:                      0.
% 2.50/0.97  sup_time_sim_immed:                     0.
% 2.50/0.97  
% 2.50/0.97  sup_num_of_clauses:                     52
% 2.50/0.97  sup_num_in_active:                      52
% 2.50/0.97  sup_num_in_passive:                     0
% 2.50/0.97  sup_num_of_loops:                       68
% 2.50/0.97  sup_fw_superposition:                   20
% 2.50/0.97  sup_bw_superposition:                   22
% 2.50/0.97  sup_immediate_simplified:               16
% 2.50/0.97  sup_given_eliminated:                   0
% 2.50/0.97  comparisons_done:                       0
% 2.50/0.97  comparisons_avoided:                    0
% 2.50/0.97  
% 2.50/0.97  ------ Simplifications
% 2.50/0.97  
% 2.50/0.97  
% 2.50/0.97  sim_fw_subset_subsumed:                 6
% 2.50/0.97  sim_bw_subset_subsumed:                 1
% 2.50/0.97  sim_fw_subsumed:                        3
% 2.50/0.97  sim_bw_subsumed:                        0
% 2.50/0.97  sim_fw_subsumption_res:                 5
% 2.50/0.97  sim_bw_subsumption_res:                 0
% 2.50/0.97  sim_tautology_del:                      0
% 2.50/0.97  sim_eq_tautology_del:                   7
% 2.50/0.97  sim_eq_res_simp:                        0
% 2.50/0.97  sim_fw_demodulated:                     0
% 2.50/0.97  sim_bw_demodulated:                     15
% 2.50/0.97  sim_light_normalised:                   19
% 2.50/0.97  sim_joinable_taut:                      0
% 2.50/0.97  sim_joinable_simp:                      0
% 2.50/0.97  sim_ac_normalised:                      0
% 2.50/0.97  sim_smt_subsumption:                    0
% 2.50/0.97  
%------------------------------------------------------------------------------
