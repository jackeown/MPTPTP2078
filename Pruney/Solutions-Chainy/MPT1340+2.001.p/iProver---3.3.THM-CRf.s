%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:20 EST 2020

% Result     : Theorem 6.74s
% Output     : CNFRefutation 6.74s
% Verified   : 
% Statistics : Number of formulae       :  234 (3986 expanded)
%              Number of clauses        :  145 (1097 expanded)
%              Number of leaves         :   24 (1150 expanded)
%              Depth                    :   22
%              Number of atoms          :  931 (26232 expanded)
%              Number of equality atoms :  355 (4239 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f34,conjecture,(
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

fof(f35,negated_conjecture,(
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
    inference(negated_conjecture,[],[f34])).

fof(f80,plain,(
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
    inference(ennf_transformation,[],[f35])).

fof(f81,plain,(
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
    inference(flattening,[],[f80])).

fof(f92,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3)),sK3)
        & v2_funct_1(sK3)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) = k2_struct_0(X1)
        & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f91,plain,(
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
            ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK2),X2)),X2)
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) = k2_struct_0(sK2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2))
            & v1_funct_1(X2) )
        & l1_struct_0(sK2)
        & ~ v2_struct_0(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f90,plain,
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
              ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f93,plain,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3)
    & v2_funct_1(sK3)
    & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    & v1_funct_1(sK3)
    & l1_struct_0(sK2)
    & ~ v2_struct_0(sK2)
    & l1_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f81,f92,f91,f90])).

fof(f157,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f93])).

fof(f31,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f149,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f75])).

fof(f154,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f93])).

fof(f152,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f93])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f59])).

fof(f126,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f63])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f64])).

fof(f130,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f87])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f19])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f37])).

fof(f123,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f155,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

fof(f32,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f76])).

fof(f150,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f77])).

fof(f153,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f93])).

fof(f156,plain,(
    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f93])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f158,plain,(
    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f93])).

fof(f29,axiom,(
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

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f71])).

fof(f145,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f159,plain,(
    v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f93])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f30,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f74,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f73])).

fof(f148,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f147,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1)
              & k1_relat_1(X1) = k2_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
          | k1_relat_1(X1) != k2_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f54])).

fof(f121,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1)
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f25,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f137,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f25])).

fof(f163,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
      | k1_relat_1(X1) != k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f121,f137])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f53,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f119,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f120,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f28,axiom,(
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

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f70,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f69])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f33,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f79,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f78])).

fof(f151,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f79])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f47,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f115,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f141,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f110,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f66,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f65])).

fof(f138,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f160,plain,(
    ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f93])).

fof(f109,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_60,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
    inference(cnf_transformation,[],[f157])).

cnf(c_2015,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_54,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f149])).

cnf(c_63,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_681,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_54,c_63])).

cnf(c_682,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_681])).

cnf(c_65,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f152])).

cnf(c_686,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_54,c_65])).

cnf(c_687,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_686])).

cnf(c_2089,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2015,c_682,c_687])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_37,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_836,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_31,c_37])).

cnf(c_29,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_838,plain,
    ( ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_836,c_29,c_28])).

cnf(c_839,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_838])).

cnf(c_2006,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_839])).

cnf(c_2618,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3)
    | v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2089,c_2006])).

cnf(c_62,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f155])).

cnf(c_69,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_55,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_64,negated_conjecture,
    ( ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f153])).

cnf(c_668,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_55,c_64])).

cnf(c_669,plain,
    ( ~ l1_struct_0(sK2)
    | ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_671,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_63])).

cnf(c_2010,plain,
    ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_2072,plain,
    ( v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2010,c_682])).

cnf(c_61,negated_conjecture,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
    inference(cnf_transformation,[],[f156])).

cnf(c_2014,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_2081,plain,
    ( v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2014,c_682,c_687])).

cnf(c_3076,plain,
    ( k2_struct_0(sK1) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2618,c_69,c_2072,c_2081])).

cnf(c_3081,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_struct_0(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3076,c_2089])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_2028,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_5228,plain,
    ( k2_relset_1(k1_relat_1(sK3),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3081,c_2028])).

cnf(c_59,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f158])).

cnf(c_2086,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(light_normalisation,[status(thm)],[c_59,c_682,c_687])).

cnf(c_3083,plain,
    ( k2_relset_1(k1_relat_1(sK3),k2_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
    inference(demodulation,[status(thm)],[c_3076,c_2086])).

cnf(c_5470,plain,
    ( k2_struct_0(sK2) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_5228,c_3083])).

cnf(c_5473,plain,
    ( k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) = k2_relat_1(sK3) ),
    inference(demodulation,[status(thm)],[c_5470,c_5228])).

cnf(c_49,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f145])).

cnf(c_2021,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_9217,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3))
    | k2_relat_1(sK3) = k1_xboole_0
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_5473,c_2021])).

cnf(c_71,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_58,negated_conjecture,
    ( v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_72,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2536,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2537,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2536])).

cnf(c_51,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_2895,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_51])).

cnf(c_2911,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2895])).

cnf(c_52,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_2894,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_52])).

cnf(c_2913,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2894])).

cnf(c_5477,plain,
    ( v1_xboole_0(k2_relat_1(sK3)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5470,c_2072])).

cnf(c_5493,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK3)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_5477])).

cnf(c_1208,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_5750,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(sK3))
    | k2_relat_1(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_1208])).

cnf(c_5755,plain,
    ( v1_xboole_0(k2_relat_1(sK3))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_relat_1(sK3) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5750])).

cnf(c_23586,plain,
    ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_9217,c_69,c_71,c_72,c_0,c_2537,c_2911,c_2913,c_5493,c_5755])).

cnf(c_27,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X0) != k1_relat_1(X1) ),
    inference(cnf_transformation,[],[f163])).

cnf(c_2030,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23589,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1(sK3))) != k6_partfun1(k2_relat_1(sK3))
    | k2_funct_1(k2_funct_1(sK3)) = sK3
    | k2_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK3)
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_23586,c_2030])).

cnf(c_2016,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_26,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_2031,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_6973,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2016,c_2031])).

cnf(c_2575,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_7437,plain,
    ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6973,c_62,c_60,c_58,c_2536,c_2575])).

cnf(c_25,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2032,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7104,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2016,c_2032])).

cnf(c_2567,plain,
    ( ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_7465,plain,
    ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7104,c_62,c_60,c_58,c_2536,c_2567])).

cnf(c_23590,plain,
    ( k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(k2_relat_1(sK3))
    | k2_funct_1(k2_funct_1(sK3)) = sK3
    | k1_relat_1(sK3) != k1_relat_1(sK3)
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_23589,c_7437,c_7465])).

cnf(c_23591,plain,
    ( k2_funct_1(k2_funct_1(sK3)) = sK3
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_23590])).

cnf(c_2019,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_7468,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7465,c_2019])).

cnf(c_7488,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7468,c_7437])).

cnf(c_46,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f143])).

cnf(c_2790,plain,
    ( ~ v1_funct_2(sK3,X0,X1)
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X0,X1,sK3) != X1 ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_3682,plain,
    ( ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2790])).

cnf(c_3683,plain,
    ( k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) != k2_relat_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3682])).

cnf(c_3703,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_7727,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7488,c_62,c_69,c_60,c_71,c_72,c_2536,c_2537,c_2895,c_2911,c_2913,c_3683,c_3703])).

cnf(c_7734,plain,
    ( k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_relat_1(k2_funct_1(sK3)) ),
    inference(superposition,[status(thm)],[c_7727,c_2028])).

cnf(c_7755,plain,
    ( k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(sK3) ),
    inference(light_normalisation,[status(thm)],[c_7734,c_7465])).

cnf(c_56,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f151])).

cnf(c_2017,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_7817,plain,
    ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7755,c_2017])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_2533,plain,
    ( v2_funct_1(k2_funct_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_2534,plain,
    ( v2_funct_1(k2_funct_1(sK3)) = iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2533])).

cnf(c_48,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f141])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_356,plain,
    ( v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_48,c_28,c_15])).

cnf(c_357,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(renaming,[status(thm)],[c_356])).

cnf(c_2593,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | v1_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(sK3) ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_2594,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) = iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2593])).

cnf(c_47,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f142])).

cnf(c_2800,plain,
    ( v1_funct_2(k2_funct_1(sK3),X0,X1)
    | ~ v1_funct_2(sK3,X1,X0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(X1,X0,sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_3687,plain,
    ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2800])).

cnf(c_3688,plain,
    ( k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) != k2_relat_1(sK3)
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3687])).

cnf(c_2844,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),X0,X1)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_tops_2(X0,X1,k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
    | k2_relset_1(X0,X1,k2_funct_1(sK3)) != X1 ),
    inference(instantiation,[status(thm)],[c_56])).

cnf(c_6032,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
    | k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2844])).

cnf(c_6033,plain,
    ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
    | k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != k1_relat_1(sK3)
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6032])).

cnf(c_13663,plain,
    ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7817,c_62,c_69,c_60,c_71,c_72,c_2534,c_2536,c_2537,c_2594,c_2895,c_2911,c_2913,c_3683,c_3688,c_3703,c_6033,c_7755])).

cnf(c_5294,plain,
    ( k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3) = k2_funct_1(sK3)
    | v1_funct_2(sK3,k1_relat_1(sK3),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_struct_0(sK2)))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3083,c_2017])).

cnf(c_3082,plain,
    ( v1_funct_2(sK3,k1_relat_1(sK3),k2_struct_0(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3076,c_2081])).

cnf(c_5464,plain,
    ( k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3) = k2_funct_1(sK3) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5294,c_69,c_72,c_3081,c_3082])).

cnf(c_43,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_57,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) ),
    inference(cnf_transformation,[],[f160])).

cnf(c_693,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != X0
    | u1_struct_0(sK2) != X2
    | u1_struct_0(sK1) != X1
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_57])).

cnf(c_694,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
    | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(unflattening,[status(thm)],[c_693])).

cnf(c_1204,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
    | sP0_iProver_split
    | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_694])).

cnf(c_2008,plain,
    ( sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1204])).

cnf(c_2372,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2008,c_682,c_687])).

cnf(c_1203,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v1_funct_1(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_694])).

cnf(c_2009,plain,
    ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1203])).

cnf(c_2225,plain,
    ( v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2009,c_682,c_687])).

cnf(c_2378,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2372,c_2225])).

cnf(c_3079,plain,
    ( k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3)),k1_relat_1(sK3),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3076,c_2378])).

cnf(c_5467,plain,
    ( k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_funct_1(sK3)),k1_relat_1(sK3),k2_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_struct_0(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_funct_1(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5464,c_3079])).

cnf(c_6365,plain,
    ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)),k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5467,c_5470])).

cnf(c_13666,plain,
    ( k2_funct_1(k2_funct_1(sK3)) != sK3
    | v1_funct_2(k2_funct_1(k2_funct_1(sK3)),k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
    | v1_funct_1(k2_funct_1(k2_funct_1(sK3))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_13663,c_6365])).

cnf(c_2845,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK3)),X0,X1)
    | ~ v1_funct_2(k2_funct_1(sK3),X1,X0)
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_relset_1(X1,X0,k2_funct_1(sK3)) != X0 ),
    inference(instantiation,[status(thm)],[c_47])).

cnf(c_6037,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK3)),k1_relat_1(sK3),k2_relat_1(sK3))
    | ~ v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2845])).

cnf(c_6038,plain,
    ( k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != k1_relat_1(sK3)
    | v1_funct_2(k2_funct_1(k2_funct_1(sK3)),k1_relat_1(sK3),k2_relat_1(sK3)) = iProver_top
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6037])).

cnf(c_2846,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),X0,X1)
    | m1_subset_1(k2_funct_1(k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_relset_1(X0,X1,k2_funct_1(sK3)) != X1 ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_6031,plain,
    ( ~ v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
    | m1_subset_1(k2_funct_1(k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
    | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
    | ~ v2_funct_1(k2_funct_1(sK3))
    | ~ v1_funct_1(k2_funct_1(sK3))
    | k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != k1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_2846])).

cnf(c_6035,plain,
    ( k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != k1_relat_1(sK3)
    | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK3)) != iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6031])).

cnf(c_1207,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3891,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != X0
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | u1_struct_0(sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_1207])).

cnf(c_5782,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
    | u1_struct_0(sK2) != k2_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_3891])).

cnf(c_3646,plain,
    ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(k2_funct_1(sK3)))
    | ~ v1_funct_1(k2_funct_1(sK3)) ),
    inference(instantiation,[status(thm)],[c_357])).

cnf(c_3650,plain,
    ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(k2_funct_1(sK3))) = iProver_top
    | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3646])).

cnf(c_3048,plain,
    ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
    inference(instantiation,[status(thm)],[c_2790])).

cnf(c_3049,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
    | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3048])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_2897,plain,
    ( ~ v1_funct_1(sK3)
    | v1_relat_1(k2_funct_1(sK3))
    | ~ v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2907,plain,
    ( v1_funct_1(sK3) != iProver_top
    | v1_relat_1(k2_funct_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2897])).

cnf(c_70,plain,
    ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_23591,c_13666,c_7755,c_6038,c_6035,c_5782,c_3703,c_3688,c_3683,c_3650,c_3049,c_2913,c_2911,c_2895,c_2907,c_2594,c_2537,c_2536,c_2534,c_682,c_72,c_59,c_71,c_60,c_70,c_69,c_62])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n007.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 15:38:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 6.74/1.49  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.74/1.49  
% 6.74/1.49  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 6.74/1.49  
% 6.74/1.49  ------  iProver source info
% 6.74/1.49  
% 6.74/1.49  git: date: 2020-06-30 10:37:57 +0100
% 6.74/1.49  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 6.74/1.49  git: non_committed_changes: false
% 6.74/1.49  git: last_make_outside_of_git: false
% 6.74/1.49  
% 6.74/1.49  ------ 
% 6.74/1.49  
% 6.74/1.49  ------ Input Options
% 6.74/1.49  
% 6.74/1.49  --out_options                           all
% 6.74/1.49  --tptp_safe_out                         true
% 6.74/1.49  --problem_path                          ""
% 6.74/1.49  --include_path                          ""
% 6.74/1.49  --clausifier                            res/vclausify_rel
% 6.74/1.49  --clausifier_options                    --mode clausify
% 6.74/1.49  --stdin                                 false
% 6.74/1.49  --stats_out                             all
% 6.74/1.49  
% 6.74/1.49  ------ General Options
% 6.74/1.49  
% 6.74/1.49  --fof                                   false
% 6.74/1.49  --time_out_real                         305.
% 6.74/1.49  --time_out_virtual                      -1.
% 6.74/1.49  --symbol_type_check                     false
% 6.74/1.49  --clausify_out                          false
% 6.74/1.49  --sig_cnt_out                           false
% 6.74/1.49  --trig_cnt_out                          false
% 6.74/1.49  --trig_cnt_out_tolerance                1.
% 6.74/1.49  --trig_cnt_out_sk_spl                   false
% 6.74/1.49  --abstr_cl_out                          false
% 6.74/1.49  
% 6.74/1.49  ------ Global Options
% 6.74/1.49  
% 6.74/1.49  --schedule                              default
% 6.74/1.49  --add_important_lit                     false
% 6.74/1.49  --prop_solver_per_cl                    1000
% 6.74/1.49  --min_unsat_core                        false
% 6.74/1.49  --soft_assumptions                      false
% 6.74/1.49  --soft_lemma_size                       3
% 6.74/1.49  --prop_impl_unit_size                   0
% 6.74/1.49  --prop_impl_unit                        []
% 6.74/1.49  --share_sel_clauses                     true
% 6.74/1.49  --reset_solvers                         false
% 6.74/1.49  --bc_imp_inh                            [conj_cone]
% 6.74/1.49  --conj_cone_tolerance                   3.
% 6.74/1.49  --extra_neg_conj                        none
% 6.74/1.49  --large_theory_mode                     true
% 6.74/1.49  --prolific_symb_bound                   200
% 6.74/1.49  --lt_threshold                          2000
% 6.74/1.49  --clause_weak_htbl                      true
% 6.74/1.49  --gc_record_bc_elim                     false
% 6.74/1.49  
% 6.74/1.49  ------ Preprocessing Options
% 6.74/1.49  
% 6.74/1.49  --preprocessing_flag                    true
% 6.74/1.49  --time_out_prep_mult                    0.1
% 6.74/1.49  --splitting_mode                        input
% 6.74/1.49  --splitting_grd                         true
% 6.74/1.49  --splitting_cvd                         false
% 6.74/1.49  --splitting_cvd_svl                     false
% 6.74/1.49  --splitting_nvd                         32
% 6.74/1.49  --sub_typing                            true
% 6.74/1.49  --prep_gs_sim                           true
% 6.74/1.49  --prep_unflatten                        true
% 6.74/1.49  --prep_res_sim                          true
% 6.74/1.49  --prep_upred                            true
% 6.74/1.49  --prep_sem_filter                       exhaustive
% 6.74/1.49  --prep_sem_filter_out                   false
% 6.74/1.49  --pred_elim                             true
% 6.74/1.49  --res_sim_input                         true
% 6.74/1.49  --eq_ax_congr_red                       true
% 6.74/1.49  --pure_diseq_elim                       true
% 6.74/1.49  --brand_transform                       false
% 6.74/1.49  --non_eq_to_eq                          false
% 6.74/1.49  --prep_def_merge                        true
% 6.74/1.49  --prep_def_merge_prop_impl              false
% 6.74/1.49  --prep_def_merge_mbd                    true
% 6.74/1.49  --prep_def_merge_tr_red                 false
% 6.74/1.49  --prep_def_merge_tr_cl                  false
% 6.74/1.49  --smt_preprocessing                     true
% 6.74/1.49  --smt_ac_axioms                         fast
% 6.74/1.49  --preprocessed_out                      false
% 6.74/1.49  --preprocessed_stats                    false
% 6.74/1.49  
% 6.74/1.49  ------ Abstraction refinement Options
% 6.74/1.49  
% 6.74/1.49  --abstr_ref                             []
% 6.74/1.49  --abstr_ref_prep                        false
% 6.74/1.49  --abstr_ref_until_sat                   false
% 6.74/1.49  --abstr_ref_sig_restrict                funpre
% 6.74/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.74/1.49  --abstr_ref_under                       []
% 6.74/1.49  
% 6.74/1.49  ------ SAT Options
% 6.74/1.49  
% 6.74/1.49  --sat_mode                              false
% 6.74/1.49  --sat_fm_restart_options                ""
% 6.74/1.49  --sat_gr_def                            false
% 6.74/1.49  --sat_epr_types                         true
% 6.74/1.49  --sat_non_cyclic_types                  false
% 6.74/1.49  --sat_finite_models                     false
% 6.74/1.49  --sat_fm_lemmas                         false
% 6.74/1.49  --sat_fm_prep                           false
% 6.74/1.49  --sat_fm_uc_incr                        true
% 6.74/1.49  --sat_out_model                         small
% 6.74/1.49  --sat_out_clauses                       false
% 6.74/1.49  
% 6.74/1.49  ------ QBF Options
% 6.74/1.49  
% 6.74/1.49  --qbf_mode                              false
% 6.74/1.49  --qbf_elim_univ                         false
% 6.74/1.49  --qbf_dom_inst                          none
% 6.74/1.49  --qbf_dom_pre_inst                      false
% 6.74/1.49  --qbf_sk_in                             false
% 6.74/1.49  --qbf_pred_elim                         true
% 6.74/1.49  --qbf_split                             512
% 6.74/1.49  
% 6.74/1.49  ------ BMC1 Options
% 6.74/1.49  
% 6.74/1.49  --bmc1_incremental                      false
% 6.74/1.49  --bmc1_axioms                           reachable_all
% 6.74/1.49  --bmc1_min_bound                        0
% 6.74/1.49  --bmc1_max_bound                        -1
% 6.74/1.49  --bmc1_max_bound_default                -1
% 6.74/1.49  --bmc1_symbol_reachability              true
% 6.74/1.49  --bmc1_property_lemmas                  false
% 6.74/1.49  --bmc1_k_induction                      false
% 6.74/1.49  --bmc1_non_equiv_states                 false
% 6.74/1.49  --bmc1_deadlock                         false
% 6.74/1.49  --bmc1_ucm                              false
% 6.74/1.49  --bmc1_add_unsat_core                   none
% 6.74/1.49  --bmc1_unsat_core_children              false
% 6.74/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.74/1.49  --bmc1_out_stat                         full
% 6.74/1.49  --bmc1_ground_init                      false
% 6.74/1.49  --bmc1_pre_inst_next_state              false
% 6.74/1.49  --bmc1_pre_inst_state                   false
% 6.74/1.49  --bmc1_pre_inst_reach_state             false
% 6.74/1.49  --bmc1_out_unsat_core                   false
% 6.74/1.49  --bmc1_aig_witness_out                  false
% 6.74/1.49  --bmc1_verbose                          false
% 6.74/1.49  --bmc1_dump_clauses_tptp                false
% 6.74/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.74/1.49  --bmc1_dump_file                        -
% 6.74/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.74/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.74/1.49  --bmc1_ucm_extend_mode                  1
% 6.74/1.49  --bmc1_ucm_init_mode                    2
% 6.74/1.49  --bmc1_ucm_cone_mode                    none
% 6.74/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.74/1.49  --bmc1_ucm_relax_model                  4
% 6.74/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.74/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.74/1.49  --bmc1_ucm_layered_model                none
% 6.74/1.49  --bmc1_ucm_max_lemma_size               10
% 6.74/1.49  
% 6.74/1.49  ------ AIG Options
% 6.74/1.49  
% 6.74/1.49  --aig_mode                              false
% 6.74/1.49  
% 6.74/1.49  ------ Instantiation Options
% 6.74/1.49  
% 6.74/1.49  --instantiation_flag                    true
% 6.74/1.49  --inst_sos_flag                         false
% 6.74/1.49  --inst_sos_phase                        true
% 6.74/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.74/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.74/1.49  --inst_lit_sel_side                     num_symb
% 6.74/1.49  --inst_solver_per_active                1400
% 6.74/1.49  --inst_solver_calls_frac                1.
% 6.74/1.49  --inst_passive_queue_type               priority_queues
% 6.74/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.74/1.49  --inst_passive_queues_freq              [25;2]
% 6.74/1.49  --inst_dismatching                      true
% 6.74/1.49  --inst_eager_unprocessed_to_passive     true
% 6.74/1.49  --inst_prop_sim_given                   true
% 6.74/1.49  --inst_prop_sim_new                     false
% 6.74/1.49  --inst_subs_new                         false
% 6.74/1.49  --inst_eq_res_simp                      false
% 6.74/1.49  --inst_subs_given                       false
% 6.74/1.49  --inst_orphan_elimination               true
% 6.74/1.49  --inst_learning_loop_flag               true
% 6.74/1.49  --inst_learning_start                   3000
% 6.74/1.49  --inst_learning_factor                  2
% 6.74/1.49  --inst_start_prop_sim_after_learn       3
% 6.74/1.49  --inst_sel_renew                        solver
% 6.74/1.49  --inst_lit_activity_flag                true
% 6.74/1.49  --inst_restr_to_given                   false
% 6.74/1.49  --inst_activity_threshold               500
% 6.74/1.49  --inst_out_proof                        true
% 6.74/1.49  
% 6.74/1.49  ------ Resolution Options
% 6.74/1.49  
% 6.74/1.49  --resolution_flag                       true
% 6.74/1.49  --res_lit_sel                           adaptive
% 6.74/1.49  --res_lit_sel_side                      none
% 6.74/1.49  --res_ordering                          kbo
% 6.74/1.49  --res_to_prop_solver                    active
% 6.74/1.49  --res_prop_simpl_new                    false
% 6.74/1.49  --res_prop_simpl_given                  true
% 6.74/1.49  --res_passive_queue_type                priority_queues
% 6.74/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.74/1.49  --res_passive_queues_freq               [15;5]
% 6.74/1.49  --res_forward_subs                      full
% 6.74/1.49  --res_backward_subs                     full
% 6.74/1.49  --res_forward_subs_resolution           true
% 6.74/1.49  --res_backward_subs_resolution          true
% 6.74/1.49  --res_orphan_elimination                true
% 6.74/1.49  --res_time_limit                        2.
% 6.74/1.49  --res_out_proof                         true
% 6.74/1.49  
% 6.74/1.49  ------ Superposition Options
% 6.74/1.49  
% 6.74/1.49  --superposition_flag                    true
% 6.74/1.49  --sup_passive_queue_type                priority_queues
% 6.74/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.74/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.74/1.49  --demod_completeness_check              fast
% 6.74/1.49  --demod_use_ground                      true
% 6.74/1.49  --sup_to_prop_solver                    passive
% 6.74/1.49  --sup_prop_simpl_new                    true
% 6.74/1.49  --sup_prop_simpl_given                  true
% 6.74/1.49  --sup_fun_splitting                     false
% 6.74/1.49  --sup_smt_interval                      50000
% 6.74/1.49  
% 6.74/1.49  ------ Superposition Simplification Setup
% 6.74/1.49  
% 6.74/1.49  --sup_indices_passive                   []
% 6.74/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.74/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.74/1.49  --sup_full_bw                           [BwDemod]
% 6.74/1.49  --sup_immed_triv                        [TrivRules]
% 6.74/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.74/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.74/1.49  --sup_immed_bw_main                     []
% 6.74/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.74/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.74/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.74/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.74/1.49  
% 6.74/1.49  ------ Combination Options
% 6.74/1.49  
% 6.74/1.49  --comb_res_mult                         3
% 6.74/1.49  --comb_sup_mult                         2
% 6.74/1.49  --comb_inst_mult                        10
% 6.74/1.49  
% 6.74/1.49  ------ Debug Options
% 6.74/1.49  
% 6.74/1.49  --dbg_backtrace                         false
% 6.74/1.49  --dbg_dump_prop_clauses                 false
% 6.74/1.49  --dbg_dump_prop_clauses_file            -
% 6.74/1.49  --dbg_out_stat                          false
% 6.74/1.49  ------ Parsing...
% 6.74/1.49  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 6.74/1.49  
% 6.74/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 6.74/1.49  
% 6.74/1.49  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 6.74/1.49  
% 6.74/1.49  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 6.74/1.49  ------ Proving...
% 6.74/1.49  ------ Problem Properties 
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  clauses                                 53
% 6.74/1.49  conjectures                             5
% 6.74/1.49  EPR                                     7
% 6.74/1.49  Horn                                    47
% 6.74/1.49  unary                                   19
% 6.74/1.49  binary                                  4
% 6.74/1.49  lits                                    162
% 6.74/1.49  lits eq                                 39
% 6.74/1.49  fd_pure                                 0
% 6.74/1.49  fd_pseudo                               0
% 6.74/1.49  fd_cond                                 3
% 6.74/1.49  fd_pseudo_cond                          5
% 6.74/1.49  AC symbols                              0
% 6.74/1.49  
% 6.74/1.49  ------ Schedule dynamic 5 is on 
% 6.74/1.49  
% 6.74/1.49  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  ------ 
% 6.74/1.49  Current options:
% 6.74/1.49  ------ 
% 6.74/1.49  
% 6.74/1.49  ------ Input Options
% 6.74/1.49  
% 6.74/1.49  --out_options                           all
% 6.74/1.49  --tptp_safe_out                         true
% 6.74/1.49  --problem_path                          ""
% 6.74/1.49  --include_path                          ""
% 6.74/1.49  --clausifier                            res/vclausify_rel
% 6.74/1.49  --clausifier_options                    --mode clausify
% 6.74/1.49  --stdin                                 false
% 6.74/1.49  --stats_out                             all
% 6.74/1.49  
% 6.74/1.49  ------ General Options
% 6.74/1.49  
% 6.74/1.49  --fof                                   false
% 6.74/1.49  --time_out_real                         305.
% 6.74/1.49  --time_out_virtual                      -1.
% 6.74/1.49  --symbol_type_check                     false
% 6.74/1.49  --clausify_out                          false
% 6.74/1.49  --sig_cnt_out                           false
% 6.74/1.49  --trig_cnt_out                          false
% 6.74/1.49  --trig_cnt_out_tolerance                1.
% 6.74/1.49  --trig_cnt_out_sk_spl                   false
% 6.74/1.49  --abstr_cl_out                          false
% 6.74/1.49  
% 6.74/1.49  ------ Global Options
% 6.74/1.49  
% 6.74/1.49  --schedule                              default
% 6.74/1.49  --add_important_lit                     false
% 6.74/1.49  --prop_solver_per_cl                    1000
% 6.74/1.49  --min_unsat_core                        false
% 6.74/1.49  --soft_assumptions                      false
% 6.74/1.49  --soft_lemma_size                       3
% 6.74/1.49  --prop_impl_unit_size                   0
% 6.74/1.49  --prop_impl_unit                        []
% 6.74/1.49  --share_sel_clauses                     true
% 6.74/1.49  --reset_solvers                         false
% 6.74/1.49  --bc_imp_inh                            [conj_cone]
% 6.74/1.49  --conj_cone_tolerance                   3.
% 6.74/1.49  --extra_neg_conj                        none
% 6.74/1.49  --large_theory_mode                     true
% 6.74/1.49  --prolific_symb_bound                   200
% 6.74/1.49  --lt_threshold                          2000
% 6.74/1.49  --clause_weak_htbl                      true
% 6.74/1.49  --gc_record_bc_elim                     false
% 6.74/1.49  
% 6.74/1.49  ------ Preprocessing Options
% 6.74/1.49  
% 6.74/1.49  --preprocessing_flag                    true
% 6.74/1.49  --time_out_prep_mult                    0.1
% 6.74/1.49  --splitting_mode                        input
% 6.74/1.49  --splitting_grd                         true
% 6.74/1.49  --splitting_cvd                         false
% 6.74/1.49  --splitting_cvd_svl                     false
% 6.74/1.49  --splitting_nvd                         32
% 6.74/1.49  --sub_typing                            true
% 6.74/1.49  --prep_gs_sim                           true
% 6.74/1.49  --prep_unflatten                        true
% 6.74/1.49  --prep_res_sim                          true
% 6.74/1.49  --prep_upred                            true
% 6.74/1.49  --prep_sem_filter                       exhaustive
% 6.74/1.49  --prep_sem_filter_out                   false
% 6.74/1.49  --pred_elim                             true
% 6.74/1.49  --res_sim_input                         true
% 6.74/1.49  --eq_ax_congr_red                       true
% 6.74/1.49  --pure_diseq_elim                       true
% 6.74/1.49  --brand_transform                       false
% 6.74/1.49  --non_eq_to_eq                          false
% 6.74/1.49  --prep_def_merge                        true
% 6.74/1.49  --prep_def_merge_prop_impl              false
% 6.74/1.49  --prep_def_merge_mbd                    true
% 6.74/1.49  --prep_def_merge_tr_red                 false
% 6.74/1.49  --prep_def_merge_tr_cl                  false
% 6.74/1.49  --smt_preprocessing                     true
% 6.74/1.49  --smt_ac_axioms                         fast
% 6.74/1.49  --preprocessed_out                      false
% 6.74/1.49  --preprocessed_stats                    false
% 6.74/1.49  
% 6.74/1.49  ------ Abstraction refinement Options
% 6.74/1.49  
% 6.74/1.49  --abstr_ref                             []
% 6.74/1.49  --abstr_ref_prep                        false
% 6.74/1.49  --abstr_ref_until_sat                   false
% 6.74/1.49  --abstr_ref_sig_restrict                funpre
% 6.74/1.49  --abstr_ref_af_restrict_to_split_sk     false
% 6.74/1.49  --abstr_ref_under                       []
% 6.74/1.49  
% 6.74/1.49  ------ SAT Options
% 6.74/1.49  
% 6.74/1.49  --sat_mode                              false
% 6.74/1.49  --sat_fm_restart_options                ""
% 6.74/1.49  --sat_gr_def                            false
% 6.74/1.49  --sat_epr_types                         true
% 6.74/1.49  --sat_non_cyclic_types                  false
% 6.74/1.49  --sat_finite_models                     false
% 6.74/1.49  --sat_fm_lemmas                         false
% 6.74/1.49  --sat_fm_prep                           false
% 6.74/1.49  --sat_fm_uc_incr                        true
% 6.74/1.49  --sat_out_model                         small
% 6.74/1.49  --sat_out_clauses                       false
% 6.74/1.49  
% 6.74/1.49  ------ QBF Options
% 6.74/1.49  
% 6.74/1.49  --qbf_mode                              false
% 6.74/1.49  --qbf_elim_univ                         false
% 6.74/1.49  --qbf_dom_inst                          none
% 6.74/1.49  --qbf_dom_pre_inst                      false
% 6.74/1.49  --qbf_sk_in                             false
% 6.74/1.49  --qbf_pred_elim                         true
% 6.74/1.49  --qbf_split                             512
% 6.74/1.49  
% 6.74/1.49  ------ BMC1 Options
% 6.74/1.49  
% 6.74/1.49  --bmc1_incremental                      false
% 6.74/1.49  --bmc1_axioms                           reachable_all
% 6.74/1.49  --bmc1_min_bound                        0
% 6.74/1.49  --bmc1_max_bound                        -1
% 6.74/1.49  --bmc1_max_bound_default                -1
% 6.74/1.49  --bmc1_symbol_reachability              true
% 6.74/1.49  --bmc1_property_lemmas                  false
% 6.74/1.49  --bmc1_k_induction                      false
% 6.74/1.49  --bmc1_non_equiv_states                 false
% 6.74/1.49  --bmc1_deadlock                         false
% 6.74/1.49  --bmc1_ucm                              false
% 6.74/1.49  --bmc1_add_unsat_core                   none
% 6.74/1.49  --bmc1_unsat_core_children              false
% 6.74/1.49  --bmc1_unsat_core_extrapolate_axioms    false
% 6.74/1.49  --bmc1_out_stat                         full
% 6.74/1.49  --bmc1_ground_init                      false
% 6.74/1.49  --bmc1_pre_inst_next_state              false
% 6.74/1.49  --bmc1_pre_inst_state                   false
% 6.74/1.49  --bmc1_pre_inst_reach_state             false
% 6.74/1.49  --bmc1_out_unsat_core                   false
% 6.74/1.49  --bmc1_aig_witness_out                  false
% 6.74/1.49  --bmc1_verbose                          false
% 6.74/1.49  --bmc1_dump_clauses_tptp                false
% 6.74/1.49  --bmc1_dump_unsat_core_tptp             false
% 6.74/1.49  --bmc1_dump_file                        -
% 6.74/1.49  --bmc1_ucm_expand_uc_limit              128
% 6.74/1.49  --bmc1_ucm_n_expand_iterations          6
% 6.74/1.49  --bmc1_ucm_extend_mode                  1
% 6.74/1.49  --bmc1_ucm_init_mode                    2
% 6.74/1.49  --bmc1_ucm_cone_mode                    none
% 6.74/1.49  --bmc1_ucm_reduced_relation_type        0
% 6.74/1.49  --bmc1_ucm_relax_model                  4
% 6.74/1.49  --bmc1_ucm_full_tr_after_sat            true
% 6.74/1.49  --bmc1_ucm_expand_neg_assumptions       false
% 6.74/1.49  --bmc1_ucm_layered_model                none
% 6.74/1.49  --bmc1_ucm_max_lemma_size               10
% 6.74/1.49  
% 6.74/1.49  ------ AIG Options
% 6.74/1.49  
% 6.74/1.49  --aig_mode                              false
% 6.74/1.49  
% 6.74/1.49  ------ Instantiation Options
% 6.74/1.49  
% 6.74/1.49  --instantiation_flag                    true
% 6.74/1.49  --inst_sos_flag                         false
% 6.74/1.49  --inst_sos_phase                        true
% 6.74/1.49  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 6.74/1.49  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 6.74/1.49  --inst_lit_sel_side                     none
% 6.74/1.49  --inst_solver_per_active                1400
% 6.74/1.49  --inst_solver_calls_frac                1.
% 6.74/1.49  --inst_passive_queue_type               priority_queues
% 6.74/1.49  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 6.74/1.49  --inst_passive_queues_freq              [25;2]
% 6.74/1.49  --inst_dismatching                      true
% 6.74/1.49  --inst_eager_unprocessed_to_passive     true
% 6.74/1.49  --inst_prop_sim_given                   true
% 6.74/1.49  --inst_prop_sim_new                     false
% 6.74/1.49  --inst_subs_new                         false
% 6.74/1.49  --inst_eq_res_simp                      false
% 6.74/1.49  --inst_subs_given                       false
% 6.74/1.49  --inst_orphan_elimination               true
% 6.74/1.49  --inst_learning_loop_flag               true
% 6.74/1.49  --inst_learning_start                   3000
% 6.74/1.49  --inst_learning_factor                  2
% 6.74/1.49  --inst_start_prop_sim_after_learn       3
% 6.74/1.49  --inst_sel_renew                        solver
% 6.74/1.49  --inst_lit_activity_flag                true
% 6.74/1.49  --inst_restr_to_given                   false
% 6.74/1.49  --inst_activity_threshold               500
% 6.74/1.49  --inst_out_proof                        true
% 6.74/1.49  
% 6.74/1.49  ------ Resolution Options
% 6.74/1.49  
% 6.74/1.49  --resolution_flag                       false
% 6.74/1.49  --res_lit_sel                           adaptive
% 6.74/1.49  --res_lit_sel_side                      none
% 6.74/1.49  --res_ordering                          kbo
% 6.74/1.49  --res_to_prop_solver                    active
% 6.74/1.49  --res_prop_simpl_new                    false
% 6.74/1.49  --res_prop_simpl_given                  true
% 6.74/1.49  --res_passive_queue_type                priority_queues
% 6.74/1.49  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 6.74/1.49  --res_passive_queues_freq               [15;5]
% 6.74/1.49  --res_forward_subs                      full
% 6.74/1.49  --res_backward_subs                     full
% 6.74/1.49  --res_forward_subs_resolution           true
% 6.74/1.49  --res_backward_subs_resolution          true
% 6.74/1.49  --res_orphan_elimination                true
% 6.74/1.49  --res_time_limit                        2.
% 6.74/1.49  --res_out_proof                         true
% 6.74/1.49  
% 6.74/1.49  ------ Superposition Options
% 6.74/1.49  
% 6.74/1.49  --superposition_flag                    true
% 6.74/1.49  --sup_passive_queue_type                priority_queues
% 6.74/1.49  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 6.74/1.49  --sup_passive_queues_freq               [8;1;4]
% 6.74/1.49  --demod_completeness_check              fast
% 6.74/1.49  --demod_use_ground                      true
% 6.74/1.49  --sup_to_prop_solver                    passive
% 6.74/1.49  --sup_prop_simpl_new                    true
% 6.74/1.49  --sup_prop_simpl_given                  true
% 6.74/1.49  --sup_fun_splitting                     false
% 6.74/1.49  --sup_smt_interval                      50000
% 6.74/1.49  
% 6.74/1.49  ------ Superposition Simplification Setup
% 6.74/1.49  
% 6.74/1.49  --sup_indices_passive                   []
% 6.74/1.49  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.49  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.49  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 6.74/1.49  --sup_full_triv                         [TrivRules;PropSubs]
% 6.74/1.49  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.74/1.49  --sup_full_bw                           [BwDemod]
% 6.74/1.49  --sup_immed_triv                        [TrivRules]
% 6.74/1.49  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 6.74/1.49  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.74/1.49  --sup_immed_bw_main                     []
% 6.74/1.49  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.74/1.49  --sup_input_triv                        [Unflattening;TrivRules]
% 6.74/1.49  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 6.74/1.49  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 6.74/1.49  
% 6.74/1.49  ------ Combination Options
% 6.74/1.49  
% 6.74/1.49  --comb_res_mult                         3
% 6.74/1.49  --comb_sup_mult                         2
% 6.74/1.49  --comb_inst_mult                        10
% 6.74/1.49  
% 6.74/1.49  ------ Debug Options
% 6.74/1.49  
% 6.74/1.49  --dbg_backtrace                         false
% 6.74/1.49  --dbg_dump_prop_clauses                 false
% 6.74/1.49  --dbg_dump_prop_clauses_file            -
% 6.74/1.49  --dbg_out_stat                          false
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  ------ Proving...
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  % SZS status Theorem for theBenchmark.p
% 6.74/1.49  
% 6.74/1.49  % SZS output start CNFRefutation for theBenchmark.p
% 6.74/1.49  
% 6.74/1.49  fof(f34,conjecture,(
% 6.74/1.49    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f35,negated_conjecture,(
% 6.74/1.49    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 6.74/1.49    inference(negated_conjecture,[],[f34])).
% 6.74/1.49  
% 6.74/1.49  fof(f80,plain,(
% 6.74/1.49    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 6.74/1.49    inference(ennf_transformation,[],[f35])).
% 6.74/1.49  
% 6.74/1.49  fof(f81,plain,(
% 6.74/1.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 6.74/1.49    inference(flattening,[],[f80])).
% 6.74/1.49  
% 6.74/1.49  fof(f92,plain,(
% 6.74/1.49    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK3)),sK3) & v2_funct_1(sK3) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK3) = k2_struct_0(X1) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK3,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK3))) )),
% 6.74/1.49    introduced(choice_axiom,[])).
% 6.74/1.49  
% 6.74/1.49  fof(f91,plain,(
% 6.74/1.49    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK2),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK2),X2) = k2_struct_0(sK2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK2)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK2)) & v1_funct_1(X2)) & l1_struct_0(sK2) & ~v2_struct_0(sK2))) )),
% 6.74/1.49    introduced(choice_axiom,[])).
% 6.74/1.49  
% 6.74/1.49  fof(f90,plain,(
% 6.74/1.49    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK1),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK1))),
% 6.74/1.49    introduced(choice_axiom,[])).
% 6.74/1.49  
% 6.74/1.49  fof(f93,plain,(
% 6.74/1.49    ((~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) & v2_funct_1(sK3) & k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) & v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) & v1_funct_1(sK3)) & l1_struct_0(sK2) & ~v2_struct_0(sK2)) & l1_struct_0(sK1)),
% 6.74/1.49    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f81,f92,f91,f90])).
% 6.74/1.49  
% 6.74/1.49  fof(f157,plain,(
% 6.74/1.49    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))),
% 6.74/1.49    inference(cnf_transformation,[],[f93])).
% 6.74/1.49  
% 6.74/1.49  fof(f31,axiom,(
% 6.74/1.49    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f75,plain,(
% 6.74/1.49    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 6.74/1.49    inference(ennf_transformation,[],[f31])).
% 6.74/1.49  
% 6.74/1.49  fof(f149,plain,(
% 6.74/1.49    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f75])).
% 6.74/1.49  
% 6.74/1.49  fof(f154,plain,(
% 6.74/1.49    l1_struct_0(sK2)),
% 6.74/1.49    inference(cnf_transformation,[],[f93])).
% 6.74/1.49  
% 6.74/1.49  fof(f152,plain,(
% 6.74/1.49    l1_struct_0(sK1)),
% 6.74/1.49    inference(cnf_transformation,[],[f93])).
% 6.74/1.49  
% 6.74/1.49  fof(f21,axiom,(
% 6.74/1.49    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f59,plain,(
% 6.74/1.49    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 6.74/1.49    inference(ennf_transformation,[],[f21])).
% 6.74/1.49  
% 6.74/1.49  fof(f60,plain,(
% 6.74/1.49    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 6.74/1.49    inference(flattening,[],[f59])).
% 6.74/1.49  
% 6.74/1.49  fof(f126,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f60])).
% 6.74/1.49  
% 6.74/1.49  fof(f23,axiom,(
% 6.74/1.49    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f63,plain,(
% 6.74/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 6.74/1.49    inference(ennf_transformation,[],[f23])).
% 6.74/1.49  
% 6.74/1.49  fof(f64,plain,(
% 6.74/1.49    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.74/1.49    inference(flattening,[],[f63])).
% 6.74/1.49  
% 6.74/1.49  fof(f87,plain,(
% 6.74/1.49    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 6.74/1.49    inference(nnf_transformation,[],[f64])).
% 6.74/1.49  
% 6.74/1.49  fof(f130,plain,(
% 6.74/1.49    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f87])).
% 6.74/1.49  
% 6.74/1.49  fof(f19,axiom,(
% 6.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f37,plain,(
% 6.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 6.74/1.49    inference(pure_predicate_removal,[],[f19])).
% 6.74/1.49  
% 6.74/1.49  fof(f57,plain,(
% 6.74/1.49    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.74/1.49    inference(ennf_transformation,[],[f37])).
% 6.74/1.49  
% 6.74/1.49  fof(f123,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.74/1.49    inference(cnf_transformation,[],[f57])).
% 6.74/1.49  
% 6.74/1.49  fof(f18,axiom,(
% 6.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f56,plain,(
% 6.74/1.49    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.74/1.49    inference(ennf_transformation,[],[f18])).
% 6.74/1.49  
% 6.74/1.49  fof(f122,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.74/1.49    inference(cnf_transformation,[],[f56])).
% 6.74/1.49  
% 6.74/1.49  fof(f155,plain,(
% 6.74/1.49    v1_funct_1(sK3)),
% 6.74/1.49    inference(cnf_transformation,[],[f93])).
% 6.74/1.49  
% 6.74/1.49  fof(f32,axiom,(
% 6.74/1.49    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f76,plain,(
% 6.74/1.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 6.74/1.49    inference(ennf_transformation,[],[f32])).
% 6.74/1.49  
% 6.74/1.49  fof(f77,plain,(
% 6.74/1.49    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 6.74/1.49    inference(flattening,[],[f76])).
% 6.74/1.49  
% 6.74/1.49  fof(f150,plain,(
% 6.74/1.49    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f77])).
% 6.74/1.49  
% 6.74/1.49  fof(f153,plain,(
% 6.74/1.49    ~v2_struct_0(sK2)),
% 6.74/1.49    inference(cnf_transformation,[],[f93])).
% 6.74/1.49  
% 6.74/1.49  fof(f156,plain,(
% 6.74/1.49    v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))),
% 6.74/1.49    inference(cnf_transformation,[],[f93])).
% 6.74/1.49  
% 6.74/1.49  fof(f20,axiom,(
% 6.74/1.49    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f58,plain,(
% 6.74/1.49    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 6.74/1.49    inference(ennf_transformation,[],[f20])).
% 6.74/1.49  
% 6.74/1.49  fof(f124,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 6.74/1.49    inference(cnf_transformation,[],[f58])).
% 6.74/1.49  
% 6.74/1.49  fof(f158,plain,(
% 6.74/1.49    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2)),
% 6.74/1.49    inference(cnf_transformation,[],[f93])).
% 6.74/1.49  
% 6.74/1.49  fof(f29,axiom,(
% 6.74/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f71,plain,(
% 6.74/1.49    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.74/1.49    inference(ennf_transformation,[],[f29])).
% 6.74/1.49  
% 6.74/1.49  fof(f72,plain,(
% 6.74/1.49    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.74/1.49    inference(flattening,[],[f71])).
% 6.74/1.49  
% 6.74/1.49  fof(f145,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f72])).
% 6.74/1.49  
% 6.74/1.49  fof(f159,plain,(
% 6.74/1.49    v2_funct_1(sK3)),
% 6.74/1.49    inference(cnf_transformation,[],[f93])).
% 6.74/1.49  
% 6.74/1.49  fof(f1,axiom,(
% 6.74/1.49    v1_xboole_0(k1_xboole_0)),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f94,plain,(
% 6.74/1.49    v1_xboole_0(k1_xboole_0)),
% 6.74/1.49    inference(cnf_transformation,[],[f1])).
% 6.74/1.49  
% 6.74/1.49  fof(f30,axiom,(
% 6.74/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f73,plain,(
% 6.74/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.74/1.49    inference(ennf_transformation,[],[f30])).
% 6.74/1.49  
% 6.74/1.49  fof(f74,plain,(
% 6.74/1.49    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.74/1.49    inference(flattening,[],[f73])).
% 6.74/1.49  
% 6.74/1.49  fof(f148,plain,(
% 6.74/1.49    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f74])).
% 6.74/1.49  
% 6.74/1.49  fof(f147,plain,(
% 6.74/1.49    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f74])).
% 6.74/1.49  
% 6.74/1.49  fof(f17,axiom,(
% 6.74/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,X1) & k1_relat_1(X1) = k2_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f54,plain,(
% 6.74/1.49    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.74/1.49    inference(ennf_transformation,[],[f17])).
% 6.74/1.49  
% 6.74/1.49  fof(f55,plain,(
% 6.74/1.49    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.74/1.49    inference(flattening,[],[f54])).
% 6.74/1.49  
% 6.74/1.49  fof(f121,plain,(
% 6.74/1.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k1_relat_1(X0)) != k5_relat_1(X0,X1) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f55])).
% 6.74/1.49  
% 6.74/1.49  fof(f25,axiom,(
% 6.74/1.49    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f137,plain,(
% 6.74/1.49    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f25])).
% 6.74/1.49  
% 6.74/1.49  fof(f163,plain,(
% 6.74/1.49    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0)) | k1_relat_1(X1) != k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.74/1.49    inference(definition_unfolding,[],[f121,f137])).
% 6.74/1.49  
% 6.74/1.49  fof(f16,axiom,(
% 6.74/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f52,plain,(
% 6.74/1.49    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.74/1.49    inference(ennf_transformation,[],[f16])).
% 6.74/1.49  
% 6.74/1.49  fof(f53,plain,(
% 6.74/1.49    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.74/1.49    inference(flattening,[],[f52])).
% 6.74/1.49  
% 6.74/1.49  fof(f119,plain,(
% 6.74/1.49    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f53])).
% 6.74/1.49  
% 6.74/1.49  fof(f120,plain,(
% 6.74/1.49    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f53])).
% 6.74/1.49  
% 6.74/1.49  fof(f28,axiom,(
% 6.74/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f69,plain,(
% 6.74/1.49    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.74/1.49    inference(ennf_transformation,[],[f28])).
% 6.74/1.49  
% 6.74/1.49  fof(f70,plain,(
% 6.74/1.49    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.74/1.49    inference(flattening,[],[f69])).
% 6.74/1.49  
% 6.74/1.49  fof(f143,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f70])).
% 6.74/1.49  
% 6.74/1.49  fof(f33,axiom,(
% 6.74/1.49    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f78,plain,(
% 6.74/1.49    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.74/1.49    inference(ennf_transformation,[],[f33])).
% 6.74/1.49  
% 6.74/1.49  fof(f79,plain,(
% 6.74/1.49    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.74/1.49    inference(flattening,[],[f78])).
% 6.74/1.49  
% 6.74/1.49  fof(f151,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f79])).
% 6.74/1.49  
% 6.74/1.49  fof(f13,axiom,(
% 6.74/1.49    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f46,plain,(
% 6.74/1.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.74/1.49    inference(ennf_transformation,[],[f13])).
% 6.74/1.49  
% 6.74/1.49  fof(f47,plain,(
% 6.74/1.49    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.74/1.49    inference(flattening,[],[f46])).
% 6.74/1.49  
% 6.74/1.49  fof(f115,plain,(
% 6.74/1.49    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f47])).
% 6.74/1.49  
% 6.74/1.49  fof(f141,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f70])).
% 6.74/1.49  
% 6.74/1.49  fof(f11,axiom,(
% 6.74/1.49    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f44,plain,(
% 6.74/1.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 6.74/1.49    inference(ennf_transformation,[],[f11])).
% 6.74/1.49  
% 6.74/1.49  fof(f45,plain,(
% 6.74/1.49    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 6.74/1.49    inference(flattening,[],[f44])).
% 6.74/1.49  
% 6.74/1.49  fof(f110,plain,(
% 6.74/1.49    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f45])).
% 6.74/1.49  
% 6.74/1.49  fof(f142,plain,(
% 6.74/1.49    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f70])).
% 6.74/1.49  
% 6.74/1.49  fof(f26,axiom,(
% 6.74/1.49    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 6.74/1.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 6.74/1.49  
% 6.74/1.49  fof(f65,plain,(
% 6.74/1.49    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 6.74/1.49    inference(ennf_transformation,[],[f26])).
% 6.74/1.49  
% 6.74/1.49  fof(f66,plain,(
% 6.74/1.49    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 6.74/1.49    inference(flattening,[],[f65])).
% 6.74/1.49  
% 6.74/1.49  fof(f138,plain,(
% 6.74/1.49    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f66])).
% 6.74/1.49  
% 6.74/1.49  fof(f160,plain,(
% 6.74/1.49    ~r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3)),
% 6.74/1.49    inference(cnf_transformation,[],[f93])).
% 6.74/1.49  
% 6.74/1.49  fof(f109,plain,(
% 6.74/1.49    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 6.74/1.49    inference(cnf_transformation,[],[f45])).
% 6.74/1.49  
% 6.74/1.49  cnf(c_60,negated_conjecture,
% 6.74/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) ),
% 6.74/1.49      inference(cnf_transformation,[],[f157]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2015,plain,
% 6.74/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_54,plain,
% 6.74/1.49      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f149]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_63,negated_conjecture,
% 6.74/1.49      ( l1_struct_0(sK2) ),
% 6.74/1.49      inference(cnf_transformation,[],[f154]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_681,plain,
% 6.74/1.49      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 6.74/1.49      inference(resolution_lifted,[status(thm)],[c_54,c_63]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_682,plain,
% 6.74/1.49      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 6.74/1.49      inference(unflattening,[status(thm)],[c_681]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_65,negated_conjecture,
% 6.74/1.49      ( l1_struct_0(sK1) ),
% 6.74/1.49      inference(cnf_transformation,[],[f152]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_686,plain,
% 6.74/1.49      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 6.74/1.49      inference(resolution_lifted,[status(thm)],[c_54,c_65]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_687,plain,
% 6.74/1.49      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 6.74/1.49      inference(unflattening,[status(thm)],[c_686]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2089,plain,
% 6.74/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) = iProver_top ),
% 6.74/1.49      inference(light_normalisation,[status(thm)],[c_2015,c_682,c_687]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_31,plain,
% 6.74/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.74/1.49      | v1_partfun1(X0,X1)
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | v1_xboole_0(X2) ),
% 6.74/1.49      inference(cnf_transformation,[],[f126]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_37,plain,
% 6.74/1.49      ( ~ v1_partfun1(X0,X1)
% 6.74/1.49      | ~ v4_relat_1(X0,X1)
% 6.74/1.49      | ~ v1_relat_1(X0)
% 6.74/1.49      | k1_relat_1(X0) = X1 ),
% 6.74/1.49      inference(cnf_transformation,[],[f130]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_836,plain,
% 6.74/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.74/1.49      | ~ v4_relat_1(X0,X1)
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | ~ v1_relat_1(X0)
% 6.74/1.49      | v1_xboole_0(X2)
% 6.74/1.49      | k1_relat_1(X0) = X1 ),
% 6.74/1.49      inference(resolution,[status(thm)],[c_31,c_37]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_29,plain,
% 6.74/1.49      ( v4_relat_1(X0,X1)
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.74/1.49      inference(cnf_transformation,[],[f123]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_28,plain,
% 6.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | v1_relat_1(X0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f122]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_838,plain,
% 6.74/1.49      ( ~ v1_funct_1(X0)
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | ~ v1_funct_2(X0,X1,X2)
% 6.74/1.49      | v1_xboole_0(X2)
% 6.74/1.49      | k1_relat_1(X0) = X1 ),
% 6.74/1.49      inference(global_propositional_subsumption,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_836,c_29,c_28]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_839,plain,
% 6.74/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | v1_xboole_0(X2)
% 6.74/1.49      | k1_relat_1(X0) = X1 ),
% 6.74/1.49      inference(renaming,[status(thm)],[c_838]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2006,plain,
% 6.74/1.49      ( k1_relat_1(X0) = X1
% 6.74/1.49      | v1_funct_2(X0,X1,X2) != iProver_top
% 6.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 6.74/1.49      | v1_funct_1(X0) != iProver_top
% 6.74/1.49      | v1_xboole_0(X2) = iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_839]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2618,plain,
% 6.74/1.49      ( k2_struct_0(sK1) = k1_relat_1(sK3)
% 6.74/1.49      | v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_2089,c_2006]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_62,negated_conjecture,
% 6.74/1.49      ( v1_funct_1(sK3) ),
% 6.74/1.49      inference(cnf_transformation,[],[f155]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_69,plain,
% 6.74/1.49      ( v1_funct_1(sK3) = iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_55,plain,
% 6.74/1.49      ( v2_struct_0(X0)
% 6.74/1.49      | ~ l1_struct_0(X0)
% 6.74/1.49      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 6.74/1.49      inference(cnf_transformation,[],[f150]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_64,negated_conjecture,
% 6.74/1.49      ( ~ v2_struct_0(sK2) ),
% 6.74/1.49      inference(cnf_transformation,[],[f153]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_668,plain,
% 6.74/1.49      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK2 != X0 ),
% 6.74/1.49      inference(resolution_lifted,[status(thm)],[c_55,c_64]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_669,plain,
% 6.74/1.49      ( ~ l1_struct_0(sK2) | ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 6.74/1.49      inference(unflattening,[status(thm)],[c_668]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_671,plain,
% 6.74/1.49      ( ~ v1_xboole_0(u1_struct_0(sK2)) ),
% 6.74/1.49      inference(global_propositional_subsumption,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_669,c_63]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2010,plain,
% 6.74/1.49      ( v1_xboole_0(u1_struct_0(sK2)) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2072,plain,
% 6.74/1.49      ( v1_xboole_0(k2_struct_0(sK2)) != iProver_top ),
% 6.74/1.49      inference(light_normalisation,[status(thm)],[c_2010,c_682]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_61,negated_conjecture,
% 6.74/1.49      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) ),
% 6.74/1.49      inference(cnf_transformation,[],[f156]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2014,plain,
% 6.74/1.49      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2081,plain,
% 6.74/1.49      ( v1_funct_2(sK3,k2_struct_0(sK1),k2_struct_0(sK2)) = iProver_top ),
% 6.74/1.49      inference(light_normalisation,[status(thm)],[c_2014,c_682,c_687]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3076,plain,
% 6.74/1.49      ( k2_struct_0(sK1) = k1_relat_1(sK3) ),
% 6.74/1.49      inference(global_propositional_subsumption,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_2618,c_69,c_2072,c_2081]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3081,plain,
% 6.74/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_struct_0(sK2)))) = iProver_top ),
% 6.74/1.49      inference(demodulation,[status(thm)],[c_3076,c_2089]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_30,plain,
% 6.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f124]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2028,plain,
% 6.74/1.49      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 6.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_5228,plain,
% 6.74/1.49      ( k2_relset_1(k1_relat_1(sK3),k2_struct_0(sK2),sK3) = k2_relat_1(sK3) ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_3081,c_2028]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_59,negated_conjecture,
% 6.74/1.49      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
% 6.74/1.49      inference(cnf_transformation,[],[f158]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2086,plain,
% 6.74/1.49      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
% 6.74/1.49      inference(light_normalisation,[status(thm)],[c_59,c_682,c_687]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3083,plain,
% 6.74/1.49      ( k2_relset_1(k1_relat_1(sK3),k2_struct_0(sK2),sK3) = k2_struct_0(sK2) ),
% 6.74/1.49      inference(demodulation,[status(thm)],[c_3076,c_2086]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_5470,plain,
% 6.74/1.49      ( k2_struct_0(sK2) = k2_relat_1(sK3) ),
% 6.74/1.49      inference(demodulation,[status(thm)],[c_5228,c_3083]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_5473,plain,
% 6.74/1.49      ( k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) = k2_relat_1(sK3) ),
% 6.74/1.49      inference(demodulation,[status(thm)],[c_5470,c_5228]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_49,plain,
% 6.74/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | ~ v2_funct_1(X0)
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | k2_relset_1(X1,X2,X0) != X2
% 6.74/1.49      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 6.74/1.49      | k1_xboole_0 = X2 ),
% 6.74/1.49      inference(cnf_transformation,[],[f145]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2021,plain,
% 6.74/1.49      ( k2_relset_1(X0,X1,X2) != X1
% 6.74/1.49      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
% 6.74/1.49      | k1_xboole_0 = X1
% 6.74/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.74/1.49      | v2_funct_1(X2) != iProver_top
% 6.74/1.49      | v1_funct_1(X2) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_9217,plain,
% 6.74/1.49      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3))
% 6.74/1.49      | k2_relat_1(sK3) = k1_xboole_0
% 6.74/1.49      | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
% 6.74/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
% 6.74/1.49      | v2_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_5473,c_2021]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_71,plain,
% 6.74/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) = iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_58,negated_conjecture,
% 6.74/1.49      ( v2_funct_1(sK3) ),
% 6.74/1.49      inference(cnf_transformation,[],[f159]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_72,plain,
% 6.74/1.49      ( v2_funct_1(sK3) = iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_0,plain,
% 6.74/1.49      ( v1_xboole_0(k1_xboole_0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f94]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2536,plain,
% 6.74/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 6.74/1.49      | v1_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_28]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2537,plain,
% 6.74/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 6.74/1.49      | v1_relat_1(sK3) = iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_2536]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_51,plain,
% 6.74/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | ~ v1_relat_1(X0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f148]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2895,plain,
% 6.74/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
% 6.74/1.49      | ~ v1_funct_1(sK3)
% 6.74/1.49      | ~ v1_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_51]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2911,plain,
% 6.74/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_relat_1(sK3) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_2895]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_52,plain,
% 6.74/1.49      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | ~ v1_relat_1(X0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f147]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2894,plain,
% 6.74/1.49      ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
% 6.74/1.49      | ~ v1_funct_1(sK3)
% 6.74/1.49      | ~ v1_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_52]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2913,plain,
% 6.74/1.49      ( v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) = iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_relat_1(sK3) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_2894]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_5477,plain,
% 6.74/1.49      ( v1_xboole_0(k2_relat_1(sK3)) != iProver_top ),
% 6.74/1.49      inference(demodulation,[status(thm)],[c_5470,c_2072]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_5493,plain,
% 6.74/1.49      ( ~ v1_xboole_0(k2_relat_1(sK3)) ),
% 6.74/1.49      inference(predicate_to_equality_rev,[status(thm)],[c_5477]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_1208,plain,
% 6.74/1.49      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 6.74/1.49      theory(equality) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_5750,plain,
% 6.74/1.49      ( ~ v1_xboole_0(X0)
% 6.74/1.49      | v1_xboole_0(k2_relat_1(sK3))
% 6.74/1.49      | k2_relat_1(sK3) != X0 ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_1208]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_5755,plain,
% 6.74/1.49      ( v1_xboole_0(k2_relat_1(sK3))
% 6.74/1.49      | ~ v1_xboole_0(k1_xboole_0)
% 6.74/1.49      | k2_relat_1(sK3) != k1_xboole_0 ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_5750]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_23586,plain,
% 6.74/1.49      ( k5_relat_1(k2_funct_1(sK3),sK3) = k6_partfun1(k2_relat_1(sK3)) ),
% 6.74/1.49      inference(global_propositional_subsumption,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_9217,c_69,c_71,c_72,c_0,c_2537,c_2911,c_2913,c_5493,
% 6.74/1.49                 c_5755]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_27,plain,
% 6.74/1.49      ( ~ v2_funct_1(X0)
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | ~ v1_funct_1(X1)
% 6.74/1.49      | ~ v1_relat_1(X0)
% 6.74/1.49      | ~ v1_relat_1(X1)
% 6.74/1.49      | k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 6.74/1.49      | k2_funct_1(X0) = X1
% 6.74/1.49      | k2_relat_1(X0) != k1_relat_1(X1) ),
% 6.74/1.49      inference(cnf_transformation,[],[f163]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2030,plain,
% 6.74/1.49      ( k5_relat_1(X0,X1) != k6_partfun1(k1_relat_1(X0))
% 6.74/1.49      | k2_funct_1(X0) = X1
% 6.74/1.49      | k2_relat_1(X0) != k1_relat_1(X1)
% 6.74/1.49      | v2_funct_1(X0) != iProver_top
% 6.74/1.49      | v1_funct_1(X0) != iProver_top
% 6.74/1.49      | v1_funct_1(X1) != iProver_top
% 6.74/1.49      | v1_relat_1(X0) != iProver_top
% 6.74/1.49      | v1_relat_1(X1) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_23589,plain,
% 6.74/1.49      ( k6_partfun1(k1_relat_1(k2_funct_1(sK3))) != k6_partfun1(k2_relat_1(sK3))
% 6.74/1.49      | k2_funct_1(k2_funct_1(sK3)) = sK3
% 6.74/1.49      | k2_relat_1(k2_funct_1(sK3)) != k1_relat_1(sK3)
% 6.74/1.49      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_relat_1(sK3) != iProver_top ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_23586,c_2030]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2016,plain,
% 6.74/1.49      ( v2_funct_1(sK3) = iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_26,plain,
% 6.74/1.49      ( ~ v2_funct_1(X0)
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | ~ v1_relat_1(X0)
% 6.74/1.49      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f119]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2031,plain,
% 6.74/1.49      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 6.74/1.49      | v2_funct_1(X0) != iProver_top
% 6.74/1.49      | v1_funct_1(X0) != iProver_top
% 6.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_6973,plain,
% 6.74/1.49      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3)
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_relat_1(sK3) != iProver_top ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_2016,c_2031]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2575,plain,
% 6.74/1.49      ( ~ v2_funct_1(sK3)
% 6.74/1.49      | ~ v1_funct_1(sK3)
% 6.74/1.49      | ~ v1_relat_1(sK3)
% 6.74/1.49      | k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_26]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_7437,plain,
% 6.74/1.49      ( k1_relat_1(k2_funct_1(sK3)) = k2_relat_1(sK3) ),
% 6.74/1.49      inference(global_propositional_subsumption,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_6973,c_62,c_60,c_58,c_2536,c_2575]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_25,plain,
% 6.74/1.49      ( ~ v2_funct_1(X0)
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | ~ v1_relat_1(X0)
% 6.74/1.49      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f120]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2032,plain,
% 6.74/1.49      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 6.74/1.49      | v2_funct_1(X0) != iProver_top
% 6.74/1.49      | v1_funct_1(X0) != iProver_top
% 6.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_7104,plain,
% 6.74/1.49      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3)
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_relat_1(sK3) != iProver_top ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_2016,c_2032]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2567,plain,
% 6.74/1.49      ( ~ v2_funct_1(sK3)
% 6.74/1.49      | ~ v1_funct_1(sK3)
% 6.74/1.49      | ~ v1_relat_1(sK3)
% 6.74/1.49      | k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_25]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_7465,plain,
% 6.74/1.49      ( k2_relat_1(k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 6.74/1.49      inference(global_propositional_subsumption,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_7104,c_62,c_60,c_58,c_2536,c_2567]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_23590,plain,
% 6.74/1.49      ( k6_partfun1(k2_relat_1(sK3)) != k6_partfun1(k2_relat_1(sK3))
% 6.74/1.49      | k2_funct_1(k2_funct_1(sK3)) = sK3
% 6.74/1.49      | k1_relat_1(sK3) != k1_relat_1(sK3)
% 6.74/1.49      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_relat_1(sK3) != iProver_top ),
% 6.74/1.49      inference(light_normalisation,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_23589,c_7437,c_7465]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_23591,plain,
% 6.74/1.49      ( k2_funct_1(k2_funct_1(sK3)) = sK3
% 6.74/1.49      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_relat_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_relat_1(sK3) != iProver_top ),
% 6.74/1.49      inference(equality_resolution_simp,[status(thm)],[c_23590]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2019,plain,
% 6.74/1.49      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 6.74/1.49      | v1_funct_1(X0) != iProver_top
% 6.74/1.49      | v1_relat_1(X0) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_7468,plain,
% 6.74/1.49      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK3)),k1_relat_1(sK3)))) = iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_7465,c_2019]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_7488,plain,
% 6.74/1.49      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_relat_1(k2_funct_1(sK3)) != iProver_top ),
% 6.74/1.49      inference(light_normalisation,[status(thm)],[c_7468,c_7437]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_46,plain,
% 6.74/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 6.74/1.49      | ~ v2_funct_1(X0)
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 6.74/1.49      inference(cnf_transformation,[],[f143]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2790,plain,
% 6.74/1.49      ( ~ v1_funct_2(sK3,X0,X1)
% 6.74/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 6.74/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.74/1.49      | ~ v2_funct_1(sK3)
% 6.74/1.49      | ~ v1_funct_1(sK3)
% 6.74/1.49      | k2_relset_1(X0,X1,sK3) != X1 ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_46]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3682,plain,
% 6.74/1.49      ( ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
% 6.74/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
% 6.74/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
% 6.74/1.49      | ~ v2_funct_1(sK3)
% 6.74/1.49      | ~ v1_funct_1(sK3)
% 6.74/1.49      | k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) != k2_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_2790]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3683,plain,
% 6.74/1.49      ( k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) != k2_relat_1(sK3)
% 6.74/1.49      | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top
% 6.74/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
% 6.74/1.49      | v2_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_3682]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3703,plain,
% 6.74/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
% 6.74/1.49      | k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) = k2_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_30]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_7727,plain,
% 6.74/1.49      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) = iProver_top ),
% 6.74/1.49      inference(global_propositional_subsumption,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_7488,c_62,c_69,c_60,c_71,c_72,c_2536,c_2537,c_2895,
% 6.74/1.49                 c_2911,c_2913,c_3683,c_3703]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_7734,plain,
% 6.74/1.49      ( k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_relat_1(k2_funct_1(sK3)) ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_7727,c_2028]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_7755,plain,
% 6.74/1.49      ( k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k1_relat_1(sK3) ),
% 6.74/1.49      inference(light_normalisation,[status(thm)],[c_7734,c_7465]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_56,plain,
% 6.74/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | ~ v2_funct_1(X0)
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 6.74/1.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 6.74/1.49      inference(cnf_transformation,[],[f151]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2017,plain,
% 6.74/1.49      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 6.74/1.49      | k2_relset_1(X0,X1,X2) != X1
% 6.74/1.49      | v1_funct_2(X2,X0,X1) != iProver_top
% 6.74/1.49      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 6.74/1.49      | v2_funct_1(X2) != iProver_top
% 6.74/1.49      | v1_funct_1(X2) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_7817,plain,
% 6.74/1.49      ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) != iProver_top
% 6.74/1.49      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_7755,c_2017]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_19,plain,
% 6.74/1.49      ( ~ v2_funct_1(X0)
% 6.74/1.49      | v2_funct_1(k2_funct_1(X0))
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | ~ v1_relat_1(X0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f115]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2533,plain,
% 6.74/1.49      ( v2_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | ~ v2_funct_1(sK3)
% 6.74/1.49      | ~ v1_funct_1(sK3)
% 6.74/1.49      | ~ v1_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_19]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2534,plain,
% 6.74/1.49      ( v2_funct_1(k2_funct_1(sK3)) = iProver_top
% 6.74/1.49      | v2_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_relat_1(sK3) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_2533]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_48,plain,
% 6.74/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | ~ v2_funct_1(X0)
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | v1_funct_1(k2_funct_1(X0))
% 6.74/1.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 6.74/1.49      inference(cnf_transformation,[],[f141]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_15,plain,
% 6.74/1.49      ( ~ v1_funct_1(X0)
% 6.74/1.49      | v1_funct_1(k2_funct_1(X0))
% 6.74/1.49      | ~ v1_relat_1(X0) ),
% 6.74/1.49      inference(cnf_transformation,[],[f110]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_356,plain,
% 6.74/1.49      ( v1_funct_1(k2_funct_1(X0))
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 6.74/1.49      inference(global_propositional_subsumption,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_48,c_28,c_15]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_357,plain,
% 6.74/1.49      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | v1_funct_1(k2_funct_1(X0)) ),
% 6.74/1.49      inference(renaming,[status(thm)],[c_356]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2593,plain,
% 6.74/1.49      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 6.74/1.49      | v1_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | ~ v1_funct_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_357]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2594,plain,
% 6.74/1.49      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(sK3)) = iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_2593]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_47,plain,
% 6.74/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.74/1.49      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | ~ v2_funct_1(X0)
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | k2_relset_1(X1,X2,X0) != X2 ),
% 6.74/1.49      inference(cnf_transformation,[],[f142]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2800,plain,
% 6.74/1.49      ( v1_funct_2(k2_funct_1(sK3),X0,X1)
% 6.74/1.49      | ~ v1_funct_2(sK3,X1,X0)
% 6.74/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 6.74/1.49      | ~ v2_funct_1(sK3)
% 6.74/1.49      | ~ v1_funct_1(sK3)
% 6.74/1.49      | k2_relset_1(X1,X0,sK3) != X0 ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_47]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3687,plain,
% 6.74/1.49      ( v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
% 6.74/1.49      | ~ v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3))
% 6.74/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
% 6.74/1.49      | ~ v2_funct_1(sK3)
% 6.74/1.49      | ~ v1_funct_1(sK3)
% 6.74/1.49      | k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) != k2_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_2800]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3688,plain,
% 6.74/1.49      ( k2_relset_1(k1_relat_1(sK3),k2_relat_1(sK3),sK3) != k2_relat_1(sK3)
% 6.74/1.49      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) = iProver_top
% 6.74/1.49      | v1_funct_2(sK3,k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
% 6.74/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
% 6.74/1.49      | v2_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_3687]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2844,plain,
% 6.74/1.49      ( ~ v1_funct_2(k2_funct_1(sK3),X0,X1)
% 6.74/1.49      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.74/1.49      | ~ v2_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | ~ v1_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | k2_tops_2(X0,X1,k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | k2_relset_1(X0,X1,k2_funct_1(sK3)) != X1 ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_56]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_6032,plain,
% 6.74/1.49      ( ~ v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
% 6.74/1.49      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
% 6.74/1.49      | ~ v2_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | ~ v1_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != k1_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_2844]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_6033,plain,
% 6.74/1.49      ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != k1_relat_1(sK3)
% 6.74/1.49      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) != iProver_top
% 6.74/1.49      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_6032]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_13663,plain,
% 6.74/1.49      ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) = k2_funct_1(k2_funct_1(sK3)) ),
% 6.74/1.49      inference(global_propositional_subsumption,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_7817,c_62,c_69,c_60,c_71,c_72,c_2534,c_2536,c_2537,
% 6.74/1.49                 c_2594,c_2895,c_2911,c_2913,c_3683,c_3688,c_3703,c_6033,
% 6.74/1.49                 c_7755]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_5294,plain,
% 6.74/1.49      ( k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3) = k2_funct_1(sK3)
% 6.74/1.49      | v1_funct_2(sK3,k1_relat_1(sK3),k2_struct_0(sK2)) != iProver_top
% 6.74/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_struct_0(sK2)))) != iProver_top
% 6.74/1.49      | v2_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top ),
% 6.74/1.49      inference(superposition,[status(thm)],[c_3083,c_2017]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3082,plain,
% 6.74/1.49      ( v1_funct_2(sK3,k1_relat_1(sK3),k2_struct_0(sK2)) = iProver_top ),
% 6.74/1.49      inference(demodulation,[status(thm)],[c_3076,c_2081]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_5464,plain,
% 6.74/1.49      ( k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3) = k2_funct_1(sK3) ),
% 6.74/1.49      inference(global_propositional_subsumption,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_5294,c_69,c_72,c_3081,c_3082]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_43,plain,
% 6.74/1.49      ( r2_funct_2(X0,X1,X2,X2)
% 6.74/1.49      | ~ v1_funct_2(X2,X0,X1)
% 6.74/1.49      | ~ v1_funct_2(X3,X0,X1)
% 6.74/1.49      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.74/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.74/1.49      | ~ v1_funct_1(X2)
% 6.74/1.49      | ~ v1_funct_1(X3) ),
% 6.74/1.49      inference(cnf_transformation,[],[f138]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_57,negated_conjecture,
% 6.74/1.49      ( ~ r2_funct_2(u1_struct_0(sK1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),sK3) ),
% 6.74/1.49      inference(cnf_transformation,[],[f160]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_693,plain,
% 6.74/1.49      ( ~ v1_funct_2(X0,X1,X2)
% 6.74/1.49      | ~ v1_funct_2(X3,X1,X2)
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | ~ v1_funct_1(X3)
% 6.74/1.49      | k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) != X0
% 6.74/1.49      | u1_struct_0(sK2) != X2
% 6.74/1.49      | u1_struct_0(sK1) != X1
% 6.74/1.49      | sK3 != X0 ),
% 6.74/1.49      inference(resolution_lifted,[status(thm)],[c_43,c_57]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_694,plain,
% 6.74/1.49      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 6.74/1.49      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 6.74/1.49      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
% 6.74/1.49      | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
% 6.74/1.49      inference(unflattening,[status(thm)],[c_693]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_1204,plain,
% 6.74/1.49      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2))
% 6.74/1.49      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 6.74/1.49      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)))
% 6.74/1.49      | sP0_iProver_split
% 6.74/1.49      | sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)) ),
% 6.74/1.49      inference(splitting,
% 6.74/1.49                [splitting(split),new_symbols(definition,[])],
% 6.74/1.49                [c_694]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2008,plain,
% 6.74/1.49      ( sK3 != k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))
% 6.74/1.49      | v1_funct_2(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK2),sK3))) != iProver_top
% 6.74/1.49      | sP0_iProver_split = iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_1204]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2372,plain,
% 6.74/1.49      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
% 6.74/1.49      | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top
% 6.74/1.49      | sP0_iProver_split = iProver_top ),
% 6.74/1.49      inference(light_normalisation,[status(thm)],[c_2008,c_682,c_687]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_1203,plain,
% 6.74/1.49      ( ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2))
% 6.74/1.49      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 6.74/1.49      | ~ v1_funct_1(X0)
% 6.74/1.49      | ~ sP0_iProver_split ),
% 6.74/1.49      inference(splitting,
% 6.74/1.49                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 6.74/1.49                [c_694]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2009,plain,
% 6.74/1.49      ( v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 6.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 6.74/1.49      | v1_funct_1(X0) != iProver_top
% 6.74/1.49      | sP0_iProver_split != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_1203]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2225,plain,
% 6.74/1.49      ( v1_funct_2(X0,k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 6.74/1.49      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 6.74/1.49      | v1_funct_1(X0) != iProver_top
% 6.74/1.49      | sP0_iProver_split != iProver_top ),
% 6.74/1.49      inference(light_normalisation,[status(thm)],[c_2009,c_682,c_687]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2378,plain,
% 6.74/1.49      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)) != sK3
% 6.74/1.49      | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k2_struct_0(sK1),k2_struct_0(sK2)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK2)))) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK2),sK3))) != iProver_top ),
% 6.74/1.49      inference(forward_subsumption_resolution,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_2372,c_2225]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3079,plain,
% 6.74/1.49      ( k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3)) != sK3
% 6.74/1.49      | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3)),k1_relat_1(sK3),k2_struct_0(sK2)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_struct_0(sK2)))) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_tops_2(k1_relat_1(sK3),k2_struct_0(sK2),sK3))) != iProver_top ),
% 6.74/1.49      inference(demodulation,[status(thm)],[c_3076,c_2378]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_5467,plain,
% 6.74/1.49      ( k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_funct_1(sK3)) != sK3
% 6.74/1.49      | v1_funct_2(k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_funct_1(sK3)),k1_relat_1(sK3),k2_struct_0(sK2)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_struct_0(sK2)))) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_tops_2(k2_struct_0(sK2),k1_relat_1(sK3),k2_funct_1(sK3))) != iProver_top ),
% 6.74/1.49      inference(demodulation,[status(thm)],[c_5464,c_3079]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_6365,plain,
% 6.74/1.49      ( k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != sK3
% 6.74/1.49      | v1_funct_2(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)),k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_tops_2(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3))) != iProver_top ),
% 6.74/1.49      inference(light_normalisation,[status(thm)],[c_5467,c_5470]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_13666,plain,
% 6.74/1.49      ( k2_funct_1(k2_funct_1(sK3)) != sK3
% 6.74/1.49      | v1_funct_2(k2_funct_1(k2_funct_1(sK3)),k1_relat_1(sK3),k2_relat_1(sK3)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_funct_1(k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(k2_funct_1(sK3))) != iProver_top ),
% 6.74/1.49      inference(demodulation,[status(thm)],[c_13663,c_6365]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2845,plain,
% 6.74/1.49      ( v1_funct_2(k2_funct_1(k2_funct_1(sK3)),X0,X1)
% 6.74/1.49      | ~ v1_funct_2(k2_funct_1(sK3),X1,X0)
% 6.74/1.49      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 6.74/1.49      | ~ v2_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | ~ v1_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | k2_relset_1(X1,X0,k2_funct_1(sK3)) != X0 ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_47]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_6037,plain,
% 6.74/1.49      ( v1_funct_2(k2_funct_1(k2_funct_1(sK3)),k1_relat_1(sK3),k2_relat_1(sK3))
% 6.74/1.49      | ~ v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
% 6.74/1.49      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
% 6.74/1.49      | ~ v2_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | ~ v1_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != k1_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_2845]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_6038,plain,
% 6.74/1.49      ( k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != k1_relat_1(sK3)
% 6.74/1.49      | v1_funct_2(k2_funct_1(k2_funct_1(sK3)),k1_relat_1(sK3),k2_relat_1(sK3)) = iProver_top
% 6.74/1.49      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) != iProver_top
% 6.74/1.49      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_6037]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2846,plain,
% 6.74/1.49      ( ~ v1_funct_2(k2_funct_1(sK3),X0,X1)
% 6.74/1.49      | m1_subset_1(k2_funct_1(k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 6.74/1.49      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 6.74/1.49      | ~ v2_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | ~ v1_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | k2_relset_1(X0,X1,k2_funct_1(sK3)) != X1 ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_46]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_6031,plain,
% 6.74/1.49      ( ~ v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3))
% 6.74/1.49      | m1_subset_1(k2_funct_1(k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3))))
% 6.74/1.49      | ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3))))
% 6.74/1.49      | ~ v2_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | ~ v1_funct_1(k2_funct_1(sK3))
% 6.74/1.49      | k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != k1_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_2846]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_6035,plain,
% 6.74/1.49      ( k2_relset_1(k2_relat_1(sK3),k1_relat_1(sK3),k2_funct_1(sK3)) != k1_relat_1(sK3)
% 6.74/1.49      | v1_funct_2(k2_funct_1(sK3),k2_relat_1(sK3),k1_relat_1(sK3)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_funct_1(k2_funct_1(sK3)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK3),k2_relat_1(sK3)))) = iProver_top
% 6.74/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK3),k1_relat_1(sK3)))) != iProver_top
% 6.74/1.49      | v2_funct_1(k2_funct_1(sK3)) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_6031]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_1207,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3891,plain,
% 6.74/1.49      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != X0
% 6.74/1.49      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 6.74/1.49      | u1_struct_0(sK2) != X0 ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_1207]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_5782,plain,
% 6.74/1.49      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) = u1_struct_0(sK2)
% 6.74/1.49      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != k2_struct_0(sK2)
% 6.74/1.49      | u1_struct_0(sK2) != k2_struct_0(sK2) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_3891]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3646,plain,
% 6.74/1.49      ( ~ m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 6.74/1.49      | v1_funct_1(k2_funct_1(k2_funct_1(sK3)))
% 6.74/1.49      | ~ v1_funct_1(k2_funct_1(sK3)) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_357]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3650,plain,
% 6.74/1.49      ( m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) != iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(k2_funct_1(sK3))) = iProver_top
% 6.74/1.49      | v1_funct_1(k2_funct_1(sK3)) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_3646]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3048,plain,
% 6.74/1.49      ( ~ v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2))
% 6.74/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1))))
% 6.74/1.49      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2))))
% 6.74/1.49      | ~ v2_funct_1(sK3)
% 6.74/1.49      | ~ v1_funct_1(sK3)
% 6.74/1.49      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_2790]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_3049,plain,
% 6.74/1.49      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK2),sK3) != u1_struct_0(sK2)
% 6.74/1.49      | v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) != iProver_top
% 6.74/1.49      | m1_subset_1(k2_funct_1(sK3),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK1)))) = iProver_top
% 6.74/1.49      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK2)))) != iProver_top
% 6.74/1.49      | v2_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_funct_1(sK3) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_3048]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_16,plain,
% 6.74/1.49      ( ~ v1_funct_1(X0)
% 6.74/1.49      | ~ v1_relat_1(X0)
% 6.74/1.49      | v1_relat_1(k2_funct_1(X0)) ),
% 6.74/1.49      inference(cnf_transformation,[],[f109]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2897,plain,
% 6.74/1.49      ( ~ v1_funct_1(sK3)
% 6.74/1.49      | v1_relat_1(k2_funct_1(sK3))
% 6.74/1.49      | ~ v1_relat_1(sK3) ),
% 6.74/1.49      inference(instantiation,[status(thm)],[c_16]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_2907,plain,
% 6.74/1.49      ( v1_funct_1(sK3) != iProver_top
% 6.74/1.49      | v1_relat_1(k2_funct_1(sK3)) = iProver_top
% 6.74/1.49      | v1_relat_1(sK3) != iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_2897]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(c_70,plain,
% 6.74/1.49      ( v1_funct_2(sK3,u1_struct_0(sK1),u1_struct_0(sK2)) = iProver_top ),
% 6.74/1.49      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 6.74/1.49  
% 6.74/1.49  cnf(contradiction,plain,
% 6.74/1.49      ( $false ),
% 6.74/1.49      inference(minisat,
% 6.74/1.49                [status(thm)],
% 6.74/1.49                [c_23591,c_13666,c_7755,c_6038,c_6035,c_5782,c_3703,
% 6.74/1.49                 c_3688,c_3683,c_3650,c_3049,c_2913,c_2911,c_2895,c_2907,
% 6.74/1.49                 c_2594,c_2537,c_2536,c_2534,c_682,c_72,c_59,c_71,c_60,
% 6.74/1.49                 c_70,c_69,c_62]) ).
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  % SZS output end CNFRefutation for theBenchmark.p
% 6.74/1.49  
% 6.74/1.49  ------                               Statistics
% 6.74/1.49  
% 6.74/1.49  ------ General
% 6.74/1.49  
% 6.74/1.49  abstr_ref_over_cycles:                  0
% 6.74/1.49  abstr_ref_under_cycles:                 0
% 6.74/1.49  gc_basic_clause_elim:                   0
% 6.74/1.49  forced_gc_time:                         0
% 6.74/1.49  parsing_time:                           0.014
% 6.74/1.49  unif_index_cands_time:                  0.
% 6.74/1.49  unif_index_add_time:                    0.
% 6.74/1.49  orderings_time:                         0.
% 6.74/1.49  out_proof_time:                         0.019
% 6.74/1.49  total_time:                             0.659
% 6.74/1.49  num_of_symbols:                         61
% 6.74/1.49  num_of_terms:                           24639
% 6.74/1.49  
% 6.74/1.49  ------ Preprocessing
% 6.74/1.49  
% 6.74/1.49  num_of_splits:                          1
% 6.74/1.49  num_of_split_atoms:                     1
% 6.74/1.49  num_of_reused_defs:                     0
% 6.74/1.49  num_eq_ax_congr_red:                    13
% 6.74/1.49  num_of_sem_filtered_clauses:            1
% 6.74/1.49  num_of_subtypes:                        0
% 6.74/1.49  monotx_restored_types:                  0
% 6.74/1.49  sat_num_of_epr_types:                   0
% 6.74/1.49  sat_num_of_non_cyclic_types:            0
% 6.74/1.49  sat_guarded_non_collapsed_types:        0
% 6.74/1.49  num_pure_diseq_elim:                    0
% 6.74/1.49  simp_replaced_by:                       0
% 6.74/1.49  res_preprocessed:                       258
% 6.74/1.49  prep_upred:                             0
% 6.74/1.49  prep_unflattend:                        15
% 6.74/1.49  smt_new_axioms:                         0
% 6.74/1.49  pred_elim_cands:                        7
% 6.74/1.49  pred_elim:                              5
% 6.74/1.49  pred_elim_cl:                           7
% 6.74/1.49  pred_elim_cycles:                       8
% 6.74/1.49  merged_defs:                            0
% 6.74/1.49  merged_defs_ncl:                        0
% 6.74/1.49  bin_hyper_res:                          0
% 6.74/1.49  prep_cycles:                            4
% 6.74/1.49  pred_elim_time:                         0.008
% 6.74/1.49  splitting_time:                         0.
% 6.74/1.49  sem_filter_time:                        0.
% 6.74/1.49  monotx_time:                            0.001
% 6.74/1.49  subtype_inf_time:                       0.
% 6.74/1.49  
% 6.74/1.49  ------ Problem properties
% 6.74/1.49  
% 6.74/1.49  clauses:                                53
% 6.74/1.49  conjectures:                            5
% 6.74/1.49  epr:                                    7
% 6.74/1.49  horn:                                   47
% 6.74/1.49  ground:                                 10
% 6.74/1.49  unary:                                  19
% 6.74/1.49  binary:                                 4
% 6.74/1.49  lits:                                   162
% 6.74/1.49  lits_eq:                                39
% 6.74/1.49  fd_pure:                                0
% 6.74/1.49  fd_pseudo:                              0
% 6.74/1.49  fd_cond:                                3
% 6.74/1.49  fd_pseudo_cond:                         5
% 6.74/1.49  ac_symbols:                             0
% 6.74/1.49  
% 6.74/1.49  ------ Propositional Solver
% 6.74/1.49  
% 6.74/1.49  prop_solver_calls:                      28
% 6.74/1.49  prop_fast_solver_calls:                 2765
% 6.74/1.49  smt_solver_calls:                       0
% 6.74/1.49  smt_fast_solver_calls:                  0
% 6.74/1.49  prop_num_of_clauses:                    8914
% 6.74/1.49  prop_preprocess_simplified:             23556
% 6.74/1.49  prop_fo_subsumed:                       242
% 6.74/1.49  prop_solver_time:                       0.
% 6.74/1.49  smt_solver_time:                        0.
% 6.74/1.49  smt_fast_solver_time:                   0.
% 6.74/1.49  prop_fast_solver_time:                  0.
% 6.74/1.49  prop_unsat_core_time:                   0.001
% 6.74/1.49  
% 6.74/1.49  ------ QBF
% 6.74/1.49  
% 6.74/1.49  qbf_q_res:                              0
% 6.74/1.49  qbf_num_tautologies:                    0
% 6.74/1.49  qbf_prep_cycles:                        0
% 6.74/1.49  
% 6.74/1.49  ------ BMC1
% 6.74/1.49  
% 6.74/1.49  bmc1_current_bound:                     -1
% 6.74/1.49  bmc1_last_solved_bound:                 -1
% 6.74/1.49  bmc1_unsat_core_size:                   -1
% 6.74/1.49  bmc1_unsat_core_parents_size:           -1
% 6.74/1.49  bmc1_merge_next_fun:                    0
% 6.74/1.49  bmc1_unsat_core_clauses_time:           0.
% 6.74/1.49  
% 6.74/1.49  ------ Instantiation
% 6.74/1.49  
% 6.74/1.49  inst_num_of_clauses:                    2749
% 6.74/1.49  inst_num_in_passive:                    1603
% 6.74/1.49  inst_num_in_active:                     923
% 6.74/1.49  inst_num_in_unprocessed:                225
% 6.74/1.49  inst_num_of_loops:                      1010
% 6.74/1.49  inst_num_of_learning_restarts:          0
% 6.74/1.49  inst_num_moves_active_passive:          85
% 6.74/1.49  inst_lit_activity:                      0
% 6.74/1.49  inst_lit_activity_moves:                0
% 6.74/1.49  inst_num_tautologies:                   0
% 6.74/1.49  inst_num_prop_implied:                  0
% 6.74/1.49  inst_num_existing_simplified:           0
% 6.74/1.49  inst_num_eq_res_simplified:             0
% 6.74/1.49  inst_num_child_elim:                    0
% 6.74/1.49  inst_num_of_dismatching_blockings:      1133
% 6.74/1.49  inst_num_of_non_proper_insts:           2304
% 6.74/1.49  inst_num_of_duplicates:                 0
% 6.74/1.49  inst_inst_num_from_inst_to_res:         0
% 6.74/1.49  inst_dismatching_checking_time:         0.
% 6.74/1.49  
% 6.74/1.49  ------ Resolution
% 6.74/1.49  
% 6.74/1.49  res_num_of_clauses:                     0
% 6.74/1.49  res_num_in_passive:                     0
% 6.74/1.49  res_num_in_active:                      0
% 6.74/1.49  res_num_of_loops:                       262
% 6.74/1.49  res_forward_subset_subsumed:            135
% 6.74/1.49  res_backward_subset_subsumed:           10
% 6.74/1.49  res_forward_subsumed:                   0
% 6.74/1.49  res_backward_subsumed:                  0
% 6.74/1.49  res_forward_subsumption_resolution:     3
% 6.74/1.49  res_backward_subsumption_resolution:    0
% 6.74/1.49  res_clause_to_clause_subsumption:       793
% 6.74/1.49  res_orphan_elimination:                 0
% 6.74/1.49  res_tautology_del:                      100
% 6.74/1.49  res_num_eq_res_simplified:              0
% 6.74/1.49  res_num_sel_changes:                    0
% 6.74/1.49  res_moves_from_active_to_pass:          0
% 6.74/1.49  
% 6.74/1.49  ------ Superposition
% 6.74/1.49  
% 6.74/1.49  sup_time_total:                         0.
% 6.74/1.49  sup_time_generating:                    0.
% 6.74/1.49  sup_time_sim_full:                      0.
% 6.74/1.49  sup_time_sim_immed:                     0.
% 6.74/1.49  
% 6.74/1.49  sup_num_of_clauses:                     312
% 6.74/1.49  sup_num_in_active:                      170
% 6.74/1.49  sup_num_in_passive:                     142
% 6.74/1.49  sup_num_of_loops:                       201
% 6.74/1.49  sup_fw_superposition:                   168
% 6.74/1.49  sup_bw_superposition:                   233
% 6.74/1.49  sup_immediate_simplified:               131
% 6.74/1.49  sup_given_eliminated:                   3
% 6.74/1.49  comparisons_done:                       0
% 6.74/1.49  comparisons_avoided:                    3
% 6.74/1.49  
% 6.74/1.49  ------ Simplifications
% 6.74/1.49  
% 6.74/1.49  
% 6.74/1.49  sim_fw_subset_subsumed:                 56
% 6.74/1.49  sim_bw_subset_subsumed:                 2
% 6.74/1.49  sim_fw_subsumed:                        28
% 6.74/1.49  sim_bw_subsumed:                        0
% 6.74/1.49  sim_fw_subsumption_res:                 52
% 6.74/1.49  sim_bw_subsumption_res:                 0
% 6.74/1.49  sim_tautology_del:                      6
% 6.74/1.49  sim_eq_tautology_del:                   33
% 6.74/1.49  sim_eq_res_simp:                        5
% 6.74/1.49  sim_fw_demodulated:                     22
% 6.74/1.49  sim_bw_demodulated:                     35
% 6.74/1.49  sim_light_normalised:                   69
% 6.74/1.49  sim_joinable_taut:                      0
% 6.74/1.49  sim_joinable_simp:                      0
% 6.74/1.49  sim_ac_normalised:                      0
% 6.74/1.49  sim_smt_subsumption:                    0
% 6.74/1.49  
%------------------------------------------------------------------------------
