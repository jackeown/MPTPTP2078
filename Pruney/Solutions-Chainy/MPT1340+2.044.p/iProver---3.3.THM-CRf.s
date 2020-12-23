%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:30 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  229 (2375 expanded)
%              Number of clauses        :  139 ( 693 expanded)
%              Number of leaves         :   23 ( 676 expanded)
%              Depth                    :   25
%              Number of atoms          :  901 (15260 expanded)
%              Number of equality atoms :  338 (2535 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f30,conjecture,(
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

fof(f31,negated_conjecture,(
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
    inference(negated_conjecture,[],[f30])).

fof(f70,plain,(
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
    inference(ennf_transformation,[],[f31])).

fof(f71,plain,(
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
    inference(flattening,[],[f70])).

fof(f81,plain,(
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

fof(f80,plain,(
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

fof(f79,plain,
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

fof(f82,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f71,f81,f80,f79])).

fof(f136,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f82])).

fof(f26,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f127,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f133,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

fof(f131,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f82])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f112,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f137,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f51])).

fof(f114,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f28,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f66])).

fof(f129,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f132,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f53])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f54])).

fof(f115,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f17])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f111,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f134,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

fof(f135,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f82])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f59])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f138,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f82])).

fof(f25,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f62,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f61])).

fof(f126,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f125,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0)
              & k1_relat_1(X0) = k2_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
          | k1_relat_1(X0) != k2_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f110,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0)
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f21,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f117,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f21])).

fof(f142,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k1_relat_1(X0) != k2_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f110,f117])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f108,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f109,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f99,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f98,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f69,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f68])).

fof(f130,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f69])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f104,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f23,axiom,(
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

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f57])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f22,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f56,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f139,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_50,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1572,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_43,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_53,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_613,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_53])).

cnf(c_614,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_613])).

cnf(c_55,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_618,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_55])).

cnf(c_619,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_618])).

cnf(c_1635,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1572,c_614,c_619])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1582,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3024,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1635,c_1582])).

cnf(c_49,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_1632,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_49,c_614,c_619])).

cnf(c_3201,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3024,c_1632])).

cnf(c_3210,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3201,c_1635])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1598,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3782,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3210,c_1598])).

cnf(c_61,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_2000,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2495,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2000])).

cnf(c_2496,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2495])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2613,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2614,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2613])).

cnf(c_4174,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3782,c_61,c_2496,c_2614])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_45,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f129])).

cnf(c_54,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f132])).

cnf(c_600,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_45,c_54])).

cnf(c_601,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_600])).

cnf(c_603,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_601,c_53])).

cnf(c_629,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_603])).

cnf(c_630,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_33,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f115])).

cnf(c_653,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_630,c_33])).

cnf(c_28,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_669,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_653,c_28])).

cnf(c_1567,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_1749,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1567,c_614])).

cnf(c_2398,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1635,c_1749])).

cnf(c_52,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_59,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_51,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_1571,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_1629,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1571,c_614,c_619])).

cnf(c_2457,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2398,c_59,c_1629])).

cnf(c_4180,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4174,c_2457])).

cnf(c_3204,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3201,c_3024])).

cnf(c_4189,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4180,c_3204])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1577,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_4992,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4189,c_1577])).

cnf(c_48,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_62,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_40,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_2051,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_2052,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2051])).

cnf(c_41,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_2054,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_41])).

cnf(c_2055,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2054])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_625,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_603])).

cnf(c_1611,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_614,c_625])).

cnf(c_3212,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3201,c_1611])).

cnf(c_10036,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4992,c_59,c_61,c_62,c_2052,c_2055,c_2496,c_2614,c_3212])).

cnf(c_27,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
    | k2_funct_1(X0) = X1
    | k2_relat_1(X1) != k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_1583,plain,
    ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
    | k2_funct_1(X1) = X0
    | k2_relat_1(X0) != k1_relat_1(X1)
    | v2_funct_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_10039,plain,
    ( k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_10036,c_1583])).

cnf(c_1573,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_26,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1584,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4754,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1573,c_1584])).

cnf(c_2048,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_4787,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4754,c_52,c_50,c_48,c_2048,c_2495,c_2613])).

cnf(c_25,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1585,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_5454,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1573,c_1585])).

cnf(c_2040,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_5851,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5454,c_52,c_50,c_48,c_2040,c_2495,c_2613])).

cnf(c_10040,plain,
    ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10039,c_4787,c_5851])).

cnf(c_10041,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_10040])).

cnf(c_1576,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4790,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4787,c_1576])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1992,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_1993,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1992])).

cnf(c_16,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1995,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1996,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1995])).

cnf(c_4887,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4790,c_59,c_61,c_1993,c_1996,c_2496,c_2614])).

cnf(c_4893,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4887,c_1582])).

cnf(c_5855,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_5851,c_4893])).

cnf(c_46,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f130])).

cnf(c_1574,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_5997,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5855,c_1574])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_2015,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_2170,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_3081,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2170])).

cnf(c_36,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2180,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_3089,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2180])).

cnf(c_3100,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_2259,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_tops_2(X0,X1,k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_46])).

cnf(c_4615,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2259])).

cnf(c_8738,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5997,c_52,c_50,c_48,c_1992,c_2015,c_2051,c_2054,c_2495,c_2613,c_3081,c_3089,c_3100,c_4615,c_5855])).

cnf(c_2507,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1632,c_1574])).

cnf(c_2601,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2507,c_59,c_62,c_1629,c_1635])).

cnf(c_34,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_47,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_564,plain,
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
    inference(resolution_lifted,[status(thm)],[c_34,c_47])).

cnf(c_565,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_564])).

cnf(c_938,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_565])).

cnf(c_1568,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_938])).

cnf(c_1880,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1568,c_614,c_619])).

cnf(c_937,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_565])).

cnf(c_1569,plain,
    ( v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_937])).

cnf(c_1730,plain,
    ( v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1569,c_614,c_619])).

cnf(c_1886,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1880,c_1730])).

cnf(c_2604,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2601,c_1886])).

cnf(c_3205,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3201,c_2604])).

cnf(c_4186,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4180,c_3205])).

cnf(c_8741,plain,
    ( k2_funct_1(k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8738,c_4186])).

cnf(c_2260,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK2)),X0,X1)
    | ~ v1_funct_2(k2_funct_1(sK2),X1,X0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X1,X0,k2_funct_1(sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_4620,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2260])).

cnf(c_4621,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4620])).

cnf(c_2261,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_4614,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2261])).

cnf(c_4618,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4614])).

cnf(c_3090,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3089])).

cnf(c_3085,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3081])).

cnf(c_2208,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2214,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2208])).

cnf(c_2016,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2015])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10041,c_8741,c_5855,c_4621,c_4618,c_3100,c_3090,c_3085,c_2614,c_2613,c_2496,c_2495,c_2214,c_2055,c_2052,c_2051,c_2016,c_1996,c_1993,c_62,c_61,c_50,c_59,c_52])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:45:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.71/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.71/0.99  
% 3.71/0.99  ------  iProver source info
% 3.71/0.99  
% 3.71/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.71/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.71/0.99  git: non_committed_changes: false
% 3.71/0.99  git: last_make_outside_of_git: false
% 3.71/0.99  
% 3.71/0.99  ------ 
% 3.71/0.99  
% 3.71/0.99  ------ Input Options
% 3.71/0.99  
% 3.71/0.99  --out_options                           all
% 3.71/0.99  --tptp_safe_out                         true
% 3.71/0.99  --problem_path                          ""
% 3.71/0.99  --include_path                          ""
% 3.71/0.99  --clausifier                            res/vclausify_rel
% 3.71/0.99  --clausifier_options                    --mode clausify
% 3.71/0.99  --stdin                                 false
% 3.71/0.99  --stats_out                             all
% 3.71/0.99  
% 3.71/0.99  ------ General Options
% 3.71/0.99  
% 3.71/0.99  --fof                                   false
% 3.71/0.99  --time_out_real                         305.
% 3.71/0.99  --time_out_virtual                      -1.
% 3.71/0.99  --symbol_type_check                     false
% 3.71/0.99  --clausify_out                          false
% 3.71/0.99  --sig_cnt_out                           false
% 3.71/0.99  --trig_cnt_out                          false
% 3.71/0.99  --trig_cnt_out_tolerance                1.
% 3.71/0.99  --trig_cnt_out_sk_spl                   false
% 3.71/0.99  --abstr_cl_out                          false
% 3.71/0.99  
% 3.71/0.99  ------ Global Options
% 3.71/0.99  
% 3.71/0.99  --schedule                              default
% 3.71/0.99  --add_important_lit                     false
% 3.71/0.99  --prop_solver_per_cl                    1000
% 3.71/0.99  --min_unsat_core                        false
% 3.71/0.99  --soft_assumptions                      false
% 3.71/0.99  --soft_lemma_size                       3
% 3.71/0.99  --prop_impl_unit_size                   0
% 3.71/0.99  --prop_impl_unit                        []
% 3.71/0.99  --share_sel_clauses                     true
% 3.71/0.99  --reset_solvers                         false
% 3.71/0.99  --bc_imp_inh                            [conj_cone]
% 3.71/0.99  --conj_cone_tolerance                   3.
% 3.71/0.99  --extra_neg_conj                        none
% 3.71/0.99  --large_theory_mode                     true
% 3.71/0.99  --prolific_symb_bound                   200
% 3.71/0.99  --lt_threshold                          2000
% 3.71/0.99  --clause_weak_htbl                      true
% 3.71/0.99  --gc_record_bc_elim                     false
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing Options
% 3.71/0.99  
% 3.71/0.99  --preprocessing_flag                    true
% 3.71/0.99  --time_out_prep_mult                    0.1
% 3.71/0.99  --splitting_mode                        input
% 3.71/0.99  --splitting_grd                         true
% 3.71/0.99  --splitting_cvd                         false
% 3.71/0.99  --splitting_cvd_svl                     false
% 3.71/0.99  --splitting_nvd                         32
% 3.71/0.99  --sub_typing                            true
% 3.71/0.99  --prep_gs_sim                           true
% 3.71/0.99  --prep_unflatten                        true
% 3.71/0.99  --prep_res_sim                          true
% 3.71/0.99  --prep_upred                            true
% 3.71/0.99  --prep_sem_filter                       exhaustive
% 3.71/0.99  --prep_sem_filter_out                   false
% 3.71/0.99  --pred_elim                             true
% 3.71/0.99  --res_sim_input                         true
% 3.71/0.99  --eq_ax_congr_red                       true
% 3.71/0.99  --pure_diseq_elim                       true
% 3.71/0.99  --brand_transform                       false
% 3.71/0.99  --non_eq_to_eq                          false
% 3.71/0.99  --prep_def_merge                        true
% 3.71/0.99  --prep_def_merge_prop_impl              false
% 3.71/0.99  --prep_def_merge_mbd                    true
% 3.71/0.99  --prep_def_merge_tr_red                 false
% 3.71/0.99  --prep_def_merge_tr_cl                  false
% 3.71/0.99  --smt_preprocessing                     true
% 3.71/0.99  --smt_ac_axioms                         fast
% 3.71/0.99  --preprocessed_out                      false
% 3.71/0.99  --preprocessed_stats                    false
% 3.71/0.99  
% 3.71/0.99  ------ Abstraction refinement Options
% 3.71/0.99  
% 3.71/0.99  --abstr_ref                             []
% 3.71/0.99  --abstr_ref_prep                        false
% 3.71/0.99  --abstr_ref_until_sat                   false
% 3.71/0.99  --abstr_ref_sig_restrict                funpre
% 3.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/0.99  --abstr_ref_under                       []
% 3.71/0.99  
% 3.71/0.99  ------ SAT Options
% 3.71/0.99  
% 3.71/0.99  --sat_mode                              false
% 3.71/0.99  --sat_fm_restart_options                ""
% 3.71/0.99  --sat_gr_def                            false
% 3.71/0.99  --sat_epr_types                         true
% 3.71/0.99  --sat_non_cyclic_types                  false
% 3.71/0.99  --sat_finite_models                     false
% 3.71/0.99  --sat_fm_lemmas                         false
% 3.71/0.99  --sat_fm_prep                           false
% 3.71/0.99  --sat_fm_uc_incr                        true
% 3.71/0.99  --sat_out_model                         small
% 3.71/0.99  --sat_out_clauses                       false
% 3.71/0.99  
% 3.71/0.99  ------ QBF Options
% 3.71/0.99  
% 3.71/0.99  --qbf_mode                              false
% 3.71/0.99  --qbf_elim_univ                         false
% 3.71/0.99  --qbf_dom_inst                          none
% 3.71/0.99  --qbf_dom_pre_inst                      false
% 3.71/0.99  --qbf_sk_in                             false
% 3.71/0.99  --qbf_pred_elim                         true
% 3.71/0.99  --qbf_split                             512
% 3.71/0.99  
% 3.71/0.99  ------ BMC1 Options
% 3.71/0.99  
% 3.71/0.99  --bmc1_incremental                      false
% 3.71/0.99  --bmc1_axioms                           reachable_all
% 3.71/0.99  --bmc1_min_bound                        0
% 3.71/0.99  --bmc1_max_bound                        -1
% 3.71/0.99  --bmc1_max_bound_default                -1
% 3.71/0.99  --bmc1_symbol_reachability              true
% 3.71/0.99  --bmc1_property_lemmas                  false
% 3.71/0.99  --bmc1_k_induction                      false
% 3.71/0.99  --bmc1_non_equiv_states                 false
% 3.71/0.99  --bmc1_deadlock                         false
% 3.71/0.99  --bmc1_ucm                              false
% 3.71/0.99  --bmc1_add_unsat_core                   none
% 3.71/0.99  --bmc1_unsat_core_children              false
% 3.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/0.99  --bmc1_out_stat                         full
% 3.71/0.99  --bmc1_ground_init                      false
% 3.71/0.99  --bmc1_pre_inst_next_state              false
% 3.71/0.99  --bmc1_pre_inst_state                   false
% 3.71/0.99  --bmc1_pre_inst_reach_state             false
% 3.71/0.99  --bmc1_out_unsat_core                   false
% 3.71/0.99  --bmc1_aig_witness_out                  false
% 3.71/0.99  --bmc1_verbose                          false
% 3.71/0.99  --bmc1_dump_clauses_tptp                false
% 3.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.71/0.99  --bmc1_dump_file                        -
% 3.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.71/0.99  --bmc1_ucm_extend_mode                  1
% 3.71/0.99  --bmc1_ucm_init_mode                    2
% 3.71/0.99  --bmc1_ucm_cone_mode                    none
% 3.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.71/0.99  --bmc1_ucm_relax_model                  4
% 3.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/0.99  --bmc1_ucm_layered_model                none
% 3.71/0.99  --bmc1_ucm_max_lemma_size               10
% 3.71/0.99  
% 3.71/0.99  ------ AIG Options
% 3.71/0.99  
% 3.71/0.99  --aig_mode                              false
% 3.71/0.99  
% 3.71/0.99  ------ Instantiation Options
% 3.71/0.99  
% 3.71/0.99  --instantiation_flag                    true
% 3.71/0.99  --inst_sos_flag                         false
% 3.71/0.99  --inst_sos_phase                        true
% 3.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/0.99  --inst_lit_sel_side                     num_symb
% 3.71/0.99  --inst_solver_per_active                1400
% 3.71/0.99  --inst_solver_calls_frac                1.
% 3.71/0.99  --inst_passive_queue_type               priority_queues
% 3.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/0.99  --inst_passive_queues_freq              [25;2]
% 3.71/0.99  --inst_dismatching                      true
% 3.71/0.99  --inst_eager_unprocessed_to_passive     true
% 3.71/0.99  --inst_prop_sim_given                   true
% 3.71/0.99  --inst_prop_sim_new                     false
% 3.71/0.99  --inst_subs_new                         false
% 3.71/0.99  --inst_eq_res_simp                      false
% 3.71/0.99  --inst_subs_given                       false
% 3.71/0.99  --inst_orphan_elimination               true
% 3.71/0.99  --inst_learning_loop_flag               true
% 3.71/0.99  --inst_learning_start                   3000
% 3.71/0.99  --inst_learning_factor                  2
% 3.71/0.99  --inst_start_prop_sim_after_learn       3
% 3.71/0.99  --inst_sel_renew                        solver
% 3.71/0.99  --inst_lit_activity_flag                true
% 3.71/0.99  --inst_restr_to_given                   false
% 3.71/0.99  --inst_activity_threshold               500
% 3.71/0.99  --inst_out_proof                        true
% 3.71/0.99  
% 3.71/0.99  ------ Resolution Options
% 3.71/0.99  
% 3.71/0.99  --resolution_flag                       true
% 3.71/0.99  --res_lit_sel                           adaptive
% 3.71/0.99  --res_lit_sel_side                      none
% 3.71/0.99  --res_ordering                          kbo
% 3.71/0.99  --res_to_prop_solver                    active
% 3.71/0.99  --res_prop_simpl_new                    false
% 3.71/0.99  --res_prop_simpl_given                  true
% 3.71/0.99  --res_passive_queue_type                priority_queues
% 3.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/0.99  --res_passive_queues_freq               [15;5]
% 3.71/0.99  --res_forward_subs                      full
% 3.71/0.99  --res_backward_subs                     full
% 3.71/0.99  --res_forward_subs_resolution           true
% 3.71/0.99  --res_backward_subs_resolution          true
% 3.71/0.99  --res_orphan_elimination                true
% 3.71/0.99  --res_time_limit                        2.
% 3.71/0.99  --res_out_proof                         true
% 3.71/0.99  
% 3.71/0.99  ------ Superposition Options
% 3.71/0.99  
% 3.71/0.99  --superposition_flag                    true
% 3.71/0.99  --sup_passive_queue_type                priority_queues
% 3.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.71/0.99  --demod_completeness_check              fast
% 3.71/0.99  --demod_use_ground                      true
% 3.71/0.99  --sup_to_prop_solver                    passive
% 3.71/0.99  --sup_prop_simpl_new                    true
% 3.71/0.99  --sup_prop_simpl_given                  true
% 3.71/0.99  --sup_fun_splitting                     false
% 3.71/0.99  --sup_smt_interval                      50000
% 3.71/0.99  
% 3.71/0.99  ------ Superposition Simplification Setup
% 3.71/0.99  
% 3.71/0.99  --sup_indices_passive                   []
% 3.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.99  --sup_full_bw                           [BwDemod]
% 3.71/0.99  --sup_immed_triv                        [TrivRules]
% 3.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.99  --sup_immed_bw_main                     []
% 3.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.99  
% 3.71/0.99  ------ Combination Options
% 3.71/0.99  
% 3.71/0.99  --comb_res_mult                         3
% 3.71/0.99  --comb_sup_mult                         2
% 3.71/0.99  --comb_inst_mult                        10
% 3.71/0.99  
% 3.71/0.99  ------ Debug Options
% 3.71/0.99  
% 3.71/0.99  --dbg_backtrace                         false
% 3.71/0.99  --dbg_dump_prop_clauses                 false
% 3.71/0.99  --dbg_dump_prop_clauses_file            -
% 3.71/0.99  --dbg_out_stat                          false
% 3.71/0.99  ------ Parsing...
% 3.71/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/0.99  ------ Proving...
% 3.71/0.99  ------ Problem Properties 
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  clauses                                 43
% 3.71/0.99  conjectures                             5
% 3.71/0.99  EPR                                     5
% 3.71/0.99  Horn                                    40
% 3.71/0.99  unary                                   15
% 3.71/0.99  binary                                  2
% 3.71/0.99  lits                                    140
% 3.71/0.99  lits eq                                 37
% 3.71/0.99  fd_pure                                 0
% 3.71/0.99  fd_pseudo                               0
% 3.71/0.99  fd_cond                                 3
% 3.71/0.99  fd_pseudo_cond                          3
% 3.71/0.99  AC symbols                              0
% 3.71/0.99  
% 3.71/0.99  ------ Schedule dynamic 5 is on 
% 3.71/0.99  
% 3.71/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  ------ 
% 3.71/0.99  Current options:
% 3.71/0.99  ------ 
% 3.71/0.99  
% 3.71/0.99  ------ Input Options
% 3.71/0.99  
% 3.71/0.99  --out_options                           all
% 3.71/0.99  --tptp_safe_out                         true
% 3.71/0.99  --problem_path                          ""
% 3.71/0.99  --include_path                          ""
% 3.71/0.99  --clausifier                            res/vclausify_rel
% 3.71/0.99  --clausifier_options                    --mode clausify
% 3.71/0.99  --stdin                                 false
% 3.71/0.99  --stats_out                             all
% 3.71/0.99  
% 3.71/0.99  ------ General Options
% 3.71/0.99  
% 3.71/0.99  --fof                                   false
% 3.71/0.99  --time_out_real                         305.
% 3.71/0.99  --time_out_virtual                      -1.
% 3.71/0.99  --symbol_type_check                     false
% 3.71/0.99  --clausify_out                          false
% 3.71/0.99  --sig_cnt_out                           false
% 3.71/0.99  --trig_cnt_out                          false
% 3.71/0.99  --trig_cnt_out_tolerance                1.
% 3.71/0.99  --trig_cnt_out_sk_spl                   false
% 3.71/0.99  --abstr_cl_out                          false
% 3.71/0.99  
% 3.71/0.99  ------ Global Options
% 3.71/0.99  
% 3.71/0.99  --schedule                              default
% 3.71/0.99  --add_important_lit                     false
% 3.71/0.99  --prop_solver_per_cl                    1000
% 3.71/0.99  --min_unsat_core                        false
% 3.71/0.99  --soft_assumptions                      false
% 3.71/0.99  --soft_lemma_size                       3
% 3.71/0.99  --prop_impl_unit_size                   0
% 3.71/0.99  --prop_impl_unit                        []
% 3.71/0.99  --share_sel_clauses                     true
% 3.71/0.99  --reset_solvers                         false
% 3.71/0.99  --bc_imp_inh                            [conj_cone]
% 3.71/0.99  --conj_cone_tolerance                   3.
% 3.71/0.99  --extra_neg_conj                        none
% 3.71/0.99  --large_theory_mode                     true
% 3.71/0.99  --prolific_symb_bound                   200
% 3.71/0.99  --lt_threshold                          2000
% 3.71/0.99  --clause_weak_htbl                      true
% 3.71/0.99  --gc_record_bc_elim                     false
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing Options
% 3.71/0.99  
% 3.71/0.99  --preprocessing_flag                    true
% 3.71/0.99  --time_out_prep_mult                    0.1
% 3.71/0.99  --splitting_mode                        input
% 3.71/0.99  --splitting_grd                         true
% 3.71/0.99  --splitting_cvd                         false
% 3.71/0.99  --splitting_cvd_svl                     false
% 3.71/0.99  --splitting_nvd                         32
% 3.71/0.99  --sub_typing                            true
% 3.71/0.99  --prep_gs_sim                           true
% 3.71/0.99  --prep_unflatten                        true
% 3.71/0.99  --prep_res_sim                          true
% 3.71/0.99  --prep_upred                            true
% 3.71/0.99  --prep_sem_filter                       exhaustive
% 3.71/0.99  --prep_sem_filter_out                   false
% 3.71/0.99  --pred_elim                             true
% 3.71/0.99  --res_sim_input                         true
% 3.71/0.99  --eq_ax_congr_red                       true
% 3.71/0.99  --pure_diseq_elim                       true
% 3.71/0.99  --brand_transform                       false
% 3.71/0.99  --non_eq_to_eq                          false
% 3.71/0.99  --prep_def_merge                        true
% 3.71/0.99  --prep_def_merge_prop_impl              false
% 3.71/0.99  --prep_def_merge_mbd                    true
% 3.71/0.99  --prep_def_merge_tr_red                 false
% 3.71/0.99  --prep_def_merge_tr_cl                  false
% 3.71/0.99  --smt_preprocessing                     true
% 3.71/0.99  --smt_ac_axioms                         fast
% 3.71/0.99  --preprocessed_out                      false
% 3.71/0.99  --preprocessed_stats                    false
% 3.71/0.99  
% 3.71/0.99  ------ Abstraction refinement Options
% 3.71/0.99  
% 3.71/0.99  --abstr_ref                             []
% 3.71/0.99  --abstr_ref_prep                        false
% 3.71/0.99  --abstr_ref_until_sat                   false
% 3.71/0.99  --abstr_ref_sig_restrict                funpre
% 3.71/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.71/0.99  --abstr_ref_under                       []
% 3.71/0.99  
% 3.71/0.99  ------ SAT Options
% 3.71/0.99  
% 3.71/0.99  --sat_mode                              false
% 3.71/0.99  --sat_fm_restart_options                ""
% 3.71/0.99  --sat_gr_def                            false
% 3.71/0.99  --sat_epr_types                         true
% 3.71/0.99  --sat_non_cyclic_types                  false
% 3.71/0.99  --sat_finite_models                     false
% 3.71/0.99  --sat_fm_lemmas                         false
% 3.71/0.99  --sat_fm_prep                           false
% 3.71/0.99  --sat_fm_uc_incr                        true
% 3.71/0.99  --sat_out_model                         small
% 3.71/0.99  --sat_out_clauses                       false
% 3.71/0.99  
% 3.71/0.99  ------ QBF Options
% 3.71/0.99  
% 3.71/0.99  --qbf_mode                              false
% 3.71/0.99  --qbf_elim_univ                         false
% 3.71/0.99  --qbf_dom_inst                          none
% 3.71/0.99  --qbf_dom_pre_inst                      false
% 3.71/0.99  --qbf_sk_in                             false
% 3.71/0.99  --qbf_pred_elim                         true
% 3.71/0.99  --qbf_split                             512
% 3.71/0.99  
% 3.71/0.99  ------ BMC1 Options
% 3.71/0.99  
% 3.71/0.99  --bmc1_incremental                      false
% 3.71/0.99  --bmc1_axioms                           reachable_all
% 3.71/0.99  --bmc1_min_bound                        0
% 3.71/0.99  --bmc1_max_bound                        -1
% 3.71/0.99  --bmc1_max_bound_default                -1
% 3.71/0.99  --bmc1_symbol_reachability              true
% 3.71/0.99  --bmc1_property_lemmas                  false
% 3.71/0.99  --bmc1_k_induction                      false
% 3.71/0.99  --bmc1_non_equiv_states                 false
% 3.71/0.99  --bmc1_deadlock                         false
% 3.71/0.99  --bmc1_ucm                              false
% 3.71/0.99  --bmc1_add_unsat_core                   none
% 3.71/0.99  --bmc1_unsat_core_children              false
% 3.71/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.71/0.99  --bmc1_out_stat                         full
% 3.71/0.99  --bmc1_ground_init                      false
% 3.71/0.99  --bmc1_pre_inst_next_state              false
% 3.71/0.99  --bmc1_pre_inst_state                   false
% 3.71/0.99  --bmc1_pre_inst_reach_state             false
% 3.71/0.99  --bmc1_out_unsat_core                   false
% 3.71/0.99  --bmc1_aig_witness_out                  false
% 3.71/0.99  --bmc1_verbose                          false
% 3.71/0.99  --bmc1_dump_clauses_tptp                false
% 3.71/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.71/0.99  --bmc1_dump_file                        -
% 3.71/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.71/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.71/0.99  --bmc1_ucm_extend_mode                  1
% 3.71/0.99  --bmc1_ucm_init_mode                    2
% 3.71/0.99  --bmc1_ucm_cone_mode                    none
% 3.71/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.71/0.99  --bmc1_ucm_relax_model                  4
% 3.71/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.71/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.71/0.99  --bmc1_ucm_layered_model                none
% 3.71/0.99  --bmc1_ucm_max_lemma_size               10
% 3.71/0.99  
% 3.71/0.99  ------ AIG Options
% 3.71/0.99  
% 3.71/0.99  --aig_mode                              false
% 3.71/0.99  
% 3.71/0.99  ------ Instantiation Options
% 3.71/0.99  
% 3.71/0.99  --instantiation_flag                    true
% 3.71/0.99  --inst_sos_flag                         false
% 3.71/0.99  --inst_sos_phase                        true
% 3.71/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.71/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.71/0.99  --inst_lit_sel_side                     none
% 3.71/0.99  --inst_solver_per_active                1400
% 3.71/0.99  --inst_solver_calls_frac                1.
% 3.71/0.99  --inst_passive_queue_type               priority_queues
% 3.71/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.71/0.99  --inst_passive_queues_freq              [25;2]
% 3.71/0.99  --inst_dismatching                      true
% 3.71/0.99  --inst_eager_unprocessed_to_passive     true
% 3.71/0.99  --inst_prop_sim_given                   true
% 3.71/0.99  --inst_prop_sim_new                     false
% 3.71/0.99  --inst_subs_new                         false
% 3.71/0.99  --inst_eq_res_simp                      false
% 3.71/0.99  --inst_subs_given                       false
% 3.71/0.99  --inst_orphan_elimination               true
% 3.71/0.99  --inst_learning_loop_flag               true
% 3.71/0.99  --inst_learning_start                   3000
% 3.71/0.99  --inst_learning_factor                  2
% 3.71/0.99  --inst_start_prop_sim_after_learn       3
% 3.71/0.99  --inst_sel_renew                        solver
% 3.71/0.99  --inst_lit_activity_flag                true
% 3.71/0.99  --inst_restr_to_given                   false
% 3.71/0.99  --inst_activity_threshold               500
% 3.71/0.99  --inst_out_proof                        true
% 3.71/0.99  
% 3.71/0.99  ------ Resolution Options
% 3.71/0.99  
% 3.71/0.99  --resolution_flag                       false
% 3.71/0.99  --res_lit_sel                           adaptive
% 3.71/0.99  --res_lit_sel_side                      none
% 3.71/0.99  --res_ordering                          kbo
% 3.71/0.99  --res_to_prop_solver                    active
% 3.71/0.99  --res_prop_simpl_new                    false
% 3.71/0.99  --res_prop_simpl_given                  true
% 3.71/0.99  --res_passive_queue_type                priority_queues
% 3.71/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.71/0.99  --res_passive_queues_freq               [15;5]
% 3.71/0.99  --res_forward_subs                      full
% 3.71/0.99  --res_backward_subs                     full
% 3.71/0.99  --res_forward_subs_resolution           true
% 3.71/0.99  --res_backward_subs_resolution          true
% 3.71/0.99  --res_orphan_elimination                true
% 3.71/0.99  --res_time_limit                        2.
% 3.71/0.99  --res_out_proof                         true
% 3.71/0.99  
% 3.71/0.99  ------ Superposition Options
% 3.71/0.99  
% 3.71/0.99  --superposition_flag                    true
% 3.71/0.99  --sup_passive_queue_type                priority_queues
% 3.71/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.71/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.71/0.99  --demod_completeness_check              fast
% 3.71/0.99  --demod_use_ground                      true
% 3.71/0.99  --sup_to_prop_solver                    passive
% 3.71/0.99  --sup_prop_simpl_new                    true
% 3.71/0.99  --sup_prop_simpl_given                  true
% 3.71/0.99  --sup_fun_splitting                     false
% 3.71/0.99  --sup_smt_interval                      50000
% 3.71/0.99  
% 3.71/0.99  ------ Superposition Simplification Setup
% 3.71/0.99  
% 3.71/0.99  --sup_indices_passive                   []
% 3.71/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.71/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.71/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.99  --sup_full_bw                           [BwDemod]
% 3.71/0.99  --sup_immed_triv                        [TrivRules]
% 3.71/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.71/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.99  --sup_immed_bw_main                     []
% 3.71/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.71/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.71/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.71/0.99  
% 3.71/0.99  ------ Combination Options
% 3.71/0.99  
% 3.71/0.99  --comb_res_mult                         3
% 3.71/0.99  --comb_sup_mult                         2
% 3.71/0.99  --comb_inst_mult                        10
% 3.71/0.99  
% 3.71/0.99  ------ Debug Options
% 3.71/0.99  
% 3.71/0.99  --dbg_backtrace                         false
% 3.71/0.99  --dbg_dump_prop_clauses                 false
% 3.71/0.99  --dbg_dump_prop_clauses_file            -
% 3.71/0.99  --dbg_out_stat                          false
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  ------ Proving...
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  % SZS status Theorem for theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  fof(f30,conjecture,(
% 3.71/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f31,negated_conjecture,(
% 3.71/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.71/0.99    inference(negated_conjecture,[],[f30])).
% 3.71/0.99  
% 3.71/0.99  fof(f70,plain,(
% 3.71/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.71/0.99    inference(ennf_transformation,[],[f31])).
% 3.71/0.99  
% 3.71/0.99  fof(f71,plain,(
% 3.71/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.71/0.99    inference(flattening,[],[f70])).
% 3.71/0.99  
% 3.71/0.99  fof(f81,plain,(
% 3.71/0.99    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f80,plain,(
% 3.71/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f79,plain,(
% 3.71/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f82,plain,(
% 3.71/0.99    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f71,f81,f80,f79])).
% 3.71/0.99  
% 3.71/0.99  fof(f136,plain,(
% 3.71/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.71/0.99    inference(cnf_transformation,[],[f82])).
% 3.71/0.99  
% 3.71/0.99  fof(f26,axiom,(
% 3.71/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f63,plain,(
% 3.71/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.71/0.99    inference(ennf_transformation,[],[f26])).
% 3.71/0.99  
% 3.71/0.99  fof(f127,plain,(
% 3.71/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f63])).
% 3.71/0.99  
% 3.71/0.99  fof(f133,plain,(
% 3.71/0.99    l1_struct_0(sK1)),
% 3.71/0.99    inference(cnf_transformation,[],[f82])).
% 3.71/0.99  
% 3.71/0.99  fof(f131,plain,(
% 3.71/0.99    l1_struct_0(sK0)),
% 3.71/0.99    inference(cnf_transformation,[],[f82])).
% 3.71/0.99  
% 3.71/0.99  fof(f18,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f50,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.99    inference(ennf_transformation,[],[f18])).
% 3.71/0.99  
% 3.71/0.99  fof(f112,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f50])).
% 3.71/0.99  
% 3.71/0.99  fof(f137,plain,(
% 3.71/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.71/0.99    inference(cnf_transformation,[],[f82])).
% 3.71/0.99  
% 3.71/0.99  fof(f5,axiom,(
% 3.71/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f33,plain,(
% 3.71/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.71/0.99    inference(ennf_transformation,[],[f5])).
% 3.71/0.99  
% 3.71/0.99  fof(f91,plain,(
% 3.71/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f33])).
% 3.71/0.99  
% 3.71/0.99  fof(f7,axiom,(
% 3.71/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f94,plain,(
% 3.71/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f7])).
% 3.71/0.99  
% 3.71/0.99  fof(f19,axiom,(
% 3.71/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f51,plain,(
% 3.71/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.71/0.99    inference(ennf_transformation,[],[f19])).
% 3.71/0.99  
% 3.71/0.99  fof(f52,plain,(
% 3.71/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.71/0.99    inference(flattening,[],[f51])).
% 3.71/0.99  
% 3.71/0.99  fof(f114,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f52])).
% 3.71/0.99  
% 3.71/0.99  fof(f28,axiom,(
% 3.71/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f66,plain,(
% 3.71/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.71/0.99    inference(ennf_transformation,[],[f28])).
% 3.71/0.99  
% 3.71/0.99  fof(f67,plain,(
% 3.71/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.71/0.99    inference(flattening,[],[f66])).
% 3.71/0.99  
% 3.71/0.99  fof(f129,plain,(
% 3.71/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f67])).
% 3.71/0.99  
% 3.71/0.99  fof(f132,plain,(
% 3.71/0.99    ~v2_struct_0(sK1)),
% 3.71/0.99    inference(cnf_transformation,[],[f82])).
% 3.71/0.99  
% 3.71/0.99  fof(f20,axiom,(
% 3.71/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f53,plain,(
% 3.71/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.71/0.99    inference(ennf_transformation,[],[f20])).
% 3.71/0.99  
% 3.71/0.99  fof(f54,plain,(
% 3.71/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.71/0.99    inference(flattening,[],[f53])).
% 3.71/0.99  
% 3.71/0.99  fof(f78,plain,(
% 3.71/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.71/0.99    inference(nnf_transformation,[],[f54])).
% 3.71/0.99  
% 3.71/0.99  fof(f115,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f78])).
% 3.71/0.99  
% 3.71/0.99  fof(f17,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f32,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.71/0.99    inference(pure_predicate_removal,[],[f17])).
% 3.71/0.99  
% 3.71/0.99  fof(f49,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/0.99    inference(ennf_transformation,[],[f32])).
% 3.71/0.99  
% 3.71/0.99  fof(f111,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/0.99    inference(cnf_transformation,[],[f49])).
% 3.71/0.99  
% 3.71/0.99  fof(f134,plain,(
% 3.71/0.99    v1_funct_1(sK2)),
% 3.71/0.99    inference(cnf_transformation,[],[f82])).
% 3.71/0.99  
% 3.71/0.99  fof(f135,plain,(
% 3.71/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.71/0.99    inference(cnf_transformation,[],[f82])).
% 3.71/0.99  
% 3.71/0.99  fof(f24,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f59,plain,(
% 3.71/0.99    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.71/0.99    inference(ennf_transformation,[],[f24])).
% 3.71/0.99  
% 3.71/0.99  fof(f60,plain,(
% 3.71/0.99    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.71/0.99    inference(flattening,[],[f59])).
% 3.71/0.99  
% 3.71/0.99  fof(f122,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f60])).
% 3.71/0.99  
% 3.71/0.99  fof(f138,plain,(
% 3.71/0.99    v2_funct_1(sK2)),
% 3.71/0.99    inference(cnf_transformation,[],[f82])).
% 3.71/0.99  
% 3.71/0.99  fof(f25,axiom,(
% 3.71/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f61,plain,(
% 3.71/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.71/0.99    inference(ennf_transformation,[],[f25])).
% 3.71/0.99  
% 3.71/0.99  fof(f62,plain,(
% 3.71/0.99    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.71/0.99    inference(flattening,[],[f61])).
% 3.71/0.99  
% 3.71/0.99  fof(f126,plain,(
% 3.71/0.99    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f62])).
% 3.71/0.99  
% 3.71/0.99  fof(f125,plain,(
% 3.71/0.99    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f62])).
% 3.71/0.99  
% 3.71/0.99  fof(f1,axiom,(
% 3.71/0.99    v1_xboole_0(k1_xboole_0)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f83,plain,(
% 3.71/0.99    v1_xboole_0(k1_xboole_0)),
% 3.71/0.99    inference(cnf_transformation,[],[f1])).
% 3.71/0.99  
% 3.71/0.99  fof(f16,axiom,(
% 3.71/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(X1,X0) & k1_relat_1(X0) = k2_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f47,plain,(
% 3.71/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.71/0.99    inference(ennf_transformation,[],[f16])).
% 3.71/0.99  
% 3.71/0.99  fof(f48,plain,(
% 3.71/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.71/0.99    inference(flattening,[],[f47])).
% 3.71/0.99  
% 3.71/0.99  fof(f110,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k6_relat_1(k2_relat_1(X0)) != k5_relat_1(X1,X0) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f48])).
% 3.71/0.99  
% 3.71/0.99  fof(f21,axiom,(
% 3.71/0.99    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f117,plain,(
% 3.71/0.99    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f21])).
% 3.71/0.99  
% 3.71/0.99  fof(f142,plain,(
% 3.71/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k1_relat_1(X0) != k2_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.99    inference(definition_unfolding,[],[f110,f117])).
% 3.71/0.99  
% 3.71/0.99  fof(f15,axiom,(
% 3.71/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f45,plain,(
% 3.71/0.99    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.71/0.99    inference(ennf_transformation,[],[f15])).
% 3.71/0.99  
% 3.71/0.99  fof(f46,plain,(
% 3.71/0.99    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.71/0.99    inference(flattening,[],[f45])).
% 3.71/0.99  
% 3.71/0.99  fof(f108,plain,(
% 3.71/0.99    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f46])).
% 3.71/0.99  
% 3.71/0.99  fof(f109,plain,(
% 3.71/0.99    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f46])).
% 3.71/0.99  
% 3.71/0.99  fof(f10,axiom,(
% 3.71/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f37,plain,(
% 3.71/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.71/0.99    inference(ennf_transformation,[],[f10])).
% 3.71/0.99  
% 3.71/0.99  fof(f38,plain,(
% 3.71/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.71/0.99    inference(flattening,[],[f37])).
% 3.71/0.99  
% 3.71/0.99  fof(f99,plain,(
% 3.71/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f38])).
% 3.71/0.99  
% 3.71/0.99  fof(f98,plain,(
% 3.71/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f38])).
% 3.71/0.99  
% 3.71/0.99  fof(f29,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f68,plain,(
% 3.71/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.71/0.99    inference(ennf_transformation,[],[f29])).
% 3.71/0.99  
% 3.71/0.99  fof(f69,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.71/0.99    inference(flattening,[],[f68])).
% 3.71/0.99  
% 3.71/0.99  fof(f130,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f69])).
% 3.71/0.99  
% 3.71/0.99  fof(f12,axiom,(
% 3.71/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f39,plain,(
% 3.71/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.71/0.99    inference(ennf_transformation,[],[f12])).
% 3.71/0.99  
% 3.71/0.99  fof(f40,plain,(
% 3.71/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.71/0.99    inference(flattening,[],[f39])).
% 3.71/0.99  
% 3.71/0.99  fof(f104,plain,(
% 3.71/0.99    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f40])).
% 3.71/0.99  
% 3.71/0.99  fof(f23,axiom,(
% 3.71/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f57,plain,(
% 3.71/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.71/0.99    inference(ennf_transformation,[],[f23])).
% 3.71/0.99  
% 3.71/0.99  fof(f58,plain,(
% 3.71/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.71/0.99    inference(flattening,[],[f57])).
% 3.71/0.99  
% 3.71/0.99  fof(f121,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f58])).
% 3.71/0.99  
% 3.71/0.99  fof(f120,plain,(
% 3.71/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f58])).
% 3.71/0.99  
% 3.71/0.99  fof(f22,axiom,(
% 3.71/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f55,plain,(
% 3.71/0.99    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.71/0.99    inference(ennf_transformation,[],[f22])).
% 3.71/0.99  
% 3.71/0.99  fof(f56,plain,(
% 3.71/0.99    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.71/0.99    inference(flattening,[],[f55])).
% 3.71/0.99  
% 3.71/0.99  fof(f118,plain,(
% 3.71/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f56])).
% 3.71/0.99  
% 3.71/0.99  fof(f139,plain,(
% 3.71/0.99    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.71/0.99    inference(cnf_transformation,[],[f82])).
% 3.71/0.99  
% 3.71/0.99  cnf(c_50,negated_conjecture,
% 3.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.71/0.99      inference(cnf_transformation,[],[f136]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1572,plain,
% 3.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_43,plain,
% 3.71/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f127]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_53,negated_conjecture,
% 3.71/0.99      ( l1_struct_0(sK1) ),
% 3.71/0.99      inference(cnf_transformation,[],[f133]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_613,plain,
% 3.71/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.71/0.99      inference(resolution_lifted,[status(thm)],[c_43,c_53]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_614,plain,
% 3.71/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.71/0.99      inference(unflattening,[status(thm)],[c_613]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_55,negated_conjecture,
% 3.71/0.99      ( l1_struct_0(sK0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f131]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_618,plain,
% 3.71/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.71/0.99      inference(resolution_lifted,[status(thm)],[c_43,c_55]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_619,plain,
% 3.71/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.71/0.99      inference(unflattening,[status(thm)],[c_618]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1635,plain,
% 3.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.71/0.99      inference(light_normalisation,[status(thm)],[c_1572,c_614,c_619]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_29,plain,
% 3.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f112]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1582,plain,
% 3.71/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.71/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3024,plain,
% 3.71/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_1635,c_1582]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_49,negated_conjecture,
% 3.71/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.71/0.99      inference(cnf_transformation,[],[f137]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1632,plain,
% 3.71/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.71/0.99      inference(light_normalisation,[status(thm)],[c_49,c_614,c_619]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3201,plain,
% 3.71/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_3024,c_1632]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3210,plain,
% 3.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_3201,c_1635]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_8,plain,
% 3.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.71/0.99      | ~ v1_relat_1(X1)
% 3.71/0.99      | v1_relat_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1598,plain,
% 3.71/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.71/0.99      | v1_relat_1(X1) != iProver_top
% 3.71/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3782,plain,
% 3.71/0.99      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
% 3.71/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_3210,c_1598]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_61,plain,
% 3.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2000,plain,
% 3.71/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | v1_relat_1(X0)
% 3.71/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_8]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2495,plain,
% 3.71/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.71/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 3.71/0.99      | v1_relat_1(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_2000]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2496,plain,
% 3.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.71/0.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 3.71/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2495]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_11,plain,
% 3.71/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.71/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2613,plain,
% 3.71/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_11]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2614,plain,
% 3.71/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2613]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4174,plain,
% 3.71/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_3782,c_61,c_2496,c_2614]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_30,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/0.99      | v1_partfun1(X0,X1)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | v1_xboole_0(X2) ),
% 3.71/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_45,plain,
% 3.71/0.99      ( v2_struct_0(X0)
% 3.71/0.99      | ~ l1_struct_0(X0)
% 3.71/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.71/0.99      inference(cnf_transformation,[],[f129]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_54,negated_conjecture,
% 3.71/0.99      ( ~ v2_struct_0(sK1) ),
% 3.71/0.99      inference(cnf_transformation,[],[f132]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_600,plain,
% 3.71/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 3.71/0.99      inference(resolution_lifted,[status(thm)],[c_45,c_54]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_601,plain,
% 3.71/0.99      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.71/0.99      inference(unflattening,[status(thm)],[c_600]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_603,plain,
% 3.71/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_601,c_53]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_629,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/0.99      | v1_partfun1(X0,X1)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | u1_struct_0(sK1) != X2 ),
% 3.71/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_603]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_630,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.71/0.99      | v1_partfun1(X0,X1)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.71/0.99      | ~ v1_funct_1(X0) ),
% 3.71/0.99      inference(unflattening,[status(thm)],[c_629]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_33,plain,
% 3.71/0.99      ( ~ v1_partfun1(X0,X1)
% 3.71/0.99      | ~ v4_relat_1(X0,X1)
% 3.71/0.99      | ~ v1_relat_1(X0)
% 3.71/0.99      | k1_relat_1(X0) = X1 ),
% 3.71/0.99      inference(cnf_transformation,[],[f115]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_653,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.71/0.99      | ~ v4_relat_1(X0,X1)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | ~ v1_relat_1(X0)
% 3.71/0.99      | k1_relat_1(X0) = X1 ),
% 3.71/0.99      inference(resolution,[status(thm)],[c_630,c_33]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_28,plain,
% 3.71/0.99      ( v4_relat_1(X0,X1)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.71/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_669,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | ~ v1_relat_1(X0)
% 3.71/0.99      | k1_relat_1(X0) = X1 ),
% 3.71/0.99      inference(forward_subsumption_resolution,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_653,c_28]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1567,plain,
% 3.71/0.99      ( k1_relat_1(X0) = X1
% 3.71/0.99      | v1_funct_2(X0,X1,u1_struct_0(sK1)) != iProver_top
% 3.71/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) != iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top
% 3.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1749,plain,
% 3.71/0.99      ( k1_relat_1(X0) = X1
% 3.71/0.99      | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
% 3.71/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top
% 3.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.99      inference(light_normalisation,[status(thm)],[c_1567,c_614]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2398,plain,
% 3.71/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.71/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.71/0.99      | v1_funct_1(sK2) != iProver_top
% 3.71/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_1635,c_1749]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_52,negated_conjecture,
% 3.71/0.99      ( v1_funct_1(sK2) ),
% 3.71/0.99      inference(cnf_transformation,[],[f134]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_59,plain,
% 3.71/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_51,negated_conjecture,
% 3.71/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.71/0.99      inference(cnf_transformation,[],[f135]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1571,plain,
% 3.71/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1629,plain,
% 3.71/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.71/0.99      inference(light_normalisation,[status(thm)],[c_1571,c_614,c_619]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2457,plain,
% 3.71/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.71/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_2398,c_59,c_1629]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4180,plain,
% 3.71/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_4174,c_2457]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3204,plain,
% 3.71/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_3201,c_3024]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4189,plain,
% 3.71/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_4180,c_3204]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_39,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ v2_funct_1(X0)
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.71/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.71/0.99      | k1_xboole_0 = X2 ),
% 3.71/0.99      inference(cnf_transformation,[],[f122]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1577,plain,
% 3.71/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.71/0.99      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 3.71/0.99      | k1_xboole_0 = X1
% 3.71/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.71/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.71/0.99      | v2_funct_1(X2) != iProver_top
% 3.71/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4992,plain,
% 3.71/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2))
% 3.71/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 3.71/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.71/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.71/0.99      | v2_funct_1(sK2) != iProver_top
% 3.71/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_4189,c_1577]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_48,negated_conjecture,
% 3.71/0.99      ( v2_funct_1(sK2) ),
% 3.71/0.99      inference(cnf_transformation,[],[f138]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_62,plain,
% 3.71/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_40,plain,
% 3.71/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | ~ v1_relat_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f126]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2051,plain,
% 3.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.71/0.99      | ~ v1_funct_1(sK2)
% 3.71/0.99      | ~ v1_relat_1(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_40]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2052,plain,
% 3.71/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 3.71/0.99      | v1_funct_1(sK2) != iProver_top
% 3.71/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2051]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_41,plain,
% 3.71/0.99      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | ~ v1_relat_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f125]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2054,plain,
% 3.71/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.71/0.99      | ~ v1_funct_1(sK2)
% 3.71/0.99      | ~ v1_relat_1(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_41]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2055,plain,
% 3.71/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
% 3.71/0.99      | v1_funct_1(sK2) != iProver_top
% 3.71/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_2054]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_0,plain,
% 3.71/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f83]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_625,plain,
% 3.71/0.99      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 3.71/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_603]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1611,plain,
% 3.71/0.99      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_614,c_625]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3212,plain,
% 3.71/0.99      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_3201,c_1611]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_10036,plain,
% 3.71/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k1_relat_1(sK2)) ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_4992,c_59,c_61,c_62,c_2052,c_2055,c_2496,c_2614,
% 3.71/0.99                 c_3212]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_27,plain,
% 3.71/0.99      ( ~ v2_funct_1(X0)
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | ~ v1_funct_1(X1)
% 3.71/0.99      | ~ v1_relat_1(X0)
% 3.71/0.99      | ~ v1_relat_1(X1)
% 3.71/0.99      | k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
% 3.71/0.99      | k2_funct_1(X0) = X1
% 3.71/0.99      | k2_relat_1(X1) != k1_relat_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f142]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1583,plain,
% 3.71/0.99      ( k5_relat_1(X0,X1) != k6_partfun1(k2_relat_1(X1))
% 3.71/0.99      | k2_funct_1(X1) = X0
% 3.71/0.99      | k2_relat_1(X0) != k1_relat_1(X1)
% 3.71/0.99      | v2_funct_1(X1) != iProver_top
% 3.71/0.99      | v1_funct_1(X1) != iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top
% 3.71/0.99      | v1_relat_1(X1) != iProver_top
% 3.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_10039,plain,
% 3.71/0.99      ( k6_partfun1(k2_relat_1(k2_funct_1(sK2))) != k6_partfun1(k1_relat_1(sK2))
% 3.71/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.71/0.99      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.71/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.71/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.71/0.99      | v1_funct_1(sK2) != iProver_top
% 3.71/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.71/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_10036,c_1583]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1573,plain,
% 3.71/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_26,plain,
% 3.71/0.99      ( ~ v2_funct_1(X0)
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | ~ v1_relat_1(X0)
% 3.71/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1584,plain,
% 3.71/0.99      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.71/0.99      | v2_funct_1(X0) != iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top
% 3.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4754,plain,
% 3.71/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.71/0.99      | v1_funct_1(sK2) != iProver_top
% 3.71/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_1573,c_1584]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2048,plain,
% 3.71/0.99      ( ~ v2_funct_1(sK2)
% 3.71/0.99      | ~ v1_funct_1(sK2)
% 3.71/0.99      | ~ v1_relat_1(sK2)
% 3.71/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4787,plain,
% 3.71/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_4754,c_52,c_50,c_48,c_2048,c_2495,c_2613]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_25,plain,
% 3.71/0.99      ( ~ v2_funct_1(X0)
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | ~ v1_relat_1(X0)
% 3.71/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1585,plain,
% 3.71/0.99      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.71/0.99      | v2_funct_1(X0) != iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top
% 3.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_5454,plain,
% 3.71/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.71/0.99      | v1_funct_1(sK2) != iProver_top
% 3.71/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_1573,c_1585]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2040,plain,
% 3.71/0.99      ( ~ v2_funct_1(sK2)
% 3.71/0.99      | ~ v1_funct_1(sK2)
% 3.71/0.99      | ~ v1_relat_1(sK2)
% 3.71/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_25]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_5851,plain,
% 3.71/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_5454,c_52,c_50,c_48,c_2040,c_2495,c_2613]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_10040,plain,
% 3.71/0.99      ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
% 3.71/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.71/0.99      | k2_relat_1(sK2) != k2_relat_1(sK2)
% 3.71/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.71/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.71/0.99      | v1_funct_1(sK2) != iProver_top
% 3.71/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.71/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.71/0.99      inference(light_normalisation,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_10039,c_4787,c_5851]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_10041,plain,
% 3.71/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.71/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.71/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.71/0.99      | v1_funct_1(sK2) != iProver_top
% 3.71/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.71/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.71/0.99      inference(equality_resolution_simp,[status(thm)],[c_10040]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1576,plain,
% 3.71/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top
% 3.71/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4790,plain,
% 3.71/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top
% 3.71/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.71/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_4787,c_1576]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_15,plain,
% 3.71/0.99      ( ~ v1_funct_1(X0)
% 3.71/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.71/0.99      | ~ v1_relat_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1992,plain,
% 3.71/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 3.71/0.99      | ~ v1_funct_1(sK2)
% 3.71/0.99      | ~ v1_relat_1(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1993,plain,
% 3.71/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.71/0.99      | v1_funct_1(sK2) != iProver_top
% 3.71/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1992]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_16,plain,
% 3.71/0.99      ( ~ v1_funct_1(X0)
% 3.71/0.99      | ~ v1_relat_1(X0)
% 3.71/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 3.71/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1995,plain,
% 3.71/0.99      ( ~ v1_funct_1(sK2)
% 3.71/0.99      | v1_relat_1(k2_funct_1(sK2))
% 3.71/0.99      | ~ v1_relat_1(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_16]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1996,plain,
% 3.71/0.99      ( v1_funct_1(sK2) != iProver_top
% 3.71/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.71/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_1995]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4887,plain,
% 3.71/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) = iProver_top ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_4790,c_59,c_61,c_1993,c_1996,c_2496,c_2614]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4893,plain,
% 3.71/0.99      ( k2_relset_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_4887,c_1582]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_5855,plain,
% 3.71/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_5851,c_4893]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_46,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ v2_funct_1(X0)
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.71/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.71/0.99      inference(cnf_transformation,[],[f130]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1574,plain,
% 3.71/0.99      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 3.71/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.71/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.71/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.71/0.99      | v2_funct_1(X2) != iProver_top
% 3.71/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_5997,plain,
% 3.71/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.71/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.71/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.71/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.71/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_5855,c_1574]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_19,plain,
% 3.71/0.99      ( ~ v2_funct_1(X0)
% 3.71/0.99      | v2_funct_1(k2_funct_1(X0))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | ~ v1_relat_1(X0) ),
% 3.71/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2015,plain,
% 3.71/0.99      ( v2_funct_1(k2_funct_1(sK2))
% 3.71/0.99      | ~ v2_funct_1(sK2)
% 3.71/0.99      | ~ v1_funct_1(sK2)
% 3.71/0.99      | ~ v1_relat_1(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_35,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.71/0.99      | ~ v2_funct_1(X0)
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.71/0.99      inference(cnf_transformation,[],[f121]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2170,plain,
% 3.71/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.71/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.71/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/0.99      | ~ v2_funct_1(sK2)
% 3.71/0.99      | ~ v1_funct_1(sK2)
% 3.71/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_35]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3081,plain,
% 3.71/0.99      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.71/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
% 3.71/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.71/0.99      | ~ v2_funct_1(sK2)
% 3.71/0.99      | ~ v1_funct_1(sK2)
% 3.71/0.99      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_2170]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_36,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ v2_funct_1(X0)
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.71/0.99      inference(cnf_transformation,[],[f120]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2180,plain,
% 3.71/0.99      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.71/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 3.71/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.71/0.99      | ~ v2_funct_1(sK2)
% 3.71/0.99      | ~ v1_funct_1(sK2)
% 3.71/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_36]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3089,plain,
% 3.71/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
% 3.71/0.99      | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.71/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.71/0.99      | ~ v2_funct_1(sK2)
% 3.71/0.99      | ~ v1_funct_1(sK2)
% 3.71/0.99      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_2180]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3100,plain,
% 3.71/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.71/0.99      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_29]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2259,plain,
% 3.71/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.71/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/0.99      | ~ v2_funct_1(k2_funct_1(sK2))
% 3.71/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.71/0.99      | k2_tops_2(X0,X1,k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.71/0.99      | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_46]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4615,plain,
% 3.71/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
% 3.71/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
% 3.71/0.99      | ~ v2_funct_1(k2_funct_1(sK2))
% 3.71/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.71/0.99      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.71/0.99      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 3.71/0.99      inference(instantiation,[status(thm)],[c_2259]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_8738,plain,
% 3.71/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_5997,c_52,c_50,c_48,c_1992,c_2015,c_2051,c_2054,
% 3.71/0.99                 c_2495,c_2613,c_3081,c_3089,c_3100,c_4615,c_5855]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2507,plain,
% 3.71/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.71/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.71/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.71/0.99      | v2_funct_1(sK2) != iProver_top
% 3.71/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.71/0.99      inference(superposition,[status(thm)],[c_1632,c_1574]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2601,plain,
% 3.71/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.71/0.99      inference(global_propositional_subsumption,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_2507,c_59,c_62,c_1629,c_1635]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_34,plain,
% 3.71/0.99      ( r2_funct_2(X0,X1,X2,X2)
% 3.71/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.71/0.99      | ~ v1_funct_2(X3,X0,X1)
% 3.71/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/0.99      | ~ v1_funct_1(X2)
% 3.71/0.99      | ~ v1_funct_1(X3) ),
% 3.71/0.99      inference(cnf_transformation,[],[f118]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_47,negated_conjecture,
% 3.71/0.99      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.71/0.99      inference(cnf_transformation,[],[f139]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_564,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/0.99      | ~ v1_funct_2(X3,X1,X2)
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | ~ v1_funct_1(X3)
% 3.71/0.99      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 3.71/0.99      | u1_struct_0(sK1) != X2
% 3.71/0.99      | u1_struct_0(sK0) != X1
% 3.71/0.99      | sK2 != X0 ),
% 3.71/0.99      inference(resolution_lifted,[status(thm)],[c_34,c_47]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_565,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.71/0.99      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.71/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.71/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.71/0.99      inference(unflattening,[status(thm)],[c_564]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_938,plain,
% 3.71/0.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.71/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.71/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.71/0.99      | sP0_iProver_split
% 3.71/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.71/0.99      inference(splitting,
% 3.71/0.99                [splitting(split),new_symbols(definition,[])],
% 3.71/0.99                [c_565]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1568,plain,
% 3.71/0.99      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.71/0.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.71/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.71/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 3.71/0.99      | sP0_iProver_split = iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_938]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1880,plain,
% 3.71/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.71/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.71/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.71/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 3.71/0.99      | sP0_iProver_split = iProver_top ),
% 3.71/0.99      inference(light_normalisation,[status(thm)],[c_1568,c_614,c_619]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_937,plain,
% 3.71/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.71/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.71/0.99      | ~ v1_funct_1(X0)
% 3.71/0.99      | ~ sP0_iProver_split ),
% 3.71/0.99      inference(splitting,
% 3.71/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.71/0.99                [c_565]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1569,plain,
% 3.71/0.99      ( v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.71/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top
% 3.71/0.99      | sP0_iProver_split != iProver_top ),
% 3.71/0.99      inference(predicate_to_equality,[status(thm)],[c_937]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1730,plain,
% 3.71/0.99      ( v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.71/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.71/0.99      | v1_funct_1(X0) != iProver_top
% 3.71/0.99      | sP0_iProver_split != iProver_top ),
% 3.71/0.99      inference(light_normalisation,[status(thm)],[c_1569,c_614,c_619]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_1886,plain,
% 3.71/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.71/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.71/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.71/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.71/0.99      inference(forward_subsumption_resolution,
% 3.71/0.99                [status(thm)],
% 3.71/0.99                [c_1880,c_1730]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2604,plain,
% 3.71/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 3.71/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.71/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.71/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_2601,c_1886]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_3205,plain,
% 3.71/0.99      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 3.71/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.71/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.71/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_3201,c_2604]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_4186,plain,
% 3.71/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 3.71/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.71/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.71/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_4180,c_3205]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_8741,plain,
% 3.71/0.99      ( k2_funct_1(k2_funct_1(sK2)) != sK2
% 3.71/0.99      | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.71/0.99      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.71/0.99      | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
% 3.71/0.99      inference(demodulation,[status(thm)],[c_8738,c_4186]) ).
% 3.71/0.99  
% 3.71/0.99  cnf(c_2260,plain,
% 3.71/0.99      ( v1_funct_2(k2_funct_1(k2_funct_1(sK2)),X0,X1)
% 3.71/0.99      | ~ v1_funct_2(k2_funct_1(sK2),X1,X0)
% 3.71/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.71/0.99      | ~ v2_funct_1(k2_funct_1(sK2))
% 3.71/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.71/1.00      | k2_relset_1(X1,X0,k2_funct_1(sK2)) != X0 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_36]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4620,plain,
% 3.71/1.00      ( v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2))
% 3.71/1.00      | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
% 3.71/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
% 3.71/1.00      | ~ v2_funct_1(k2_funct_1(sK2))
% 3.71/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.71/1.00      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2260]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4621,plain,
% 3.71/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.71/1.00      | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
% 3.71/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.71/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_4620]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2261,plain,
% 3.71/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.71/1.00      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.71/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/1.00      | ~ v2_funct_1(k2_funct_1(sK2))
% 3.71/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.71/1.00      | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_35]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4614,plain,
% 3.71/1.00      ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
% 3.71/1.00      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.71/1.00      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
% 3.71/1.00      | ~ v2_funct_1(k2_funct_1(sK2))
% 3.71/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.71/1.00      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_2261]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4618,plain,
% 3.71/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.71/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.71/1.00      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.71/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_4614]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3090,plain,
% 3.71/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 3.71/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 3.71/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.71/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.71/1.00      | v2_funct_1(sK2) != iProver_top
% 3.71/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_3089]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3085,plain,
% 3.71/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 3.71/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 3.71/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.71/1.00      | v2_funct_1(sK2) != iProver_top
% 3.71/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_3081]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2208,plain,
% 3.71/1.00      ( v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
% 3.71/1.00      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.71/1.00      | ~ v1_relat_1(k2_funct_1(sK2)) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_15]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2214,plain,
% 3.71/1.00      ( v1_funct_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.71/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_2208]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2016,plain,
% 3.71/1.00      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.71/1.00      | v2_funct_1(sK2) != iProver_top
% 3.71/1.00      | v1_funct_1(sK2) != iProver_top
% 3.71/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_2015]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(contradiction,plain,
% 3.71/1.00      ( $false ),
% 3.71/1.00      inference(minisat,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_10041,c_8741,c_5855,c_4621,c_4618,c_3100,c_3090,
% 3.71/1.00                 c_3085,c_2614,c_2613,c_2496,c_2495,c_2214,c_2055,c_2052,
% 3.71/1.00                 c_2051,c_2016,c_1996,c_1993,c_62,c_61,c_50,c_59,c_52]) ).
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.71/1.00  
% 3.71/1.00  ------                               Statistics
% 3.71/1.00  
% 3.71/1.00  ------ General
% 3.71/1.00  
% 3.71/1.00  abstr_ref_over_cycles:                  0
% 3.71/1.00  abstr_ref_under_cycles:                 0
% 3.71/1.00  gc_basic_clause_elim:                   0
% 3.71/1.00  forced_gc_time:                         0
% 3.71/1.00  parsing_time:                           0.043
% 3.71/1.00  unif_index_cands_time:                  0.
% 3.71/1.00  unif_index_add_time:                    0.
% 3.71/1.00  orderings_time:                         0.
% 3.71/1.00  out_proof_time:                         0.015
% 3.71/1.00  total_time:                             0.398
% 3.71/1.00  num_of_symbols:                         60
% 3.71/1.00  num_of_terms:                           9584
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing
% 3.71/1.00  
% 3.71/1.00  num_of_splits:                          1
% 3.71/1.00  num_of_split_atoms:                     1
% 3.71/1.00  num_of_reused_defs:                     0
% 3.71/1.00  num_eq_ax_congr_red:                    5
% 3.71/1.00  num_of_sem_filtered_clauses:            1
% 3.71/1.00  num_of_subtypes:                        0
% 3.71/1.00  monotx_restored_types:                  0
% 3.71/1.00  sat_num_of_epr_types:                   0
% 3.71/1.00  sat_num_of_non_cyclic_types:            0
% 3.71/1.00  sat_guarded_non_collapsed_types:        0
% 3.71/1.00  num_pure_diseq_elim:                    0
% 3.71/1.00  simp_replaced_by:                       0
% 3.71/1.00  res_preprocessed:                       218
% 3.71/1.00  prep_upred:                             0
% 3.71/1.00  prep_unflattend:                        9
% 3.71/1.00  smt_new_axioms:                         0
% 3.71/1.00  pred_elim_cands:                        6
% 3.71/1.00  pred_elim:                              6
% 3.71/1.00  pred_elim_cl:                           9
% 3.71/1.00  pred_elim_cycles:                       8
% 3.71/1.00  merged_defs:                            0
% 3.71/1.00  merged_defs_ncl:                        0
% 3.71/1.00  bin_hyper_res:                          0
% 3.71/1.00  prep_cycles:                            4
% 3.71/1.00  pred_elim_time:                         0.005
% 3.71/1.00  splitting_time:                         0.
% 3.71/1.00  sem_filter_time:                        0.
% 3.71/1.00  monotx_time:                            0.001
% 3.71/1.00  subtype_inf_time:                       0.
% 3.71/1.00  
% 3.71/1.00  ------ Problem properties
% 3.71/1.00  
% 3.71/1.00  clauses:                                43
% 3.71/1.00  conjectures:                            5
% 3.71/1.00  epr:                                    5
% 3.71/1.00  horn:                                   40
% 3.71/1.00  ground:                                 9
% 3.71/1.00  unary:                                  15
% 3.71/1.00  binary:                                 2
% 3.71/1.00  lits:                                   140
% 3.71/1.00  lits_eq:                                37
% 3.71/1.00  fd_pure:                                0
% 3.71/1.00  fd_pseudo:                              0
% 3.71/1.00  fd_cond:                                3
% 3.71/1.00  fd_pseudo_cond:                         3
% 3.71/1.00  ac_symbols:                             0
% 3.71/1.00  
% 3.71/1.00  ------ Propositional Solver
% 3.71/1.00  
% 3.71/1.00  prop_solver_calls:                      27
% 3.71/1.00  prop_fast_solver_calls:                 1922
% 3.71/1.00  smt_solver_calls:                       0
% 3.71/1.00  smt_fast_solver_calls:                  0
% 3.71/1.00  prop_num_of_clauses:                    3854
% 3.71/1.00  prop_preprocess_simplified:             12082
% 3.71/1.00  prop_fo_subsumed:                       136
% 3.71/1.00  prop_solver_time:                       0.
% 3.71/1.00  smt_solver_time:                        0.
% 3.71/1.00  smt_fast_solver_time:                   0.
% 3.71/1.00  prop_fast_solver_time:                  0.
% 3.71/1.00  prop_unsat_core_time:                   0.
% 3.71/1.00  
% 3.71/1.00  ------ QBF
% 3.71/1.00  
% 3.71/1.00  qbf_q_res:                              0
% 3.71/1.00  qbf_num_tautologies:                    0
% 3.71/1.00  qbf_prep_cycles:                        0
% 3.71/1.00  
% 3.71/1.00  ------ BMC1
% 3.71/1.00  
% 3.71/1.00  bmc1_current_bound:                     -1
% 3.71/1.00  bmc1_last_solved_bound:                 -1
% 3.71/1.00  bmc1_unsat_core_size:                   -1
% 3.71/1.00  bmc1_unsat_core_parents_size:           -1
% 3.71/1.00  bmc1_merge_next_fun:                    0
% 3.71/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.71/1.00  
% 3.71/1.00  ------ Instantiation
% 3.71/1.00  
% 3.71/1.00  inst_num_of_clauses:                    1387
% 3.71/1.00  inst_num_in_passive:                    509
% 3.71/1.00  inst_num_in_active:                     563
% 3.71/1.00  inst_num_in_unprocessed:                315
% 3.71/1.00  inst_num_of_loops:                      630
% 3.71/1.00  inst_num_of_learning_restarts:          0
% 3.71/1.00  inst_num_moves_active_passive:          65
% 3.71/1.00  inst_lit_activity:                      0
% 3.71/1.00  inst_lit_activity_moves:                0
% 3.71/1.00  inst_num_tautologies:                   0
% 3.71/1.00  inst_num_prop_implied:                  0
% 3.71/1.00  inst_num_existing_simplified:           0
% 3.71/1.00  inst_num_eq_res_simplified:             0
% 3.71/1.00  inst_num_child_elim:                    0
% 3.71/1.00  inst_num_of_dismatching_blockings:      225
% 3.71/1.00  inst_num_of_non_proper_insts:           1100
% 3.71/1.00  inst_num_of_duplicates:                 0
% 3.71/1.00  inst_inst_num_from_inst_to_res:         0
% 3.71/1.00  inst_dismatching_checking_time:         0.
% 3.71/1.00  
% 3.71/1.00  ------ Resolution
% 3.71/1.00  
% 3.71/1.00  res_num_of_clauses:                     0
% 3.71/1.00  res_num_in_passive:                     0
% 3.71/1.00  res_num_in_active:                      0
% 3.71/1.00  res_num_of_loops:                       222
% 3.71/1.00  res_forward_subset_subsumed:            60
% 3.71/1.00  res_backward_subset_subsumed:           0
% 3.71/1.00  res_forward_subsumed:                   0
% 3.71/1.00  res_backward_subsumed:                  0
% 3.71/1.00  res_forward_subsumption_resolution:     1
% 3.71/1.00  res_backward_subsumption_resolution:    0
% 3.71/1.00  res_clause_to_clause_subsumption:       305
% 3.71/1.00  res_orphan_elimination:                 0
% 3.71/1.00  res_tautology_del:                      34
% 3.71/1.00  res_num_eq_res_simplified:              0
% 3.71/1.00  res_num_sel_changes:                    0
% 3.71/1.00  res_moves_from_active_to_pass:          0
% 3.71/1.00  
% 3.71/1.00  ------ Superposition
% 3.71/1.00  
% 3.71/1.00  sup_time_total:                         0.
% 3.71/1.00  sup_time_generating:                    0.
% 3.71/1.00  sup_time_sim_full:                      0.
% 3.71/1.00  sup_time_sim_immed:                     0.
% 3.71/1.00  
% 3.71/1.00  sup_num_of_clauses:                     137
% 3.71/1.00  sup_num_in_active:                      95
% 3.71/1.00  sup_num_in_passive:                     42
% 3.71/1.00  sup_num_of_loops:                       124
% 3.71/1.00  sup_fw_superposition:                   83
% 3.71/1.00  sup_bw_superposition:                   88
% 3.71/1.00  sup_immediate_simplified:               69
% 3.71/1.00  sup_given_eliminated:                   0
% 3.71/1.00  comparisons_done:                       0
% 3.71/1.00  comparisons_avoided:                    0
% 3.71/1.00  
% 3.71/1.00  ------ Simplifications
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  sim_fw_subset_subsumed:                 28
% 3.71/1.00  sim_bw_subset_subsumed:                 5
% 3.71/1.00  sim_fw_subsumed:                        7
% 3.71/1.00  sim_bw_subsumed:                        0
% 3.71/1.00  sim_fw_subsumption_res:                 1
% 3.71/1.00  sim_bw_subsumption_res:                 0
% 3.71/1.00  sim_tautology_del:                      1
% 3.71/1.00  sim_eq_tautology_del:                   17
% 3.71/1.00  sim_eq_res_simp:                        2
% 3.71/1.00  sim_fw_demodulated:                     1
% 3.71/1.00  sim_bw_demodulated:                     30
% 3.71/1.00  sim_light_normalised:                   45
% 3.71/1.00  sim_joinable_taut:                      0
% 3.71/1.00  sim_joinable_simp:                      0
% 3.71/1.00  sim_ac_normalised:                      0
% 3.71/1.00  sim_smt_subsumption:                    0
% 3.71/1.00  
%------------------------------------------------------------------------------
