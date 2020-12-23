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

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  215 (1832 expanded)
%              Number of clauses        :  131 ( 513 expanded)
%              Number of leaves         :   21 ( 534 expanded)
%              Depth                    :   24
%              Number of atoms          :  797 (11960 expanded)
%              Number of equality atoms :  311 (2052 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
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

fof(f25,negated_conjecture,(
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
    inference(negated_conjecture,[],[f24])).

fof(f51,plain,(
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
    inference(ennf_transformation,[],[f25])).

fof(f52,plain,(
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
    inference(flattening,[],[f51])).

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,
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

fof(f61,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f52,f60,f59,f58])).

fof(f104,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f61])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f96,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f99,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f80,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f105,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

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

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f102,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f106,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f103,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f47])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f8,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f8])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f109,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f73,f86])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f87,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f107,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f53])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f78,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f44])).

fof(f95,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f18,axiom,(
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
    inference(ennf_transformation,[],[f18])).

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

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f76,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f82,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f77,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f94,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1605,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_33,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_42,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_537,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_42])).

cnf(c_538,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_537])).

cnf(c_44,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_542,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_44])).

cnf(c_543,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_542])).

cnf(c_1662,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1605,c_538,c_543])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1616,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2739,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_1616])).

cnf(c_19,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1618,plain,
    ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_7159,plain,
    ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2739,c_1618])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1614,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3489,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1662,c_1614])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1659,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_38,c_538,c_543])).

cnf(c_3741,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3489,c_1659])).

cnf(c_3744,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3741,c_3489])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1610,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_5033,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3744,c_1610])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_48,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_37,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_51,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_3749,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3741,c_1662])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1604,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_1656,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1604,c_538,c_543])).

cnf(c_3750,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3741,c_1656])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_34,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_510,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_34])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_528,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_510,c_43])).

cnf(c_529,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_531,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_529,c_42])).

cnf(c_1639,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_531,c_538])).

cnf(c_3751,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3741,c_1639])).

cnf(c_5512,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5033,c_48,c_51,c_3749,c_3750,c_3751])).

cnf(c_7186,plain,
    ( k1_relat_1(k6_partfun1(k2_struct_0(sK0))) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7159,c_5512])).

cnf(c_12,plain,
    ( k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_7187,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7186,c_12])).

cnf(c_7222,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7187,c_48,c_51])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1607,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_2538,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1659,c_1607])).

cnf(c_2759,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2538,c_48,c_51,c_1662,c_1656])).

cnf(c_24,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_36,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_549,plain,
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
    inference(resolution_lifted,[status(thm)],[c_24,c_36])).

cnf(c_550,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_549])).

cnf(c_851,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_550])).

cnf(c_1600,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_851])).

cnf(c_1858,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1600,c_538,c_543])).

cnf(c_850,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_550])).

cnf(c_1601,plain,
    ( v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_850])).

cnf(c_1785,plain,
    ( v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1601,c_538,c_543])).

cnf(c_1864,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1858,c_1785])).

cnf(c_2762,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2759,c_1864])).

cnf(c_3745,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3741,c_2762])).

cnf(c_7227,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7222,c_3745])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1629,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1620,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_6144,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2739,c_1620])).

cnf(c_1956,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_2043,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_6327,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6144,c_41,c_39,c_37,c_1956,c_2043])).

cnf(c_30,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1609,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6330,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6327,c_1609])).

cnf(c_50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_1957,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1956])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_14,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_236,plain,
    ( ~ v2_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_27,c_21,c_14])).

cnf(c_237,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_236])).

cnf(c_1602,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_237])).

cnf(c_2010,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1662,c_1602])).

cnf(c_15,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_2045,plain,
    ( v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_2052,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2045])).

cnf(c_6492,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6330,c_48,c_50,c_51,c_1957,c_2010,c_2052])).

cnf(c_16,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1621,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6266,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2739,c_1621])).

cnf(c_2044,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_6402,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6266,c_41,c_39,c_37,c_1956,c_2044])).

cnf(c_6498,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6492,c_6402])).

cnf(c_6506,plain,
    ( k2_relset_1(k2_relat_1(sK2),X0,k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6498,c_1614])).

cnf(c_6520,plain,
    ( k2_relset_1(k2_relat_1(sK2),X0,k2_funct_1(sK2)) = k1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6506,c_6402])).

cnf(c_6599,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1629,c_6520])).

cnf(c_6603,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_6599,c_1607])).

cnf(c_20,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1617,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5160,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2739,c_1617])).

cnf(c_2042,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_5505,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5160,c_41,c_39,c_37,c_1956,c_2042])).

cnf(c_6614,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6603,c_5505])).

cnf(c_13,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_2047,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_2048,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2047])).

cnf(c_31,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2038,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
    | ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2387,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2038])).

cnf(c_2389,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
    | r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2387])).

cnf(c_2388,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2391,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2388])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2027,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_3244,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2027])).

cnf(c_3245,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3244])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2022,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3249,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2022])).

cnf(c_3250,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3249])).

cnf(c_2039,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
    | ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_3252,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2039])).

cnf(c_3254,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3252])).

cnf(c_4436,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_6810,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6614,c_41,c_48,c_39,c_50,c_51,c_1956,c_1957,c_2010,c_2048,c_2389,c_2388,c_2391,c_3245,c_3250,c_3252,c_3254,c_4436])).

cnf(c_7250,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7227,c_6810])).

cnf(c_7251,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_7250])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7251,c_3254,c_2391,c_2389,c_1957,c_50,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:27:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.56/1.01  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.01  
% 3.56/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.56/1.01  
% 3.56/1.01  ------  iProver source info
% 3.56/1.01  
% 3.56/1.01  git: date: 2020-06-30 10:37:57 +0100
% 3.56/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.56/1.01  git: non_committed_changes: false
% 3.56/1.01  git: last_make_outside_of_git: false
% 3.56/1.01  
% 3.56/1.01  ------ 
% 3.56/1.01  
% 3.56/1.01  ------ Input Options
% 3.56/1.01  
% 3.56/1.01  --out_options                           all
% 3.56/1.01  --tptp_safe_out                         true
% 3.56/1.01  --problem_path                          ""
% 3.56/1.01  --include_path                          ""
% 3.56/1.01  --clausifier                            res/vclausify_rel
% 3.56/1.01  --clausifier_options                    --mode clausify
% 3.56/1.01  --stdin                                 false
% 3.56/1.01  --stats_out                             all
% 3.56/1.01  
% 3.56/1.01  ------ General Options
% 3.56/1.01  
% 3.56/1.01  --fof                                   false
% 3.56/1.01  --time_out_real                         305.
% 3.56/1.01  --time_out_virtual                      -1.
% 3.56/1.01  --symbol_type_check                     false
% 3.56/1.01  --clausify_out                          false
% 3.56/1.01  --sig_cnt_out                           false
% 3.56/1.01  --trig_cnt_out                          false
% 3.56/1.01  --trig_cnt_out_tolerance                1.
% 3.56/1.01  --trig_cnt_out_sk_spl                   false
% 3.56/1.01  --abstr_cl_out                          false
% 3.56/1.01  
% 3.56/1.01  ------ Global Options
% 3.56/1.01  
% 3.56/1.01  --schedule                              default
% 3.56/1.01  --add_important_lit                     false
% 3.56/1.01  --prop_solver_per_cl                    1000
% 3.56/1.01  --min_unsat_core                        false
% 3.56/1.01  --soft_assumptions                      false
% 3.56/1.01  --soft_lemma_size                       3
% 3.56/1.01  --prop_impl_unit_size                   0
% 3.56/1.01  --prop_impl_unit                        []
% 3.56/1.01  --share_sel_clauses                     true
% 3.56/1.01  --reset_solvers                         false
% 3.56/1.01  --bc_imp_inh                            [conj_cone]
% 3.56/1.01  --conj_cone_tolerance                   3.
% 3.56/1.01  --extra_neg_conj                        none
% 3.56/1.01  --large_theory_mode                     true
% 3.56/1.01  --prolific_symb_bound                   200
% 3.56/1.01  --lt_threshold                          2000
% 3.56/1.01  --clause_weak_htbl                      true
% 3.56/1.01  --gc_record_bc_elim                     false
% 3.56/1.01  
% 3.56/1.01  ------ Preprocessing Options
% 3.56/1.01  
% 3.56/1.01  --preprocessing_flag                    true
% 3.56/1.01  --time_out_prep_mult                    0.1
% 3.56/1.01  --splitting_mode                        input
% 3.56/1.01  --splitting_grd                         true
% 3.56/1.01  --splitting_cvd                         false
% 3.56/1.01  --splitting_cvd_svl                     false
% 3.56/1.01  --splitting_nvd                         32
% 3.56/1.01  --sub_typing                            true
% 3.56/1.01  --prep_gs_sim                           true
% 3.56/1.01  --prep_unflatten                        true
% 3.56/1.01  --prep_res_sim                          true
% 3.56/1.01  --prep_upred                            true
% 3.56/1.01  --prep_sem_filter                       exhaustive
% 3.56/1.01  --prep_sem_filter_out                   false
% 3.56/1.01  --pred_elim                             true
% 3.56/1.01  --res_sim_input                         true
% 3.56/1.01  --eq_ax_congr_red                       true
% 3.56/1.01  --pure_diseq_elim                       true
% 3.56/1.01  --brand_transform                       false
% 3.56/1.01  --non_eq_to_eq                          false
% 3.56/1.01  --prep_def_merge                        true
% 3.56/1.01  --prep_def_merge_prop_impl              false
% 3.56/1.01  --prep_def_merge_mbd                    true
% 3.56/1.01  --prep_def_merge_tr_red                 false
% 3.56/1.01  --prep_def_merge_tr_cl                  false
% 3.56/1.01  --smt_preprocessing                     true
% 3.56/1.01  --smt_ac_axioms                         fast
% 3.56/1.01  --preprocessed_out                      false
% 3.56/1.01  --preprocessed_stats                    false
% 3.56/1.01  
% 3.56/1.01  ------ Abstraction refinement Options
% 3.56/1.01  
% 3.56/1.01  --abstr_ref                             []
% 3.56/1.01  --abstr_ref_prep                        false
% 3.56/1.01  --abstr_ref_until_sat                   false
% 3.56/1.01  --abstr_ref_sig_restrict                funpre
% 3.56/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/1.01  --abstr_ref_under                       []
% 3.56/1.01  
% 3.56/1.01  ------ SAT Options
% 3.56/1.01  
% 3.56/1.01  --sat_mode                              false
% 3.56/1.01  --sat_fm_restart_options                ""
% 3.56/1.01  --sat_gr_def                            false
% 3.56/1.01  --sat_epr_types                         true
% 3.56/1.01  --sat_non_cyclic_types                  false
% 3.56/1.01  --sat_finite_models                     false
% 3.56/1.01  --sat_fm_lemmas                         false
% 3.56/1.01  --sat_fm_prep                           false
% 3.56/1.01  --sat_fm_uc_incr                        true
% 3.56/1.01  --sat_out_model                         small
% 3.56/1.01  --sat_out_clauses                       false
% 3.56/1.01  
% 3.56/1.01  ------ QBF Options
% 3.56/1.01  
% 3.56/1.01  --qbf_mode                              false
% 3.56/1.01  --qbf_elim_univ                         false
% 3.56/1.01  --qbf_dom_inst                          none
% 3.56/1.01  --qbf_dom_pre_inst                      false
% 3.56/1.01  --qbf_sk_in                             false
% 3.56/1.01  --qbf_pred_elim                         true
% 3.56/1.01  --qbf_split                             512
% 3.56/1.01  
% 3.56/1.01  ------ BMC1 Options
% 3.56/1.01  
% 3.56/1.01  --bmc1_incremental                      false
% 3.56/1.01  --bmc1_axioms                           reachable_all
% 3.56/1.01  --bmc1_min_bound                        0
% 3.56/1.01  --bmc1_max_bound                        -1
% 3.56/1.01  --bmc1_max_bound_default                -1
% 3.56/1.01  --bmc1_symbol_reachability              true
% 3.56/1.01  --bmc1_property_lemmas                  false
% 3.56/1.01  --bmc1_k_induction                      false
% 3.56/1.01  --bmc1_non_equiv_states                 false
% 3.56/1.01  --bmc1_deadlock                         false
% 3.56/1.01  --bmc1_ucm                              false
% 3.56/1.01  --bmc1_add_unsat_core                   none
% 3.56/1.01  --bmc1_unsat_core_children              false
% 3.56/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/1.01  --bmc1_out_stat                         full
% 3.56/1.01  --bmc1_ground_init                      false
% 3.56/1.01  --bmc1_pre_inst_next_state              false
% 3.56/1.01  --bmc1_pre_inst_state                   false
% 3.56/1.01  --bmc1_pre_inst_reach_state             false
% 3.56/1.01  --bmc1_out_unsat_core                   false
% 3.56/1.01  --bmc1_aig_witness_out                  false
% 3.56/1.01  --bmc1_verbose                          false
% 3.56/1.01  --bmc1_dump_clauses_tptp                false
% 3.56/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.56/1.01  --bmc1_dump_file                        -
% 3.56/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.56/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.56/1.01  --bmc1_ucm_extend_mode                  1
% 3.56/1.01  --bmc1_ucm_init_mode                    2
% 3.56/1.01  --bmc1_ucm_cone_mode                    none
% 3.56/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.56/1.01  --bmc1_ucm_relax_model                  4
% 3.56/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.56/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/1.01  --bmc1_ucm_layered_model                none
% 3.56/1.01  --bmc1_ucm_max_lemma_size               10
% 3.56/1.01  
% 3.56/1.01  ------ AIG Options
% 3.56/1.01  
% 3.56/1.01  --aig_mode                              false
% 3.56/1.01  
% 3.56/1.01  ------ Instantiation Options
% 3.56/1.01  
% 3.56/1.01  --instantiation_flag                    true
% 3.56/1.01  --inst_sos_flag                         false
% 3.56/1.01  --inst_sos_phase                        true
% 3.56/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/1.01  --inst_lit_sel_side                     num_symb
% 3.56/1.01  --inst_solver_per_active                1400
% 3.56/1.01  --inst_solver_calls_frac                1.
% 3.56/1.01  --inst_passive_queue_type               priority_queues
% 3.56/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/1.01  --inst_passive_queues_freq              [25;2]
% 3.56/1.01  --inst_dismatching                      true
% 3.56/1.01  --inst_eager_unprocessed_to_passive     true
% 3.56/1.01  --inst_prop_sim_given                   true
% 3.56/1.01  --inst_prop_sim_new                     false
% 3.56/1.01  --inst_subs_new                         false
% 3.56/1.01  --inst_eq_res_simp                      false
% 3.56/1.01  --inst_subs_given                       false
% 3.56/1.01  --inst_orphan_elimination               true
% 3.56/1.01  --inst_learning_loop_flag               true
% 3.56/1.01  --inst_learning_start                   3000
% 3.56/1.01  --inst_learning_factor                  2
% 3.56/1.01  --inst_start_prop_sim_after_learn       3
% 3.56/1.01  --inst_sel_renew                        solver
% 3.56/1.01  --inst_lit_activity_flag                true
% 3.56/1.01  --inst_restr_to_given                   false
% 3.56/1.01  --inst_activity_threshold               500
% 3.56/1.01  --inst_out_proof                        true
% 3.56/1.01  
% 3.56/1.01  ------ Resolution Options
% 3.56/1.01  
% 3.56/1.01  --resolution_flag                       true
% 3.56/1.01  --res_lit_sel                           adaptive
% 3.56/1.01  --res_lit_sel_side                      none
% 3.56/1.01  --res_ordering                          kbo
% 3.56/1.01  --res_to_prop_solver                    active
% 3.56/1.01  --res_prop_simpl_new                    false
% 3.56/1.01  --res_prop_simpl_given                  true
% 3.56/1.01  --res_passive_queue_type                priority_queues
% 3.56/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/1.01  --res_passive_queues_freq               [15;5]
% 3.56/1.01  --res_forward_subs                      full
% 3.56/1.01  --res_backward_subs                     full
% 3.56/1.01  --res_forward_subs_resolution           true
% 3.56/1.01  --res_backward_subs_resolution          true
% 3.56/1.01  --res_orphan_elimination                true
% 3.56/1.01  --res_time_limit                        2.
% 3.56/1.01  --res_out_proof                         true
% 3.56/1.01  
% 3.56/1.01  ------ Superposition Options
% 3.56/1.01  
% 3.56/1.01  --superposition_flag                    true
% 3.56/1.01  --sup_passive_queue_type                priority_queues
% 3.56/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.56/1.01  --demod_completeness_check              fast
% 3.56/1.01  --demod_use_ground                      true
% 3.56/1.01  --sup_to_prop_solver                    passive
% 3.56/1.01  --sup_prop_simpl_new                    true
% 3.56/1.01  --sup_prop_simpl_given                  true
% 3.56/1.01  --sup_fun_splitting                     false
% 3.56/1.01  --sup_smt_interval                      50000
% 3.56/1.01  
% 3.56/1.01  ------ Superposition Simplification Setup
% 3.56/1.01  
% 3.56/1.01  --sup_indices_passive                   []
% 3.56/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.01  --sup_full_bw                           [BwDemod]
% 3.56/1.01  --sup_immed_triv                        [TrivRules]
% 3.56/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.01  --sup_immed_bw_main                     []
% 3.56/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/1.01  
% 3.56/1.01  ------ Combination Options
% 3.56/1.01  
% 3.56/1.01  --comb_res_mult                         3
% 3.56/1.01  --comb_sup_mult                         2
% 3.56/1.01  --comb_inst_mult                        10
% 3.56/1.01  
% 3.56/1.01  ------ Debug Options
% 3.56/1.01  
% 3.56/1.01  --dbg_backtrace                         false
% 3.56/1.01  --dbg_dump_prop_clauses                 false
% 3.56/1.01  --dbg_dump_prop_clauses_file            -
% 3.56/1.01  --dbg_out_stat                          false
% 3.56/1.01  ------ Parsing...
% 3.56/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.56/1.01  
% 3.56/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 5 0s  sf_e  pe_s  pe_e 
% 3.56/1.01  
% 3.56/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.56/1.01  
% 3.56/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.56/1.01  ------ Proving...
% 3.56/1.01  ------ Problem Properties 
% 3.56/1.01  
% 3.56/1.01  
% 3.56/1.01  clauses                                 40
% 3.56/1.01  conjectures                             5
% 3.56/1.01  EPR                                     5
% 3.56/1.01  Horn                                    37
% 3.56/1.01  unary                                   15
% 3.56/1.01  binary                                  5
% 3.56/1.01  lits                                    116
% 3.56/1.01  lits eq                                 29
% 3.56/1.01  fd_pure                                 0
% 3.56/1.01  fd_pseudo                               0
% 3.56/1.01  fd_cond                                 3
% 3.56/1.01  fd_pseudo_cond                          1
% 3.56/1.01  AC symbols                              0
% 3.56/1.01  
% 3.56/1.01  ------ Schedule dynamic 5 is on 
% 3.56/1.01  
% 3.56/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.56/1.01  
% 3.56/1.01  
% 3.56/1.01  ------ 
% 3.56/1.01  Current options:
% 3.56/1.01  ------ 
% 3.56/1.01  
% 3.56/1.01  ------ Input Options
% 3.56/1.01  
% 3.56/1.01  --out_options                           all
% 3.56/1.01  --tptp_safe_out                         true
% 3.56/1.01  --problem_path                          ""
% 3.56/1.01  --include_path                          ""
% 3.56/1.01  --clausifier                            res/vclausify_rel
% 3.56/1.01  --clausifier_options                    --mode clausify
% 3.56/1.01  --stdin                                 false
% 3.56/1.01  --stats_out                             all
% 3.56/1.01  
% 3.56/1.01  ------ General Options
% 3.56/1.01  
% 3.56/1.01  --fof                                   false
% 3.56/1.01  --time_out_real                         305.
% 3.56/1.01  --time_out_virtual                      -1.
% 3.56/1.01  --symbol_type_check                     false
% 3.56/1.01  --clausify_out                          false
% 3.56/1.01  --sig_cnt_out                           false
% 3.56/1.01  --trig_cnt_out                          false
% 3.56/1.01  --trig_cnt_out_tolerance                1.
% 3.56/1.01  --trig_cnt_out_sk_spl                   false
% 3.56/1.01  --abstr_cl_out                          false
% 3.56/1.01  
% 3.56/1.01  ------ Global Options
% 3.56/1.01  
% 3.56/1.01  --schedule                              default
% 3.56/1.01  --add_important_lit                     false
% 3.56/1.01  --prop_solver_per_cl                    1000
% 3.56/1.01  --min_unsat_core                        false
% 3.56/1.01  --soft_assumptions                      false
% 3.56/1.01  --soft_lemma_size                       3
% 3.56/1.01  --prop_impl_unit_size                   0
% 3.56/1.01  --prop_impl_unit                        []
% 3.56/1.01  --share_sel_clauses                     true
% 3.56/1.01  --reset_solvers                         false
% 3.56/1.01  --bc_imp_inh                            [conj_cone]
% 3.56/1.01  --conj_cone_tolerance                   3.
% 3.56/1.01  --extra_neg_conj                        none
% 3.56/1.01  --large_theory_mode                     true
% 3.56/1.01  --prolific_symb_bound                   200
% 3.56/1.01  --lt_threshold                          2000
% 3.56/1.01  --clause_weak_htbl                      true
% 3.56/1.01  --gc_record_bc_elim                     false
% 3.56/1.01  
% 3.56/1.01  ------ Preprocessing Options
% 3.56/1.01  
% 3.56/1.01  --preprocessing_flag                    true
% 3.56/1.01  --time_out_prep_mult                    0.1
% 3.56/1.01  --splitting_mode                        input
% 3.56/1.01  --splitting_grd                         true
% 3.56/1.01  --splitting_cvd                         false
% 3.56/1.01  --splitting_cvd_svl                     false
% 3.56/1.01  --splitting_nvd                         32
% 3.56/1.01  --sub_typing                            true
% 3.56/1.01  --prep_gs_sim                           true
% 3.56/1.01  --prep_unflatten                        true
% 3.56/1.01  --prep_res_sim                          true
% 3.56/1.01  --prep_upred                            true
% 3.56/1.01  --prep_sem_filter                       exhaustive
% 3.56/1.01  --prep_sem_filter_out                   false
% 3.56/1.01  --pred_elim                             true
% 3.56/1.01  --res_sim_input                         true
% 3.56/1.01  --eq_ax_congr_red                       true
% 3.56/1.01  --pure_diseq_elim                       true
% 3.56/1.01  --brand_transform                       false
% 3.56/1.01  --non_eq_to_eq                          false
% 3.56/1.01  --prep_def_merge                        true
% 3.56/1.01  --prep_def_merge_prop_impl              false
% 3.56/1.01  --prep_def_merge_mbd                    true
% 3.56/1.01  --prep_def_merge_tr_red                 false
% 3.56/1.01  --prep_def_merge_tr_cl                  false
% 3.56/1.01  --smt_preprocessing                     true
% 3.56/1.01  --smt_ac_axioms                         fast
% 3.56/1.01  --preprocessed_out                      false
% 3.56/1.01  --preprocessed_stats                    false
% 3.56/1.01  
% 3.56/1.01  ------ Abstraction refinement Options
% 3.56/1.01  
% 3.56/1.01  --abstr_ref                             []
% 3.56/1.01  --abstr_ref_prep                        false
% 3.56/1.01  --abstr_ref_until_sat                   false
% 3.56/1.01  --abstr_ref_sig_restrict                funpre
% 3.56/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 3.56/1.01  --abstr_ref_under                       []
% 3.56/1.01  
% 3.56/1.01  ------ SAT Options
% 3.56/1.01  
% 3.56/1.01  --sat_mode                              false
% 3.56/1.01  --sat_fm_restart_options                ""
% 3.56/1.01  --sat_gr_def                            false
% 3.56/1.01  --sat_epr_types                         true
% 3.56/1.01  --sat_non_cyclic_types                  false
% 3.56/1.01  --sat_finite_models                     false
% 3.56/1.01  --sat_fm_lemmas                         false
% 3.56/1.01  --sat_fm_prep                           false
% 3.56/1.01  --sat_fm_uc_incr                        true
% 3.56/1.01  --sat_out_model                         small
% 3.56/1.01  --sat_out_clauses                       false
% 3.56/1.01  
% 3.56/1.01  ------ QBF Options
% 3.56/1.01  
% 3.56/1.01  --qbf_mode                              false
% 3.56/1.01  --qbf_elim_univ                         false
% 3.56/1.01  --qbf_dom_inst                          none
% 3.56/1.01  --qbf_dom_pre_inst                      false
% 3.56/1.01  --qbf_sk_in                             false
% 3.56/1.01  --qbf_pred_elim                         true
% 3.56/1.01  --qbf_split                             512
% 3.56/1.01  
% 3.56/1.01  ------ BMC1 Options
% 3.56/1.01  
% 3.56/1.01  --bmc1_incremental                      false
% 3.56/1.01  --bmc1_axioms                           reachable_all
% 3.56/1.01  --bmc1_min_bound                        0
% 3.56/1.01  --bmc1_max_bound                        -1
% 3.56/1.01  --bmc1_max_bound_default                -1
% 3.56/1.01  --bmc1_symbol_reachability              true
% 3.56/1.01  --bmc1_property_lemmas                  false
% 3.56/1.01  --bmc1_k_induction                      false
% 3.56/1.01  --bmc1_non_equiv_states                 false
% 3.56/1.01  --bmc1_deadlock                         false
% 3.56/1.01  --bmc1_ucm                              false
% 3.56/1.01  --bmc1_add_unsat_core                   none
% 3.56/1.01  --bmc1_unsat_core_children              false
% 3.56/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 3.56/1.01  --bmc1_out_stat                         full
% 3.56/1.01  --bmc1_ground_init                      false
% 3.56/1.01  --bmc1_pre_inst_next_state              false
% 3.56/1.01  --bmc1_pre_inst_state                   false
% 3.56/1.01  --bmc1_pre_inst_reach_state             false
% 3.56/1.01  --bmc1_out_unsat_core                   false
% 3.56/1.01  --bmc1_aig_witness_out                  false
% 3.56/1.01  --bmc1_verbose                          false
% 3.56/1.01  --bmc1_dump_clauses_tptp                false
% 3.56/1.01  --bmc1_dump_unsat_core_tptp             false
% 3.56/1.01  --bmc1_dump_file                        -
% 3.56/1.01  --bmc1_ucm_expand_uc_limit              128
% 3.56/1.01  --bmc1_ucm_n_expand_iterations          6
% 3.56/1.01  --bmc1_ucm_extend_mode                  1
% 3.56/1.01  --bmc1_ucm_init_mode                    2
% 3.56/1.01  --bmc1_ucm_cone_mode                    none
% 3.56/1.01  --bmc1_ucm_reduced_relation_type        0
% 3.56/1.01  --bmc1_ucm_relax_model                  4
% 3.56/1.01  --bmc1_ucm_full_tr_after_sat            true
% 3.56/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 3.56/1.01  --bmc1_ucm_layered_model                none
% 3.56/1.01  --bmc1_ucm_max_lemma_size               10
% 3.56/1.01  
% 3.56/1.01  ------ AIG Options
% 3.56/1.01  
% 3.56/1.01  --aig_mode                              false
% 3.56/1.01  
% 3.56/1.01  ------ Instantiation Options
% 3.56/1.01  
% 3.56/1.01  --instantiation_flag                    true
% 3.56/1.01  --inst_sos_flag                         false
% 3.56/1.01  --inst_sos_phase                        true
% 3.56/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.56/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.56/1.01  --inst_lit_sel_side                     none
% 3.56/1.01  --inst_solver_per_active                1400
% 3.56/1.01  --inst_solver_calls_frac                1.
% 3.56/1.01  --inst_passive_queue_type               priority_queues
% 3.56/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.56/1.01  --inst_passive_queues_freq              [25;2]
% 3.56/1.01  --inst_dismatching                      true
% 3.56/1.01  --inst_eager_unprocessed_to_passive     true
% 3.56/1.01  --inst_prop_sim_given                   true
% 3.56/1.01  --inst_prop_sim_new                     false
% 3.56/1.01  --inst_subs_new                         false
% 3.56/1.01  --inst_eq_res_simp                      false
% 3.56/1.01  --inst_subs_given                       false
% 3.56/1.01  --inst_orphan_elimination               true
% 3.56/1.01  --inst_learning_loop_flag               true
% 3.56/1.01  --inst_learning_start                   3000
% 3.56/1.01  --inst_learning_factor                  2
% 3.56/1.01  --inst_start_prop_sim_after_learn       3
% 3.56/1.01  --inst_sel_renew                        solver
% 3.56/1.01  --inst_lit_activity_flag                true
% 3.56/1.01  --inst_restr_to_given                   false
% 3.56/1.01  --inst_activity_threshold               500
% 3.56/1.01  --inst_out_proof                        true
% 3.56/1.01  
% 3.56/1.01  ------ Resolution Options
% 3.56/1.01  
% 3.56/1.01  --resolution_flag                       false
% 3.56/1.01  --res_lit_sel                           adaptive
% 3.56/1.01  --res_lit_sel_side                      none
% 3.56/1.01  --res_ordering                          kbo
% 3.56/1.01  --res_to_prop_solver                    active
% 3.56/1.01  --res_prop_simpl_new                    false
% 3.56/1.01  --res_prop_simpl_given                  true
% 3.56/1.01  --res_passive_queue_type                priority_queues
% 3.56/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.56/1.01  --res_passive_queues_freq               [15;5]
% 3.56/1.01  --res_forward_subs                      full
% 3.56/1.01  --res_backward_subs                     full
% 3.56/1.01  --res_forward_subs_resolution           true
% 3.56/1.01  --res_backward_subs_resolution          true
% 3.56/1.01  --res_orphan_elimination                true
% 3.56/1.01  --res_time_limit                        2.
% 3.56/1.01  --res_out_proof                         true
% 3.56/1.01  
% 3.56/1.01  ------ Superposition Options
% 3.56/1.01  
% 3.56/1.01  --superposition_flag                    true
% 3.56/1.01  --sup_passive_queue_type                priority_queues
% 3.56/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.56/1.01  --sup_passive_queues_freq               [8;1;4]
% 3.56/1.01  --demod_completeness_check              fast
% 3.56/1.01  --demod_use_ground                      true
% 3.56/1.01  --sup_to_prop_solver                    passive
% 3.56/1.01  --sup_prop_simpl_new                    true
% 3.56/1.01  --sup_prop_simpl_given                  true
% 3.56/1.01  --sup_fun_splitting                     false
% 3.56/1.01  --sup_smt_interval                      50000
% 3.56/1.01  
% 3.56/1.01  ------ Superposition Simplification Setup
% 3.56/1.01  
% 3.56/1.01  --sup_indices_passive                   []
% 3.56/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.56/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 3.56/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.01  --sup_full_bw                           [BwDemod]
% 3.56/1.01  --sup_immed_triv                        [TrivRules]
% 3.56/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.56/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.01  --sup_immed_bw_main                     []
% 3.56/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 3.56/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.56/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.56/1.01  
% 3.56/1.01  ------ Combination Options
% 3.56/1.01  
% 3.56/1.01  --comb_res_mult                         3
% 3.56/1.01  --comb_sup_mult                         2
% 3.56/1.01  --comb_inst_mult                        10
% 3.56/1.01  
% 3.56/1.01  ------ Debug Options
% 3.56/1.01  
% 3.56/1.01  --dbg_backtrace                         false
% 3.56/1.01  --dbg_dump_prop_clauses                 false
% 3.56/1.01  --dbg_dump_prop_clauses_file            -
% 3.56/1.01  --dbg_out_stat                          false
% 3.56/1.01  
% 3.56/1.01  
% 3.56/1.01  
% 3.56/1.01  
% 3.56/1.01  ------ Proving...
% 3.56/1.01  
% 3.56/1.01  
% 3.56/1.01  % SZS status Theorem for theBenchmark.p
% 3.56/1.01  
% 3.56/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 3.56/1.01  
% 3.56/1.01  fof(f24,conjecture,(
% 3.56/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f25,negated_conjecture,(
% 3.56/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.56/1.01    inference(negated_conjecture,[],[f24])).
% 3.56/1.01  
% 3.56/1.01  fof(f51,plain,(
% 3.56/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.56/1.01    inference(ennf_transformation,[],[f25])).
% 3.56/1.01  
% 3.56/1.01  fof(f52,plain,(
% 3.56/1.01    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.56/1.01    inference(flattening,[],[f51])).
% 3.56/1.01  
% 3.56/1.01  fof(f60,plain,(
% 3.56/1.01    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.56/1.01    introduced(choice_axiom,[])).
% 3.56/1.01  
% 3.56/1.01  fof(f59,plain,(
% 3.56/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.56/1.01    introduced(choice_axiom,[])).
% 3.56/1.01  
% 3.56/1.01  fof(f58,plain,(
% 3.56/1.01    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.56/1.01    introduced(choice_axiom,[])).
% 3.56/1.01  
% 3.56/1.01  fof(f61,plain,(
% 3.56/1.01    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.56/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f52,f60,f59,f58])).
% 3.56/1.01  
% 3.56/1.01  fof(f104,plain,(
% 3.56/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.56/1.01    inference(cnf_transformation,[],[f61])).
% 3.56/1.01  
% 3.56/1.01  fof(f21,axiom,(
% 3.56/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f46,plain,(
% 3.56/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.56/1.01    inference(ennf_transformation,[],[f21])).
% 3.56/1.01  
% 3.56/1.01  fof(f96,plain,(
% 3.56/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f46])).
% 3.56/1.01  
% 3.56/1.01  fof(f101,plain,(
% 3.56/1.01    l1_struct_0(sK1)),
% 3.56/1.01    inference(cnf_transformation,[],[f61])).
% 3.56/1.01  
% 3.56/1.01  fof(f99,plain,(
% 3.56/1.01    l1_struct_0(sK0)),
% 3.56/1.01    inference(cnf_transformation,[],[f61])).
% 3.56/1.01  
% 3.56/1.01  fof(f13,axiom,(
% 3.56/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f35,plain,(
% 3.56/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.56/1.01    inference(ennf_transformation,[],[f13])).
% 3.56/1.01  
% 3.56/1.01  fof(f83,plain,(
% 3.56/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.56/1.01    inference(cnf_transformation,[],[f35])).
% 3.56/1.01  
% 3.56/1.01  fof(f11,axiom,(
% 3.56/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f31,plain,(
% 3.56/1.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.56/1.01    inference(ennf_transformation,[],[f11])).
% 3.56/1.01  
% 3.56/1.01  fof(f32,plain,(
% 3.56/1.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.56/1.01    inference(flattening,[],[f31])).
% 3.56/1.01  
% 3.56/1.01  fof(f80,plain,(
% 3.56/1.01    ( ! [X0] : (k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f32])).
% 3.56/1.01  
% 3.56/1.01  fof(f15,axiom,(
% 3.56/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f37,plain,(
% 3.56/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.56/1.01    inference(ennf_transformation,[],[f15])).
% 3.56/1.01  
% 3.56/1.01  fof(f85,plain,(
% 3.56/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.56/1.01    inference(cnf_transformation,[],[f37])).
% 3.56/1.01  
% 3.56/1.01  fof(f105,plain,(
% 3.56/1.01    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.56/1.01    inference(cnf_transformation,[],[f61])).
% 3.56/1.01  
% 3.56/1.01  fof(f19,axiom,(
% 3.56/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f42,plain,(
% 3.56/1.01    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.56/1.01    inference(ennf_transformation,[],[f19])).
% 3.56/1.01  
% 3.56/1.01  fof(f43,plain,(
% 3.56/1.01    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.56/1.01    inference(flattening,[],[f42])).
% 3.56/1.01  
% 3.56/1.01  fof(f91,plain,(
% 3.56/1.01    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f43])).
% 3.56/1.01  
% 3.56/1.01  fof(f102,plain,(
% 3.56/1.01    v1_funct_1(sK2)),
% 3.56/1.01    inference(cnf_transformation,[],[f61])).
% 3.56/1.01  
% 3.56/1.01  fof(f106,plain,(
% 3.56/1.01    v2_funct_1(sK2)),
% 3.56/1.01    inference(cnf_transformation,[],[f61])).
% 3.56/1.01  
% 3.56/1.01  fof(f103,plain,(
% 3.56/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.56/1.01    inference(cnf_transformation,[],[f61])).
% 3.56/1.01  
% 3.56/1.01  fof(f1,axiom,(
% 3.56/1.01    v1_xboole_0(k1_xboole_0)),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f62,plain,(
% 3.56/1.01    v1_xboole_0(k1_xboole_0)),
% 3.56/1.01    inference(cnf_transformation,[],[f1])).
% 3.56/1.01  
% 3.56/1.01  fof(f22,axiom,(
% 3.56/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f47,plain,(
% 3.56/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.56/1.01    inference(ennf_transformation,[],[f22])).
% 3.56/1.01  
% 3.56/1.01  fof(f48,plain,(
% 3.56/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.56/1.01    inference(flattening,[],[f47])).
% 3.56/1.01  
% 3.56/1.01  fof(f97,plain,(
% 3.56/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f48])).
% 3.56/1.01  
% 3.56/1.01  fof(f100,plain,(
% 3.56/1.01    ~v2_struct_0(sK1)),
% 3.56/1.01    inference(cnf_transformation,[],[f61])).
% 3.56/1.01  
% 3.56/1.01  fof(f8,axiom,(
% 3.56/1.01    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f73,plain,(
% 3.56/1.01    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 3.56/1.01    inference(cnf_transformation,[],[f8])).
% 3.56/1.01  
% 3.56/1.01  fof(f16,axiom,(
% 3.56/1.01    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f86,plain,(
% 3.56/1.01    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f16])).
% 3.56/1.01  
% 3.56/1.01  fof(f109,plain,(
% 3.56/1.01    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 3.56/1.01    inference(definition_unfolding,[],[f73,f86])).
% 3.56/1.01  
% 3.56/1.01  fof(f23,axiom,(
% 3.56/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f49,plain,(
% 3.56/1.01    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.56/1.01    inference(ennf_transformation,[],[f23])).
% 3.56/1.01  
% 3.56/1.01  fof(f50,plain,(
% 3.56/1.01    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.56/1.01    inference(flattening,[],[f49])).
% 3.56/1.01  
% 3.56/1.01  fof(f98,plain,(
% 3.56/1.01    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f50])).
% 3.56/1.01  
% 3.56/1.01  fof(f17,axiom,(
% 3.56/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f38,plain,(
% 3.56/1.01    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.56/1.01    inference(ennf_transformation,[],[f17])).
% 3.56/1.01  
% 3.56/1.01  fof(f39,plain,(
% 3.56/1.01    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.56/1.01    inference(flattening,[],[f38])).
% 3.56/1.01  
% 3.56/1.01  fof(f87,plain,(
% 3.56/1.01    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f39])).
% 3.56/1.01  
% 3.56/1.01  fof(f107,plain,(
% 3.56/1.01    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.56/1.01    inference(cnf_transformation,[],[f61])).
% 3.56/1.01  
% 3.56/1.01  fof(f2,axiom,(
% 3.56/1.01    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f53,plain,(
% 3.56/1.01    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.56/1.01    inference(nnf_transformation,[],[f2])).
% 3.56/1.01  
% 3.56/1.01  fof(f54,plain,(
% 3.56/1.01    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.56/1.01    inference(flattening,[],[f53])).
% 3.56/1.01  
% 3.56/1.01  fof(f63,plain,(
% 3.56/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.56/1.01    inference(cnf_transformation,[],[f54])).
% 3.56/1.01  
% 3.56/1.01  fof(f111,plain,(
% 3.56/1.01    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.56/1.01    inference(equality_resolution,[],[f63])).
% 3.56/1.01  
% 3.56/1.01  fof(f10,axiom,(
% 3.56/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f29,plain,(
% 3.56/1.01    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.56/1.01    inference(ennf_transformation,[],[f10])).
% 3.56/1.01  
% 3.56/1.01  fof(f30,plain,(
% 3.56/1.01    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.56/1.01    inference(flattening,[],[f29])).
% 3.56/1.01  
% 3.56/1.01  fof(f78,plain,(
% 3.56/1.01    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f30])).
% 3.56/1.01  
% 3.56/1.01  fof(f20,axiom,(
% 3.56/1.01    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f44,plain,(
% 3.56/1.01    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.56/1.01    inference(ennf_transformation,[],[f20])).
% 3.56/1.01  
% 3.56/1.01  fof(f45,plain,(
% 3.56/1.01    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.56/1.01    inference(flattening,[],[f44])).
% 3.56/1.01  
% 3.56/1.01  fof(f95,plain,(
% 3.56/1.01    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f45])).
% 3.56/1.01  
% 3.56/1.01  fof(f18,axiom,(
% 3.56/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f40,plain,(
% 3.56/1.01    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.56/1.01    inference(ennf_transformation,[],[f18])).
% 3.56/1.01  
% 3.56/1.01  fof(f41,plain,(
% 3.56/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.56/1.01    inference(flattening,[],[f40])).
% 3.56/1.01  
% 3.56/1.01  fof(f88,plain,(
% 3.56/1.01    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f41])).
% 3.56/1.01  
% 3.56/1.01  fof(f9,axiom,(
% 3.56/1.01    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f27,plain,(
% 3.56/1.01    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.56/1.01    inference(ennf_transformation,[],[f9])).
% 3.56/1.01  
% 3.56/1.01  fof(f28,plain,(
% 3.56/1.01    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.56/1.01    inference(flattening,[],[f27])).
% 3.56/1.01  
% 3.56/1.01  fof(f76,plain,(
% 3.56/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f28])).
% 3.56/1.01  
% 3.56/1.01  fof(f75,plain,(
% 3.56/1.01    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f28])).
% 3.56/1.01  
% 3.56/1.01  fof(f79,plain,(
% 3.56/1.01    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f30])).
% 3.56/1.01  
% 3.56/1.01  fof(f12,axiom,(
% 3.56/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.56/1.01    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.56/1.01  
% 3.56/1.01  fof(f33,plain,(
% 3.56/1.01    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.56/1.01    inference(ennf_transformation,[],[f12])).
% 3.56/1.01  
% 3.56/1.01  fof(f34,plain,(
% 3.56/1.01    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.56/1.01    inference(flattening,[],[f33])).
% 3.56/1.01  
% 3.56/1.01  fof(f82,plain,(
% 3.56/1.01    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f34])).
% 3.56/1.01  
% 3.56/1.01  fof(f77,plain,(
% 3.56/1.01    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f28])).
% 3.56/1.01  
% 3.56/1.01  fof(f94,plain,(
% 3.56/1.01    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f45])).
% 3.56/1.01  
% 3.56/1.01  fof(f90,plain,(
% 3.56/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f41])).
% 3.56/1.01  
% 3.56/1.01  fof(f89,plain,(
% 3.56/1.01    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.56/1.01    inference(cnf_transformation,[],[f41])).
% 3.56/1.01  
% 3.56/1.01  cnf(c_39,negated_conjecture,
% 3.56/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.56/1.01      inference(cnf_transformation,[],[f104]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1605,plain,
% 3.56/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_33,plain,
% 3.56/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f96]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_42,negated_conjecture,
% 3.56/1.01      ( l1_struct_0(sK1) ),
% 3.56/1.01      inference(cnf_transformation,[],[f101]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_537,plain,
% 3.56/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.56/1.01      inference(resolution_lifted,[status(thm)],[c_33,c_42]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_538,plain,
% 3.56/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.56/1.01      inference(unflattening,[status(thm)],[c_537]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_44,negated_conjecture,
% 3.56/1.01      ( l1_struct_0(sK0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f99]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_542,plain,
% 3.56/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.56/1.01      inference(resolution_lifted,[status(thm)],[c_33,c_44]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_543,plain,
% 3.56/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.56/1.01      inference(unflattening,[status(thm)],[c_542]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1662,plain,
% 3.56/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.56/1.01      inference(light_normalisation,[status(thm)],[c_1605,c_538,c_543]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_21,plain,
% 3.56/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.56/1.01      | v1_relat_1(X0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f83]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1616,plain,
% 3.56/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.56/1.01      | v1_relat_1(X0) = iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2739,plain,
% 3.56/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_1662,c_1616]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_19,plain,
% 3.56/1.01      ( ~ v1_relat_1(X0)
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ v2_funct_1(X0)
% 3.56/1.01      | k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f80]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1618,plain,
% 3.56/1.01      ( k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) = k1_relat_1(X0)
% 3.56/1.01      | v1_relat_1(X0) != iProver_top
% 3.56/1.01      | v1_funct_1(X0) != iProver_top
% 3.56/1.01      | v2_funct_1(X0) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_7159,plain,
% 3.56/1.01      ( k1_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) = k1_relat_1(sK2)
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_2739,c_1618]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_23,plain,
% 3.56/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.56/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f85]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1614,plain,
% 3.56/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.56/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3489,plain,
% 3.56/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_1662,c_1614]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_38,negated_conjecture,
% 3.56/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.56/1.01      inference(cnf_transformation,[],[f105]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1659,plain,
% 3.56/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.56/1.01      inference(light_normalisation,[status(thm)],[c_38,c_538,c_543]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3741,plain,
% 3.56/1.01      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.56/1.01      inference(demodulation,[status(thm)],[c_3489,c_1659]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3744,plain,
% 3.56/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.56/1.01      inference(demodulation,[status(thm)],[c_3741,c_3489]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_29,plain,
% 3.56/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.56/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ v2_funct_1(X0)
% 3.56/1.01      | k2_relset_1(X1,X2,X0) != X2
% 3.56/1.01      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.56/1.01      | k1_xboole_0 = X2 ),
% 3.56/1.01      inference(cnf_transformation,[],[f91]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1610,plain,
% 3.56/1.01      ( k2_relset_1(X0,X1,X2) != X1
% 3.56/1.01      | k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
% 3.56/1.01      | k1_xboole_0 = X1
% 3.56/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.56/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.56/1.01      | v1_funct_1(X2) != iProver_top
% 3.56/1.01      | v2_funct_1(X2) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_5033,plain,
% 3.56/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
% 3.56/1.01      | k2_relat_1(sK2) = k1_xboole_0
% 3.56/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.56/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_3744,c_1610]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_41,negated_conjecture,
% 3.56/1.01      ( v1_funct_1(sK2) ),
% 3.56/1.01      inference(cnf_transformation,[],[f102]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_48,plain,
% 3.56/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_37,negated_conjecture,
% 3.56/1.01      ( v2_funct_1(sK2) ),
% 3.56/1.01      inference(cnf_transformation,[],[f106]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_51,plain,
% 3.56/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3749,plain,
% 3.56/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 3.56/1.01      inference(demodulation,[status(thm)],[c_3741,c_1662]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_40,negated_conjecture,
% 3.56/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.56/1.01      inference(cnf_transformation,[],[f103]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1604,plain,
% 3.56/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1656,plain,
% 3.56/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.56/1.01      inference(light_normalisation,[status(thm)],[c_1604,c_538,c_543]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3750,plain,
% 3.56/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 3.56/1.01      inference(demodulation,[status(thm)],[c_3741,c_1656]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_0,plain,
% 3.56/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f62]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_34,plain,
% 3.56/1.01      ( v2_struct_0(X0)
% 3.56/1.01      | ~ l1_struct_0(X0)
% 3.56/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.56/1.01      inference(cnf_transformation,[],[f97]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_510,plain,
% 3.56/1.01      ( v2_struct_0(X0)
% 3.56/1.01      | ~ l1_struct_0(X0)
% 3.56/1.01      | u1_struct_0(X0) != k1_xboole_0 ),
% 3.56/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_34]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_43,negated_conjecture,
% 3.56/1.01      ( ~ v2_struct_0(sK1) ),
% 3.56/1.01      inference(cnf_transformation,[],[f100]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_528,plain,
% 3.56/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 3.56/1.01      inference(resolution_lifted,[status(thm)],[c_510,c_43]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_529,plain,
% 3.56/1.01      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 3.56/1.01      inference(unflattening,[status(thm)],[c_528]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_531,plain,
% 3.56/1.01      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 3.56/1.01      inference(global_propositional_subsumption,
% 3.56/1.01                [status(thm)],
% 3.56/1.01                [c_529,c_42]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1639,plain,
% 3.56/1.01      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 3.56/1.01      inference(light_normalisation,[status(thm)],[c_531,c_538]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3751,plain,
% 3.56/1.01      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 3.56/1.01      inference(demodulation,[status(thm)],[c_3741,c_1639]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_5512,plain,
% 3.56/1.01      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) ),
% 3.56/1.01      inference(global_propositional_subsumption,
% 3.56/1.01                [status(thm)],
% 3.56/1.01                [c_5033,c_48,c_51,c_3749,c_3750,c_3751]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_7186,plain,
% 3.56/1.01      ( k1_relat_1(k6_partfun1(k2_struct_0(sK0))) = k1_relat_1(sK2)
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(light_normalisation,[status(thm)],[c_7159,c_5512]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_12,plain,
% 3.56/1.01      ( k1_relat_1(k6_partfun1(X0)) = X0 ),
% 3.56/1.01      inference(cnf_transformation,[],[f109]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_7187,plain,
% 3.56/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(demodulation,[status(thm)],[c_7186,c_12]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_7222,plain,
% 3.56/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.56/1.01      inference(global_propositional_subsumption,
% 3.56/1.01                [status(thm)],
% 3.56/1.01                [c_7187,c_48,c_51]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_35,plain,
% 3.56/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.56/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ v2_funct_1(X0)
% 3.56/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.56/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.56/1.01      inference(cnf_transformation,[],[f98]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1607,plain,
% 3.56/1.01      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 3.56/1.01      | k2_relset_1(X0,X1,X2) != X1
% 3.56/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.56/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.56/1.01      | v1_funct_1(X2) != iProver_top
% 3.56/1.01      | v2_funct_1(X2) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2538,plain,
% 3.56/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.56/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.56/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_1659,c_1607]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2759,plain,
% 3.56/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.56/1.01      inference(global_propositional_subsumption,
% 3.56/1.01                [status(thm)],
% 3.56/1.01                [c_2538,c_48,c_51,c_1662,c_1656]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_24,plain,
% 3.56/1.01      ( r2_funct_2(X0,X1,X2,X2)
% 3.56/1.01      | ~ v1_funct_2(X3,X0,X1)
% 3.56/1.01      | ~ v1_funct_2(X2,X0,X1)
% 3.56/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.56/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.56/1.01      | ~ v1_funct_1(X3)
% 3.56/1.01      | ~ v1_funct_1(X2) ),
% 3.56/1.01      inference(cnf_transformation,[],[f87]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_36,negated_conjecture,
% 3.56/1.01      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.56/1.01      inference(cnf_transformation,[],[f107]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_549,plain,
% 3.56/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.56/1.01      | ~ v1_funct_2(X3,X1,X2)
% 3.56/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.56/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ v1_funct_1(X3)
% 3.56/1.01      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X3
% 3.56/1.01      | u1_struct_0(sK1) != X2
% 3.56/1.01      | u1_struct_0(sK0) != X1
% 3.56/1.01      | sK2 != X3 ),
% 3.56/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_36]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_550,plain,
% 3.56/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.56/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.56/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.56/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.56/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.56/1.01      inference(unflattening,[status(thm)],[c_549]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_851,plain,
% 3.56/1.01      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.56/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.56/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.56/1.01      | sP0_iProver_split
% 3.56/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.56/1.01      inference(splitting,
% 3.56/1.01                [splitting(split),new_symbols(definition,[])],
% 3.56/1.01                [c_550]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1600,plain,
% 3.56/1.01      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.56/1.01      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.56/1.01      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.56/1.01      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 3.56/1.01      | sP0_iProver_split = iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_851]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1858,plain,
% 3.56/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.56/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.56/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.56/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 3.56/1.01      | sP0_iProver_split = iProver_top ),
% 3.56/1.01      inference(light_normalisation,[status(thm)],[c_1600,c_538,c_543]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_850,plain,
% 3.56/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.56/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ sP0_iProver_split ),
% 3.56/1.01      inference(splitting,
% 3.56/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.56/1.01                [c_550]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1601,plain,
% 3.56/1.01      ( v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.56/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.56/1.01      | v1_funct_1(X0) != iProver_top
% 3.56/1.01      | sP0_iProver_split != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_850]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1785,plain,
% 3.56/1.01      ( v1_funct_2(X0,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.56/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.56/1.01      | v1_funct_1(X0) != iProver_top
% 3.56/1.01      | sP0_iProver_split != iProver_top ),
% 3.56/1.01      inference(light_normalisation,[status(thm)],[c_1601,c_538,c_543]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1864,plain,
% 3.56/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.56/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.56/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.56/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.56/1.01      inference(forward_subsumption_resolution,
% 3.56/1.01                [status(thm)],
% 3.56/1.01                [c_1858,c_1785]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2762,plain,
% 3.56/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 3.56/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.56/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.56/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 3.56/1.01      inference(demodulation,[status(thm)],[c_2759,c_1864]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3745,plain,
% 3.56/1.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 3.56/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.56/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.56/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 3.56/1.01      inference(demodulation,[status(thm)],[c_3741,c_2762]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_7227,plain,
% 3.56/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 3.56/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.56/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.56/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.56/1.01      inference(demodulation,[status(thm)],[c_7222,c_3745]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3,plain,
% 3.56/1.01      ( r1_tarski(X0,X0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f111]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1629,plain,
% 3.56/1.01      ( r1_tarski(X0,X0) = iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_17,plain,
% 3.56/1.01      ( ~ v1_relat_1(X0)
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ v2_funct_1(X0)
% 3.56/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f78]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1620,plain,
% 3.56/1.01      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.56/1.01      | v1_relat_1(X0) != iProver_top
% 3.56/1.01      | v1_funct_1(X0) != iProver_top
% 3.56/1.01      | v2_funct_1(X0) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6144,plain,
% 3.56/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_2739,c_1620]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1956,plain,
% 3.56/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.56/1.01      | v1_relat_1(sK2) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_21]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2043,plain,
% 3.56/1.01      ( ~ v1_relat_1(sK2)
% 3.56/1.01      | ~ v1_funct_1(sK2)
% 3.56/1.01      | ~ v2_funct_1(sK2)
% 3.56/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_17]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6327,plain,
% 3.56/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.56/1.01      inference(global_propositional_subsumption,
% 3.56/1.01                [status(thm)],
% 3.56/1.01                [c_6144,c_41,c_39,c_37,c_1956,c_2043]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_30,plain,
% 3.56/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.56/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.56/1.01      | ~ v1_relat_1(X0)
% 3.56/1.01      | ~ v1_funct_1(X0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f95]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1609,plain,
% 3.56/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.56/1.01      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.56/1.01      | v1_relat_1(X0) != iProver_top
% 3.56/1.01      | v1_funct_1(X0) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6330,plain,
% 3.56/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) = iProver_top
% 3.56/1.01      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 3.56/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.56/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_6327,c_1609]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_50,plain,
% 3.56/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1957,plain,
% 3.56/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.56/1.01      | v1_relat_1(sK2) = iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_1956]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_27,plain,
% 3.56/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.56/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | v1_funct_1(k2_funct_1(X0))
% 3.56/1.01      | ~ v2_funct_1(X0)
% 3.56/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.56/1.01      inference(cnf_transformation,[],[f88]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_14,plain,
% 3.56/1.01      ( ~ v1_relat_1(X0)
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | v1_funct_1(k2_funct_1(X0))
% 3.56/1.01      | ~ v2_funct_1(X0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f76]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_236,plain,
% 3.56/1.01      ( ~ v2_funct_1(X0)
% 3.56/1.01      | v1_funct_1(k2_funct_1(X0))
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.56/1.01      inference(global_propositional_subsumption,
% 3.56/1.01                [status(thm)],
% 3.56/1.01                [c_27,c_21,c_14]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_237,plain,
% 3.56/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | v1_funct_1(k2_funct_1(X0))
% 3.56/1.01      | ~ v2_funct_1(X0) ),
% 3.56/1.01      inference(renaming,[status(thm)],[c_236]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1602,plain,
% 3.56/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.56/1.01      | v1_funct_1(X0) != iProver_top
% 3.56/1.01      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.56/1.01      | v2_funct_1(X0) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_237]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2010,plain,
% 3.56/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_1662,c_1602]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_15,plain,
% 3.56/1.01      ( ~ v1_relat_1(X0)
% 3.56/1.01      | v1_relat_1(k2_funct_1(X0))
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ v2_funct_1(X0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f75]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2045,plain,
% 3.56/1.01      ( v1_relat_1(k2_funct_1(sK2))
% 3.56/1.01      | ~ v1_relat_1(sK2)
% 3.56/1.01      | ~ v1_funct_1(sK2)
% 3.56/1.01      | ~ v2_funct_1(sK2) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_15]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2052,plain,
% 3.56/1.01      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.56/1.01      | v1_relat_1(sK2) != iProver_top
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_2045]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6492,plain,
% 3.56/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) = iProver_top
% 3.56/1.01      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top ),
% 3.56/1.01      inference(global_propositional_subsumption,
% 3.56/1.01                [status(thm)],
% 3.56/1.01                [c_6330,c_48,c_50,c_51,c_1957,c_2010,c_2052]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_16,plain,
% 3.56/1.01      ( ~ v1_relat_1(X0)
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ v2_funct_1(X0)
% 3.56/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f79]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1621,plain,
% 3.56/1.01      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.56/1.01      | v1_relat_1(X0) != iProver_top
% 3.56/1.01      | v1_funct_1(X0) != iProver_top
% 3.56/1.01      | v2_funct_1(X0) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6266,plain,
% 3.56/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_2739,c_1621]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2044,plain,
% 3.56/1.01      ( ~ v1_relat_1(sK2)
% 3.56/1.01      | ~ v1_funct_1(sK2)
% 3.56/1.01      | ~ v2_funct_1(sK2)
% 3.56/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_16]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6402,plain,
% 3.56/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.56/1.01      inference(global_propositional_subsumption,
% 3.56/1.01                [status(thm)],
% 3.56/1.01                [c_6266,c_41,c_39,c_37,c_1956,c_2044]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6498,plain,
% 3.56/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) = iProver_top
% 3.56/1.01      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.56/1.01      inference(light_normalisation,[status(thm)],[c_6492,c_6402]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6506,plain,
% 3.56/1.01      ( k2_relset_1(k2_relat_1(sK2),X0,k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
% 3.56/1.01      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_6498,c_1614]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6520,plain,
% 3.56/1.01      ( k2_relset_1(k2_relat_1(sK2),X0,k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.56/1.01      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.56/1.01      inference(light_normalisation,[status(thm)],[c_6506,c_6402]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6599,plain,
% 3.56/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_1629,c_6520]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6603,plain,
% 3.56/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.56/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.56/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.56/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.56/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_6599,c_1607]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_20,plain,
% 3.56/1.01      ( ~ v1_relat_1(X0)
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ v2_funct_1(X0)
% 3.56/1.01      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.56/1.01      inference(cnf_transformation,[],[f82]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_1617,plain,
% 3.56/1.01      ( k2_funct_1(k2_funct_1(X0)) = X0
% 3.56/1.01      | v1_relat_1(X0) != iProver_top
% 3.56/1.01      | v1_funct_1(X0) != iProver_top
% 3.56/1.01      | v2_funct_1(X0) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_5160,plain,
% 3.56/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(superposition,[status(thm)],[c_2739,c_1617]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2042,plain,
% 3.56/1.01      ( ~ v1_relat_1(sK2)
% 3.56/1.01      | ~ v1_funct_1(sK2)
% 3.56/1.01      | ~ v2_funct_1(sK2)
% 3.56/1.01      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_20]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_5505,plain,
% 3.56/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.56/1.01      inference(global_propositional_subsumption,
% 3.56/1.01                [status(thm)],
% 3.56/1.01                [c_5160,c_41,c_39,c_37,c_1956,c_2042]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6614,plain,
% 3.56/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 3.56/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.56/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.56/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.56/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.56/1.01      inference(light_normalisation,[status(thm)],[c_6603,c_5505]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_13,plain,
% 3.56/1.01      ( ~ v1_relat_1(X0)
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ v2_funct_1(X0)
% 3.56/1.01      | v2_funct_1(k2_funct_1(X0)) ),
% 3.56/1.01      inference(cnf_transformation,[],[f77]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2047,plain,
% 3.56/1.01      ( ~ v1_relat_1(sK2)
% 3.56/1.01      | ~ v1_funct_1(sK2)
% 3.56/1.01      | v2_funct_1(k2_funct_1(sK2))
% 3.56/1.01      | ~ v2_funct_1(sK2) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_13]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2048,plain,
% 3.56/1.01      ( v1_relat_1(sK2) != iProver_top
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_2047]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_31,plain,
% 3.56/1.01      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.56/1.01      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.56/1.01      | ~ v1_relat_1(X0)
% 3.56/1.01      | ~ v1_funct_1(X0) ),
% 3.56/1.01      inference(cnf_transformation,[],[f94]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2038,plain,
% 3.56/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
% 3.56/1.01      | ~ r1_tarski(k2_relat_1(sK2),X0)
% 3.56/1.01      | ~ v1_relat_1(sK2)
% 3.56/1.01      | ~ v1_funct_1(sK2) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_31]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2387,plain,
% 3.56/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.56/1.01      | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
% 3.56/1.01      | ~ v1_relat_1(sK2)
% 3.56/1.01      | ~ v1_funct_1(sK2) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_2038]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2389,plain,
% 3.56/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
% 3.56/1.01      | r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.56/1.01      | v1_relat_1(sK2) != iProver_top
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_2387]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2388,plain,
% 3.56/1.01      ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2391,plain,
% 3.56/1.01      ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_2388]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_25,plain,
% 3.56/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.56/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.56/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ v2_funct_1(X0)
% 3.56/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.56/1.01      inference(cnf_transformation,[],[f90]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2027,plain,
% 3.56/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 3.56/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.56/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.56/1.01      | ~ v1_funct_1(sK2)
% 3.56/1.01      | ~ v2_funct_1(sK2)
% 3.56/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_25]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3244,plain,
% 3.56/1.01      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.56/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
% 3.56/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.56/1.01      | ~ v1_funct_1(sK2)
% 3.56/1.01      | ~ v2_funct_1(sK2)
% 3.56/1.01      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_2027]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3245,plain,
% 3.56/1.01      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 3.56/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.56/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 3.56/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_3244]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_26,plain,
% 3.56/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 3.56/1.01      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.56/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.56/1.01      | ~ v1_funct_1(X0)
% 3.56/1.01      | ~ v2_funct_1(X0)
% 3.56/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.56/1.01      inference(cnf_transformation,[],[f89]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2022,plain,
% 3.56/1.01      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.56/1.01      | ~ v1_funct_2(sK2,X1,X0)
% 3.56/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.56/1.01      | ~ v1_funct_1(sK2)
% 3.56/1.01      | ~ v2_funct_1(sK2)
% 3.56/1.01      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_26]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3249,plain,
% 3.56/1.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
% 3.56/1.01      | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.56/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.56/1.01      | ~ v1_funct_1(sK2)
% 3.56/1.01      | ~ v2_funct_1(sK2)
% 3.56/1.01      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_2022]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3250,plain,
% 3.56/1.01      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 3.56/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 3.56/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.56/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top
% 3.56/1.01      | v2_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_3249]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_2039,plain,
% 3.56/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
% 3.56/1.01      | ~ r1_tarski(k2_relat_1(sK2),X0)
% 3.56/1.01      | ~ v1_relat_1(sK2)
% 3.56/1.01      | ~ v1_funct_1(sK2) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_30]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3252,plain,
% 3.56/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.56/1.01      | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
% 3.56/1.01      | ~ v1_relat_1(sK2)
% 3.56/1.01      | ~ v1_funct_1(sK2) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_2039]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_3254,plain,
% 3.56/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 3.56/1.01      | r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.56/1.01      | v1_relat_1(sK2) != iProver_top
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(predicate_to_equality,[status(thm)],[c_3252]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_4436,plain,
% 3.56/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.56/1.01      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.56/1.01      inference(instantiation,[status(thm)],[c_23]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_6810,plain,
% 3.56/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 3.56/1.01      inference(global_propositional_subsumption,
% 3.56/1.01                [status(thm)],
% 3.56/1.01                [c_6614,c_41,c_48,c_39,c_50,c_51,c_1956,c_1957,c_2010,
% 3.56/1.01                 c_2048,c_2389,c_2388,c_2391,c_3245,c_3250,c_3252,c_3254,
% 3.56/1.01                 c_4436]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_7250,plain,
% 3.56/1.01      ( sK2 != sK2
% 3.56/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.56/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(light_normalisation,[status(thm)],[c_7227,c_6810]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(c_7251,plain,
% 3.56/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.56/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.56/1.01      | v1_funct_1(sK2) != iProver_top ),
% 3.56/1.01      inference(equality_resolution_simp,[status(thm)],[c_7250]) ).
% 3.56/1.01  
% 3.56/1.01  cnf(contradiction,plain,
% 3.56/1.01      ( $false ),
% 3.56/1.01      inference(minisat,
% 3.56/1.01                [status(thm)],
% 3.56/1.01                [c_7251,c_3254,c_2391,c_2389,c_1957,c_50,c_48]) ).
% 3.56/1.01  
% 3.56/1.01  
% 3.56/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 3.56/1.01  
% 3.56/1.01  ------                               Statistics
% 3.56/1.01  
% 3.56/1.01  ------ General
% 3.56/1.01  
% 3.56/1.01  abstr_ref_over_cycles:                  0
% 3.56/1.01  abstr_ref_under_cycles:                 0
% 3.56/1.01  gc_basic_clause_elim:                   0
% 3.56/1.01  forced_gc_time:                         0
% 3.56/1.01  parsing_time:                           0.014
% 3.56/1.01  unif_index_cands_time:                  0.
% 3.56/1.01  unif_index_add_time:                    0.
% 3.56/1.01  orderings_time:                         0.
% 3.56/1.01  out_proof_time:                         0.014
% 3.56/1.01  total_time:                             0.26
% 3.56/1.01  num_of_symbols:                         57
% 3.56/1.01  num_of_terms:                           6445
% 3.56/1.01  
% 3.56/1.01  ------ Preprocessing
% 3.56/1.01  
% 3.56/1.01  num_of_splits:                          1
% 3.56/1.01  num_of_split_atoms:                     1
% 3.56/1.01  num_of_reused_defs:                     0
% 3.56/1.01  num_eq_ax_congr_red:                    6
% 3.56/1.01  num_of_sem_filtered_clauses:            1
% 3.56/1.01  num_of_subtypes:                        0
% 3.56/1.01  monotx_restored_types:                  0
% 3.56/1.01  sat_num_of_epr_types:                   0
% 3.56/1.01  sat_num_of_non_cyclic_types:            0
% 3.56/1.01  sat_guarded_non_collapsed_types:        0
% 3.56/1.01  num_pure_diseq_elim:                    0
% 3.56/1.01  simp_replaced_by:                       0
% 3.56/1.01  res_preprocessed:                       199
% 3.56/1.01  prep_upred:                             0
% 3.56/1.01  prep_unflattend:                        6
% 3.56/1.01  smt_new_axioms:                         0
% 3.56/1.01  pred_elim_cands:                        6
% 3.56/1.01  pred_elim:                              4
% 3.56/1.01  pred_elim_cl:                           4
% 3.56/1.01  pred_elim_cycles:                       6
% 3.56/1.01  merged_defs:                            8
% 3.56/1.01  merged_defs_ncl:                        0
% 3.56/1.01  bin_hyper_res:                          8
% 3.56/1.01  prep_cycles:                            4
% 3.56/1.01  pred_elim_time:                         0.004
% 3.56/1.01  splitting_time:                         0.
% 3.56/1.01  sem_filter_time:                        0.
% 3.56/1.01  monotx_time:                            0.001
% 3.56/1.01  subtype_inf_time:                       0.
% 3.56/1.01  
% 3.56/1.01  ------ Problem properties
% 3.56/1.01  
% 3.56/1.01  clauses:                                40
% 3.56/1.01  conjectures:                            5
% 3.56/1.01  epr:                                    5
% 3.56/1.01  horn:                                   37
% 3.56/1.01  ground:                                 9
% 3.56/1.01  unary:                                  15
% 3.56/1.01  binary:                                 5
% 3.56/1.01  lits:                                   116
% 3.56/1.01  lits_eq:                                29
% 3.56/1.01  fd_pure:                                0
% 3.56/1.01  fd_pseudo:                              0
% 3.56/1.01  fd_cond:                                3
% 3.56/1.01  fd_pseudo_cond:                         1
% 3.56/1.01  ac_symbols:                             0
% 3.56/1.01  
% 3.56/1.01  ------ Propositional Solver
% 3.56/1.01  
% 3.56/1.01  prop_solver_calls:                      27
% 3.56/1.01  prop_fast_solver_calls:                 1404
% 3.56/1.01  smt_solver_calls:                       0
% 3.56/1.01  smt_fast_solver_calls:                  0
% 3.56/1.01  prop_num_of_clauses:                    2540
% 3.56/1.01  prop_preprocess_simplified:             8106
% 3.56/1.01  prop_fo_subsumed:                       41
% 3.56/1.01  prop_solver_time:                       0.
% 3.56/1.01  smt_solver_time:                        0.
% 3.56/1.01  smt_fast_solver_time:                   0.
% 3.56/1.01  prop_fast_solver_time:                  0.
% 3.56/1.01  prop_unsat_core_time:                   0.
% 3.56/1.01  
% 3.56/1.01  ------ QBF
% 3.56/1.01  
% 3.56/1.01  qbf_q_res:                              0
% 3.56/1.01  qbf_num_tautologies:                    0
% 3.56/1.01  qbf_prep_cycles:                        0
% 3.56/1.01  
% 3.56/1.01  ------ BMC1
% 3.56/1.01  
% 3.56/1.01  bmc1_current_bound:                     -1
% 3.56/1.01  bmc1_last_solved_bound:                 -1
% 3.56/1.01  bmc1_unsat_core_size:                   -1
% 3.56/1.01  bmc1_unsat_core_parents_size:           -1
% 3.56/1.01  bmc1_merge_next_fun:                    0
% 3.56/1.01  bmc1_unsat_core_clauses_time:           0.
% 3.56/1.01  
% 3.56/1.01  ------ Instantiation
% 3.56/1.01  
% 3.56/1.01  inst_num_of_clauses:                    837
% 3.56/1.01  inst_num_in_passive:                    99
% 3.56/1.01  inst_num_in_active:                     398
% 3.56/1.01  inst_num_in_unprocessed:                340
% 3.56/1.01  inst_num_of_loops:                      430
% 3.56/1.01  inst_num_of_learning_restarts:          0
% 3.56/1.01  inst_num_moves_active_passive:          30
% 3.56/1.01  inst_lit_activity:                      0
% 3.56/1.01  inst_lit_activity_moves:                0
% 3.56/1.01  inst_num_tautologies:                   0
% 3.56/1.01  inst_num_prop_implied:                  0
% 3.56/1.01  inst_num_existing_simplified:           0
% 3.56/1.01  inst_num_eq_res_simplified:             0
% 3.56/1.01  inst_num_child_elim:                    0
% 3.56/1.01  inst_num_of_dismatching_blockings:      179
% 3.56/1.01  inst_num_of_non_proper_insts:           663
% 3.56/1.01  inst_num_of_duplicates:                 0
% 3.56/1.01  inst_inst_num_from_inst_to_res:         0
% 3.56/1.01  inst_dismatching_checking_time:         0.
% 3.56/1.01  
% 3.56/1.01  ------ Resolution
% 3.56/1.01  
% 3.56/1.01  res_num_of_clauses:                     0
% 3.56/1.01  res_num_in_passive:                     0
% 3.56/1.01  res_num_in_active:                      0
% 3.56/1.01  res_num_of_loops:                       203
% 3.56/1.01  res_forward_subset_subsumed:            23
% 3.56/1.01  res_backward_subset_subsumed:           0
% 3.56/1.01  res_forward_subsumed:                   0
% 3.56/1.01  res_backward_subsumed:                  0
% 3.56/1.01  res_forward_subsumption_resolution:     0
% 3.56/1.01  res_backward_subsumption_resolution:    0
% 3.56/1.01  res_clause_to_clause_subsumption:       334
% 3.56/1.01  res_orphan_elimination:                 0
% 3.56/1.01  res_tautology_del:                      52
% 3.56/1.01  res_num_eq_res_simplified:              0
% 3.56/1.01  res_num_sel_changes:                    0
% 3.56/1.01  res_moves_from_active_to_pass:          0
% 3.56/1.01  
% 3.56/1.01  ------ Superposition
% 3.56/1.01  
% 3.56/1.01  sup_time_total:                         0.
% 3.56/1.01  sup_time_generating:                    0.
% 3.56/1.01  sup_time_sim_full:                      0.
% 3.56/1.01  sup_time_sim_immed:                     0.
% 3.56/1.01  
% 3.56/1.01  sup_num_of_clauses:                     155
% 3.56/1.01  sup_num_in_active:                      65
% 3.56/1.01  sup_num_in_passive:                     90
% 3.56/1.01  sup_num_of_loops:                       85
% 3.56/1.01  sup_fw_superposition:                   88
% 3.56/1.01  sup_bw_superposition:                   74
% 3.56/1.01  sup_immediate_simplified:               39
% 3.56/1.01  sup_given_eliminated:                   0
% 3.56/1.01  comparisons_done:                       0
% 3.56/1.01  comparisons_avoided:                    0
% 3.56/1.01  
% 3.56/1.01  ------ Simplifications
% 3.56/1.01  
% 3.56/1.01  
% 3.56/1.01  sim_fw_subset_subsumed:                 9
% 3.56/1.01  sim_bw_subset_subsumed:                 0
% 3.56/1.01  sim_fw_subsumed:                        5
% 3.56/1.01  sim_bw_subsumed:                        0
% 3.56/1.01  sim_fw_subsumption_res:                 1
% 3.56/1.01  sim_bw_subsumption_res:                 0
% 3.56/1.01  sim_tautology_del:                      2
% 3.56/1.01  sim_eq_tautology_del:                   6
% 3.56/1.01  sim_eq_res_simp:                        1
% 3.56/1.01  sim_fw_demodulated:                     9
% 3.56/1.01  sim_bw_demodulated:                     22
% 3.56/1.01  sim_light_normalised:                   30
% 3.56/1.01  sim_joinable_taut:                      0
% 3.56/1.01  sim_joinable_simp:                      0
% 3.56/1.01  sim_ac_normalised:                      0
% 3.56/1.01  sim_smt_subsumption:                    0
% 3.56/1.01  
%------------------------------------------------------------------------------
