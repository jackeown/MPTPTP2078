%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:59 EST 2020

% Result     : Theorem 3.04s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :  199 (4208 expanded)
%              Number of clauses        :  125 (1152 expanded)
%              Number of leaves         :   18 (1242 expanded)
%              Depth                    :   27
%              Number of atoms          :  683 (30232 expanded)
%              Number of equality atoms :  311 (10352 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f57,plain,(
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

fof(f56,plain,(
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

fof(f55,plain,
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

fof(f58,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f57,f56,f55])).

fof(f97,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f58])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f89,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f94,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f92,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f58])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f98,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f16,axiom,(
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

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f95,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f96,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f58])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f99,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f58])).

fof(f14,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f66,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f20,axiom,(
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
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f100,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f51])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f63])).

fof(f62,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f102,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f62])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f65,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f90,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_36,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1754,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_30,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_39,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_417,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_39])).

cnf(c_418,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_41,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_422,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_41])).

cnf(c_423,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_422])).

cnf(c_1795,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1754,c_418,c_423])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1762,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_2886,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1795,c_1762])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1788,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_35,c_418,c_423])).

cnf(c_3127,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2886,c_1788])).

cnf(c_3138,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3127,c_1795])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_24,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_429,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_9,c_24])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_433,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_429,c_24,c_9,c_8])).

cnf(c_434,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_433])).

cnf(c_515,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_26,c_434])).

cnf(c_519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_515,c_26,c_8,c_429])).

cnf(c_520,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_519])).

cnf(c_1750,plain,
    ( k1_relat_1(X0) = X1
    | k1_xboole_0 = X2
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_520])).

cnf(c_4183,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3138,c_1750])).

cnf(c_38,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_37,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1753,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_1785,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1753,c_418,c_423])).

cnf(c_3139,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3127,c_1785])).

cnf(c_3165,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3139])).

cnf(c_4213,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4183])).

cnf(c_4887,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4183,c_38,c_3165,c_4213])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_34,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_668,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_34])).

cnf(c_669,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_668])).

cnf(c_673,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_669,c_38])).

cnf(c_674,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_673])).

cnf(c_1744,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_2645,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1788,c_1744])).

cnf(c_2905,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2645,c_1785,c_1795])).

cnf(c_3134,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3127,c_2905])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1755,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5441,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3134,c_1755])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_644,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_34])).

cnf(c_645,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_649,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_funct_2(k2_funct_1(sK2),X0,X1)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_645,c_38])).

cnf(c_650,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(renaming,[status(thm)],[c_649])).

cnf(c_1745,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_2360,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1788,c_1745])).

cnf(c_2456,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2360,c_1785,c_1795])).

cnf(c_3137,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3127,c_2456])).

cnf(c_5733,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5441,c_3137])).

cnf(c_5734,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5733])).

cnf(c_3795,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3134,c_1762])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_706,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_34])).

cnf(c_707,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_706])).

cnf(c_709,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_707,c_38])).

cnf(c_746,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_709])).

cnf(c_747,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_746])).

cnf(c_1743,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_2025,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_2648,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1743,c_36,c_2025])).

cnf(c_3803,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3795,c_2648])).

cnf(c_32,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_596,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_34])).

cnf(c_597,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_596])).

cnf(c_601,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_597,c_38])).

cnf(c_602,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_601])).

cnf(c_1747,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_602])).

cnf(c_2466,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1788,c_1747])).

cnf(c_2527,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2466,c_1785,c_1795])).

cnf(c_33,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1888,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_33,c_418,c_423])).

cnf(c_2530,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2527,c_1888])).

cnf(c_3135,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3127,c_2530])).

cnf(c_3992,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3803,c_3135])).

cnf(c_5739,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5734,c_3992])).

cnf(c_5902,plain,
    ( k2_struct_0(sK0) = k1_xboole_0
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4887,c_5739])).

cnf(c_3133,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3127,c_2886])).

cnf(c_6437,plain,
    ( k2_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2) = k2_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5902,c_3133])).

cnf(c_6952,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6437,c_1744])).

cnf(c_2,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_3,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_6960,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k1_xboole_0,k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6952,c_2,c_3])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_128,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6433,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5902,c_3134])).

cnf(c_6462,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6433,c_2])).

cnf(c_13,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_539,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_xboole_0(X1)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_13,c_434])).

cnf(c_543,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_539,c_24,c_13,c_9,c_8])).

cnf(c_1749,plain,
    ( k1_relat_1(X0) = X1
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_543])).

cnf(c_3338,plain,
    ( k1_relat_1(X0) = X1
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2,c_1749])).

cnf(c_7169,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = X0
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6462,c_3338])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_692,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_34])).

cnf(c_693,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_695,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_38])).

cnf(c_758,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_695])).

cnf(c_759,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_758])).

cnf(c_1742,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_2028,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_759])).

cnf(c_2105,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1742,c_36,c_2028])).

cnf(c_7173,plain,
    ( k2_relat_1(sK2) = X0
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7169,c_2105])).

cnf(c_7195,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_7173])).

cnf(c_7411,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6960,c_128,c_7195])).

cnf(c_31,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_40,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_404,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_40])).

cnf(c_405,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_404])).

cnf(c_407,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_405,c_39])).

cnf(c_1751,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_407])).

cnf(c_1780,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1751,c_418])).

cnf(c_3140,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3127,c_1780])).

cnf(c_7429,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7411,c_3140])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_7429,c_128])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:00:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.04/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.04/0.99  
% 3.04/0.99  ------  iProver source info
% 3.04/0.99  
% 3.04/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.04/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.04/0.99  git: non_committed_changes: false
% 3.04/0.99  git: last_make_outside_of_git: false
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options
% 3.04/0.99  
% 3.04/0.99  --out_options                           all
% 3.04/0.99  --tptp_safe_out                         true
% 3.04/0.99  --problem_path                          ""
% 3.04/0.99  --include_path                          ""
% 3.04/0.99  --clausifier                            res/vclausify_rel
% 3.04/0.99  --clausifier_options                    --mode clausify
% 3.04/0.99  --stdin                                 false
% 3.04/0.99  --stats_out                             all
% 3.04/0.99  
% 3.04/0.99  ------ General Options
% 3.04/0.99  
% 3.04/0.99  --fof                                   false
% 3.04/0.99  --time_out_real                         305.
% 3.04/0.99  --time_out_virtual                      -1.
% 3.04/0.99  --symbol_type_check                     false
% 3.04/0.99  --clausify_out                          false
% 3.04/0.99  --sig_cnt_out                           false
% 3.04/0.99  --trig_cnt_out                          false
% 3.04/0.99  --trig_cnt_out_tolerance                1.
% 3.04/0.99  --trig_cnt_out_sk_spl                   false
% 3.04/0.99  --abstr_cl_out                          false
% 3.04/0.99  
% 3.04/0.99  ------ Global Options
% 3.04/0.99  
% 3.04/0.99  --schedule                              default
% 3.04/0.99  --add_important_lit                     false
% 3.04/0.99  --prop_solver_per_cl                    1000
% 3.04/0.99  --min_unsat_core                        false
% 3.04/0.99  --soft_assumptions                      false
% 3.04/0.99  --soft_lemma_size                       3
% 3.04/0.99  --prop_impl_unit_size                   0
% 3.04/0.99  --prop_impl_unit                        []
% 3.04/0.99  --share_sel_clauses                     true
% 3.04/0.99  --reset_solvers                         false
% 3.04/0.99  --bc_imp_inh                            [conj_cone]
% 3.04/0.99  --conj_cone_tolerance                   3.
% 3.04/0.99  --extra_neg_conj                        none
% 3.04/0.99  --large_theory_mode                     true
% 3.04/0.99  --prolific_symb_bound                   200
% 3.04/0.99  --lt_threshold                          2000
% 3.04/0.99  --clause_weak_htbl                      true
% 3.04/0.99  --gc_record_bc_elim                     false
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing Options
% 3.04/0.99  
% 3.04/0.99  --preprocessing_flag                    true
% 3.04/0.99  --time_out_prep_mult                    0.1
% 3.04/0.99  --splitting_mode                        input
% 3.04/0.99  --splitting_grd                         true
% 3.04/0.99  --splitting_cvd                         false
% 3.04/0.99  --splitting_cvd_svl                     false
% 3.04/0.99  --splitting_nvd                         32
% 3.04/0.99  --sub_typing                            true
% 3.04/0.99  --prep_gs_sim                           true
% 3.04/0.99  --prep_unflatten                        true
% 3.04/0.99  --prep_res_sim                          true
% 3.04/0.99  --prep_upred                            true
% 3.04/0.99  --prep_sem_filter                       exhaustive
% 3.04/0.99  --prep_sem_filter_out                   false
% 3.04/0.99  --pred_elim                             true
% 3.04/0.99  --res_sim_input                         true
% 3.04/0.99  --eq_ax_congr_red                       true
% 3.04/0.99  --pure_diseq_elim                       true
% 3.04/0.99  --brand_transform                       false
% 3.04/0.99  --non_eq_to_eq                          false
% 3.04/0.99  --prep_def_merge                        true
% 3.04/0.99  --prep_def_merge_prop_impl              false
% 3.04/0.99  --prep_def_merge_mbd                    true
% 3.04/0.99  --prep_def_merge_tr_red                 false
% 3.04/0.99  --prep_def_merge_tr_cl                  false
% 3.04/0.99  --smt_preprocessing                     true
% 3.04/0.99  --smt_ac_axioms                         fast
% 3.04/0.99  --preprocessed_out                      false
% 3.04/0.99  --preprocessed_stats                    false
% 3.04/0.99  
% 3.04/0.99  ------ Abstraction refinement Options
% 3.04/0.99  
% 3.04/0.99  --abstr_ref                             []
% 3.04/0.99  --abstr_ref_prep                        false
% 3.04/0.99  --abstr_ref_until_sat                   false
% 3.04/0.99  --abstr_ref_sig_restrict                funpre
% 3.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.99  --abstr_ref_under                       []
% 3.04/0.99  
% 3.04/0.99  ------ SAT Options
% 3.04/0.99  
% 3.04/0.99  --sat_mode                              false
% 3.04/0.99  --sat_fm_restart_options                ""
% 3.04/0.99  --sat_gr_def                            false
% 3.04/0.99  --sat_epr_types                         true
% 3.04/0.99  --sat_non_cyclic_types                  false
% 3.04/0.99  --sat_finite_models                     false
% 3.04/0.99  --sat_fm_lemmas                         false
% 3.04/0.99  --sat_fm_prep                           false
% 3.04/0.99  --sat_fm_uc_incr                        true
% 3.04/0.99  --sat_out_model                         small
% 3.04/0.99  --sat_out_clauses                       false
% 3.04/0.99  
% 3.04/0.99  ------ QBF Options
% 3.04/0.99  
% 3.04/0.99  --qbf_mode                              false
% 3.04/0.99  --qbf_elim_univ                         false
% 3.04/0.99  --qbf_dom_inst                          none
% 3.04/0.99  --qbf_dom_pre_inst                      false
% 3.04/0.99  --qbf_sk_in                             false
% 3.04/0.99  --qbf_pred_elim                         true
% 3.04/0.99  --qbf_split                             512
% 3.04/0.99  
% 3.04/0.99  ------ BMC1 Options
% 3.04/0.99  
% 3.04/0.99  --bmc1_incremental                      false
% 3.04/0.99  --bmc1_axioms                           reachable_all
% 3.04/0.99  --bmc1_min_bound                        0
% 3.04/0.99  --bmc1_max_bound                        -1
% 3.04/0.99  --bmc1_max_bound_default                -1
% 3.04/0.99  --bmc1_symbol_reachability              true
% 3.04/0.99  --bmc1_property_lemmas                  false
% 3.04/0.99  --bmc1_k_induction                      false
% 3.04/0.99  --bmc1_non_equiv_states                 false
% 3.04/0.99  --bmc1_deadlock                         false
% 3.04/0.99  --bmc1_ucm                              false
% 3.04/0.99  --bmc1_add_unsat_core                   none
% 3.04/0.99  --bmc1_unsat_core_children              false
% 3.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.99  --bmc1_out_stat                         full
% 3.04/0.99  --bmc1_ground_init                      false
% 3.04/0.99  --bmc1_pre_inst_next_state              false
% 3.04/0.99  --bmc1_pre_inst_state                   false
% 3.04/0.99  --bmc1_pre_inst_reach_state             false
% 3.04/0.99  --bmc1_out_unsat_core                   false
% 3.04/0.99  --bmc1_aig_witness_out                  false
% 3.04/0.99  --bmc1_verbose                          false
% 3.04/0.99  --bmc1_dump_clauses_tptp                false
% 3.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.99  --bmc1_dump_file                        -
% 3.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.99  --bmc1_ucm_extend_mode                  1
% 3.04/0.99  --bmc1_ucm_init_mode                    2
% 3.04/0.99  --bmc1_ucm_cone_mode                    none
% 3.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.99  --bmc1_ucm_relax_model                  4
% 3.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.99  --bmc1_ucm_layered_model                none
% 3.04/0.99  --bmc1_ucm_max_lemma_size               10
% 3.04/0.99  
% 3.04/0.99  ------ AIG Options
% 3.04/0.99  
% 3.04/0.99  --aig_mode                              false
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation Options
% 3.04/0.99  
% 3.04/0.99  --instantiation_flag                    true
% 3.04/0.99  --inst_sos_flag                         false
% 3.04/0.99  --inst_sos_phase                        true
% 3.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel_side                     num_symb
% 3.04/0.99  --inst_solver_per_active                1400
% 3.04/0.99  --inst_solver_calls_frac                1.
% 3.04/0.99  --inst_passive_queue_type               priority_queues
% 3.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.99  --inst_passive_queues_freq              [25;2]
% 3.04/0.99  --inst_dismatching                      true
% 3.04/0.99  --inst_eager_unprocessed_to_passive     true
% 3.04/0.99  --inst_prop_sim_given                   true
% 3.04/0.99  --inst_prop_sim_new                     false
% 3.04/0.99  --inst_subs_new                         false
% 3.04/0.99  --inst_eq_res_simp                      false
% 3.04/0.99  --inst_subs_given                       false
% 3.04/0.99  --inst_orphan_elimination               true
% 3.04/0.99  --inst_learning_loop_flag               true
% 3.04/0.99  --inst_learning_start                   3000
% 3.04/0.99  --inst_learning_factor                  2
% 3.04/0.99  --inst_start_prop_sim_after_learn       3
% 3.04/0.99  --inst_sel_renew                        solver
% 3.04/0.99  --inst_lit_activity_flag                true
% 3.04/0.99  --inst_restr_to_given                   false
% 3.04/0.99  --inst_activity_threshold               500
% 3.04/0.99  --inst_out_proof                        true
% 3.04/0.99  
% 3.04/0.99  ------ Resolution Options
% 3.04/0.99  
% 3.04/0.99  --resolution_flag                       true
% 3.04/0.99  --res_lit_sel                           adaptive
% 3.04/0.99  --res_lit_sel_side                      none
% 3.04/0.99  --res_ordering                          kbo
% 3.04/0.99  --res_to_prop_solver                    active
% 3.04/0.99  --res_prop_simpl_new                    false
% 3.04/0.99  --res_prop_simpl_given                  true
% 3.04/0.99  --res_passive_queue_type                priority_queues
% 3.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.99  --res_passive_queues_freq               [15;5]
% 3.04/0.99  --res_forward_subs                      full
% 3.04/0.99  --res_backward_subs                     full
% 3.04/0.99  --res_forward_subs_resolution           true
% 3.04/0.99  --res_backward_subs_resolution          true
% 3.04/0.99  --res_orphan_elimination                true
% 3.04/0.99  --res_time_limit                        2.
% 3.04/0.99  --res_out_proof                         true
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Options
% 3.04/0.99  
% 3.04/0.99  --superposition_flag                    true
% 3.04/0.99  --sup_passive_queue_type                priority_queues
% 3.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.99  --demod_completeness_check              fast
% 3.04/0.99  --demod_use_ground                      true
% 3.04/0.99  --sup_to_prop_solver                    passive
% 3.04/0.99  --sup_prop_simpl_new                    true
% 3.04/0.99  --sup_prop_simpl_given                  true
% 3.04/0.99  --sup_fun_splitting                     false
% 3.04/0.99  --sup_smt_interval                      50000
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Simplification Setup
% 3.04/0.99  
% 3.04/0.99  --sup_indices_passive                   []
% 3.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_full_bw                           [BwDemod]
% 3.04/0.99  --sup_immed_triv                        [TrivRules]
% 3.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_immed_bw_main                     []
% 3.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  
% 3.04/0.99  ------ Combination Options
% 3.04/0.99  
% 3.04/0.99  --comb_res_mult                         3
% 3.04/0.99  --comb_sup_mult                         2
% 3.04/0.99  --comb_inst_mult                        10
% 3.04/0.99  
% 3.04/0.99  ------ Debug Options
% 3.04/0.99  
% 3.04/0.99  --dbg_backtrace                         false
% 3.04/0.99  --dbg_dump_prop_clauses                 false
% 3.04/0.99  --dbg_dump_prop_clauses_file            -
% 3.04/0.99  --dbg_out_stat                          false
% 3.04/0.99  ------ Parsing...
% 3.04/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.04/0.99  ------ Proving...
% 3.04/0.99  ------ Problem Properties 
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  clauses                                 33
% 3.04/0.99  conjectures                             5
% 3.04/0.99  EPR                                     3
% 3.04/0.99  Horn                                    26
% 3.04/0.99  unary                                   11
% 3.04/0.99  binary                                  5
% 3.04/0.99  lits                                    86
% 3.04/0.99  lits eq                                 32
% 3.04/0.99  fd_pure                                 0
% 3.04/0.99  fd_pseudo                               0
% 3.04/0.99  fd_cond                                 5
% 3.04/0.99  fd_pseudo_cond                          2
% 3.04/0.99  AC symbols                              0
% 3.04/0.99  
% 3.04/0.99  ------ Schedule dynamic 5 is on 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ 
% 3.04/0.99  Current options:
% 3.04/0.99  ------ 
% 3.04/0.99  
% 3.04/0.99  ------ Input Options
% 3.04/0.99  
% 3.04/0.99  --out_options                           all
% 3.04/0.99  --tptp_safe_out                         true
% 3.04/0.99  --problem_path                          ""
% 3.04/0.99  --include_path                          ""
% 3.04/0.99  --clausifier                            res/vclausify_rel
% 3.04/0.99  --clausifier_options                    --mode clausify
% 3.04/0.99  --stdin                                 false
% 3.04/0.99  --stats_out                             all
% 3.04/0.99  
% 3.04/0.99  ------ General Options
% 3.04/0.99  
% 3.04/0.99  --fof                                   false
% 3.04/0.99  --time_out_real                         305.
% 3.04/0.99  --time_out_virtual                      -1.
% 3.04/0.99  --symbol_type_check                     false
% 3.04/0.99  --clausify_out                          false
% 3.04/0.99  --sig_cnt_out                           false
% 3.04/0.99  --trig_cnt_out                          false
% 3.04/0.99  --trig_cnt_out_tolerance                1.
% 3.04/0.99  --trig_cnt_out_sk_spl                   false
% 3.04/0.99  --abstr_cl_out                          false
% 3.04/0.99  
% 3.04/0.99  ------ Global Options
% 3.04/0.99  
% 3.04/0.99  --schedule                              default
% 3.04/0.99  --add_important_lit                     false
% 3.04/0.99  --prop_solver_per_cl                    1000
% 3.04/0.99  --min_unsat_core                        false
% 3.04/0.99  --soft_assumptions                      false
% 3.04/0.99  --soft_lemma_size                       3
% 3.04/0.99  --prop_impl_unit_size                   0
% 3.04/0.99  --prop_impl_unit                        []
% 3.04/0.99  --share_sel_clauses                     true
% 3.04/0.99  --reset_solvers                         false
% 3.04/0.99  --bc_imp_inh                            [conj_cone]
% 3.04/0.99  --conj_cone_tolerance                   3.
% 3.04/0.99  --extra_neg_conj                        none
% 3.04/0.99  --large_theory_mode                     true
% 3.04/0.99  --prolific_symb_bound                   200
% 3.04/0.99  --lt_threshold                          2000
% 3.04/0.99  --clause_weak_htbl                      true
% 3.04/0.99  --gc_record_bc_elim                     false
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing Options
% 3.04/0.99  
% 3.04/0.99  --preprocessing_flag                    true
% 3.04/0.99  --time_out_prep_mult                    0.1
% 3.04/0.99  --splitting_mode                        input
% 3.04/0.99  --splitting_grd                         true
% 3.04/0.99  --splitting_cvd                         false
% 3.04/0.99  --splitting_cvd_svl                     false
% 3.04/0.99  --splitting_nvd                         32
% 3.04/0.99  --sub_typing                            true
% 3.04/0.99  --prep_gs_sim                           true
% 3.04/0.99  --prep_unflatten                        true
% 3.04/0.99  --prep_res_sim                          true
% 3.04/0.99  --prep_upred                            true
% 3.04/0.99  --prep_sem_filter                       exhaustive
% 3.04/0.99  --prep_sem_filter_out                   false
% 3.04/0.99  --pred_elim                             true
% 3.04/0.99  --res_sim_input                         true
% 3.04/0.99  --eq_ax_congr_red                       true
% 3.04/0.99  --pure_diseq_elim                       true
% 3.04/0.99  --brand_transform                       false
% 3.04/0.99  --non_eq_to_eq                          false
% 3.04/0.99  --prep_def_merge                        true
% 3.04/0.99  --prep_def_merge_prop_impl              false
% 3.04/0.99  --prep_def_merge_mbd                    true
% 3.04/0.99  --prep_def_merge_tr_red                 false
% 3.04/0.99  --prep_def_merge_tr_cl                  false
% 3.04/0.99  --smt_preprocessing                     true
% 3.04/0.99  --smt_ac_axioms                         fast
% 3.04/0.99  --preprocessed_out                      false
% 3.04/0.99  --preprocessed_stats                    false
% 3.04/0.99  
% 3.04/0.99  ------ Abstraction refinement Options
% 3.04/0.99  
% 3.04/0.99  --abstr_ref                             []
% 3.04/0.99  --abstr_ref_prep                        false
% 3.04/0.99  --abstr_ref_until_sat                   false
% 3.04/0.99  --abstr_ref_sig_restrict                funpre
% 3.04/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.04/0.99  --abstr_ref_under                       []
% 3.04/0.99  
% 3.04/0.99  ------ SAT Options
% 3.04/0.99  
% 3.04/0.99  --sat_mode                              false
% 3.04/0.99  --sat_fm_restart_options                ""
% 3.04/0.99  --sat_gr_def                            false
% 3.04/0.99  --sat_epr_types                         true
% 3.04/0.99  --sat_non_cyclic_types                  false
% 3.04/0.99  --sat_finite_models                     false
% 3.04/0.99  --sat_fm_lemmas                         false
% 3.04/0.99  --sat_fm_prep                           false
% 3.04/0.99  --sat_fm_uc_incr                        true
% 3.04/0.99  --sat_out_model                         small
% 3.04/0.99  --sat_out_clauses                       false
% 3.04/0.99  
% 3.04/0.99  ------ QBF Options
% 3.04/0.99  
% 3.04/0.99  --qbf_mode                              false
% 3.04/0.99  --qbf_elim_univ                         false
% 3.04/0.99  --qbf_dom_inst                          none
% 3.04/0.99  --qbf_dom_pre_inst                      false
% 3.04/0.99  --qbf_sk_in                             false
% 3.04/0.99  --qbf_pred_elim                         true
% 3.04/0.99  --qbf_split                             512
% 3.04/0.99  
% 3.04/0.99  ------ BMC1 Options
% 3.04/0.99  
% 3.04/0.99  --bmc1_incremental                      false
% 3.04/0.99  --bmc1_axioms                           reachable_all
% 3.04/0.99  --bmc1_min_bound                        0
% 3.04/0.99  --bmc1_max_bound                        -1
% 3.04/0.99  --bmc1_max_bound_default                -1
% 3.04/0.99  --bmc1_symbol_reachability              true
% 3.04/0.99  --bmc1_property_lemmas                  false
% 3.04/0.99  --bmc1_k_induction                      false
% 3.04/0.99  --bmc1_non_equiv_states                 false
% 3.04/0.99  --bmc1_deadlock                         false
% 3.04/0.99  --bmc1_ucm                              false
% 3.04/0.99  --bmc1_add_unsat_core                   none
% 3.04/0.99  --bmc1_unsat_core_children              false
% 3.04/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.04/0.99  --bmc1_out_stat                         full
% 3.04/0.99  --bmc1_ground_init                      false
% 3.04/0.99  --bmc1_pre_inst_next_state              false
% 3.04/0.99  --bmc1_pre_inst_state                   false
% 3.04/0.99  --bmc1_pre_inst_reach_state             false
% 3.04/0.99  --bmc1_out_unsat_core                   false
% 3.04/0.99  --bmc1_aig_witness_out                  false
% 3.04/0.99  --bmc1_verbose                          false
% 3.04/0.99  --bmc1_dump_clauses_tptp                false
% 3.04/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.04/0.99  --bmc1_dump_file                        -
% 3.04/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.04/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.04/0.99  --bmc1_ucm_extend_mode                  1
% 3.04/0.99  --bmc1_ucm_init_mode                    2
% 3.04/0.99  --bmc1_ucm_cone_mode                    none
% 3.04/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.04/0.99  --bmc1_ucm_relax_model                  4
% 3.04/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.04/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.04/0.99  --bmc1_ucm_layered_model                none
% 3.04/0.99  --bmc1_ucm_max_lemma_size               10
% 3.04/0.99  
% 3.04/0.99  ------ AIG Options
% 3.04/0.99  
% 3.04/0.99  --aig_mode                              false
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation Options
% 3.04/0.99  
% 3.04/0.99  --instantiation_flag                    true
% 3.04/0.99  --inst_sos_flag                         false
% 3.04/0.99  --inst_sos_phase                        true
% 3.04/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.04/0.99  --inst_lit_sel_side                     none
% 3.04/0.99  --inst_solver_per_active                1400
% 3.04/0.99  --inst_solver_calls_frac                1.
% 3.04/0.99  --inst_passive_queue_type               priority_queues
% 3.04/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.04/0.99  --inst_passive_queues_freq              [25;2]
% 3.04/0.99  --inst_dismatching                      true
% 3.04/0.99  --inst_eager_unprocessed_to_passive     true
% 3.04/0.99  --inst_prop_sim_given                   true
% 3.04/0.99  --inst_prop_sim_new                     false
% 3.04/0.99  --inst_subs_new                         false
% 3.04/0.99  --inst_eq_res_simp                      false
% 3.04/0.99  --inst_subs_given                       false
% 3.04/0.99  --inst_orphan_elimination               true
% 3.04/0.99  --inst_learning_loop_flag               true
% 3.04/0.99  --inst_learning_start                   3000
% 3.04/0.99  --inst_learning_factor                  2
% 3.04/0.99  --inst_start_prop_sim_after_learn       3
% 3.04/0.99  --inst_sel_renew                        solver
% 3.04/0.99  --inst_lit_activity_flag                true
% 3.04/0.99  --inst_restr_to_given                   false
% 3.04/0.99  --inst_activity_threshold               500
% 3.04/0.99  --inst_out_proof                        true
% 3.04/0.99  
% 3.04/0.99  ------ Resolution Options
% 3.04/0.99  
% 3.04/0.99  --resolution_flag                       false
% 3.04/0.99  --res_lit_sel                           adaptive
% 3.04/0.99  --res_lit_sel_side                      none
% 3.04/0.99  --res_ordering                          kbo
% 3.04/0.99  --res_to_prop_solver                    active
% 3.04/0.99  --res_prop_simpl_new                    false
% 3.04/0.99  --res_prop_simpl_given                  true
% 3.04/0.99  --res_passive_queue_type                priority_queues
% 3.04/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.04/0.99  --res_passive_queues_freq               [15;5]
% 3.04/0.99  --res_forward_subs                      full
% 3.04/0.99  --res_backward_subs                     full
% 3.04/0.99  --res_forward_subs_resolution           true
% 3.04/0.99  --res_backward_subs_resolution          true
% 3.04/0.99  --res_orphan_elimination                true
% 3.04/0.99  --res_time_limit                        2.
% 3.04/0.99  --res_out_proof                         true
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Options
% 3.04/0.99  
% 3.04/0.99  --superposition_flag                    true
% 3.04/0.99  --sup_passive_queue_type                priority_queues
% 3.04/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.04/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.04/0.99  --demod_completeness_check              fast
% 3.04/0.99  --demod_use_ground                      true
% 3.04/0.99  --sup_to_prop_solver                    passive
% 3.04/0.99  --sup_prop_simpl_new                    true
% 3.04/0.99  --sup_prop_simpl_given                  true
% 3.04/0.99  --sup_fun_splitting                     false
% 3.04/0.99  --sup_smt_interval                      50000
% 3.04/0.99  
% 3.04/0.99  ------ Superposition Simplification Setup
% 3.04/0.99  
% 3.04/0.99  --sup_indices_passive                   []
% 3.04/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.04/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.04/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_full_bw                           [BwDemod]
% 3.04/0.99  --sup_immed_triv                        [TrivRules]
% 3.04/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.04/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_immed_bw_main                     []
% 3.04/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.04/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.04/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.04/0.99  
% 3.04/0.99  ------ Combination Options
% 3.04/0.99  
% 3.04/0.99  --comb_res_mult                         3
% 3.04/0.99  --comb_sup_mult                         2
% 3.04/0.99  --comb_inst_mult                        10
% 3.04/0.99  
% 3.04/0.99  ------ Debug Options
% 3.04/0.99  
% 3.04/0.99  --dbg_backtrace                         false
% 3.04/0.99  --dbg_dump_prop_clauses                 false
% 3.04/0.99  --dbg_dump_prop_clauses_file            -
% 3.04/0.99  --dbg_out_stat                          false
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  ------ Proving...
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS status Theorem for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  fof(f21,conjecture,(
% 3.04/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f22,negated_conjecture,(
% 3.04/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.04/0.99    inference(negated_conjecture,[],[f21])).
% 3.04/0.99  
% 3.04/0.99  fof(f49,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f22])).
% 3.04/0.99  
% 3.04/0.99  fof(f50,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f49])).
% 3.04/0.99  
% 3.04/0.99  fof(f57,plain,(
% 3.04/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f56,plain,(
% 3.04/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f55,plain,(
% 3.04/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.04/0.99    introduced(choice_axiom,[])).
% 3.04/0.99  
% 3.04/0.99  fof(f58,plain,(
% 3.04/0.99    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.04/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f57,f56,f55])).
% 3.04/0.99  
% 3.04/0.99  fof(f97,plain,(
% 3.04/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f18,axiom,(
% 3.04/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f44,plain,(
% 3.04/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f18])).
% 3.04/0.99  
% 3.04/0.99  fof(f89,plain,(
% 3.04/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f44])).
% 3.04/0.99  
% 3.04/0.99  fof(f94,plain,(
% 3.04/0.99    l1_struct_0(sK1)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f92,plain,(
% 3.04/0.99    l1_struct_0(sK0)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f11,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f32,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f11])).
% 3.04/0.99  
% 3.04/0.99  fof(f71,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f32])).
% 3.04/0.99  
% 3.04/0.99  fof(f98,plain,(
% 3.04/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f16,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f40,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.04/0.99    inference(ennf_transformation,[],[f16])).
% 3.04/0.99  
% 3.04/0.99  fof(f41,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.04/0.99    inference(flattening,[],[f40])).
% 3.04/0.99  
% 3.04/0.99  fof(f84,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f41])).
% 3.04/0.99  
% 3.04/0.99  fof(f8,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f23,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.04/0.99    inference(pure_predicate_removal,[],[f8])).
% 3.04/0.99  
% 3.04/0.99  fof(f29,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f23])).
% 3.04/0.99  
% 3.04/0.99  fof(f68,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f29])).
% 3.04/0.99  
% 3.04/0.99  fof(f15,axiom,(
% 3.04/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f38,plain,(
% 3.04/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.04/0.99    inference(ennf_transformation,[],[f15])).
% 3.04/0.99  
% 3.04/0.99  fof(f39,plain,(
% 3.04/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.04/0.99    inference(flattening,[],[f38])).
% 3.04/0.99  
% 3.04/0.99  fof(f54,plain,(
% 3.04/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.04/0.99    inference(nnf_transformation,[],[f39])).
% 3.04/0.99  
% 3.04/0.99  fof(f82,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f54])).
% 3.04/0.99  
% 3.04/0.99  fof(f7,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f28,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f7])).
% 3.04/0.99  
% 3.04/0.99  fof(f67,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f28])).
% 3.04/0.99  
% 3.04/0.99  fof(f95,plain,(
% 3.04/0.99    v1_funct_1(sK2)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f96,plain,(
% 3.04/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f17,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f42,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.04/0.99    inference(ennf_transformation,[],[f17])).
% 3.04/0.99  
% 3.04/0.99  fof(f43,plain,(
% 3.04/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.04/0.99    inference(flattening,[],[f42])).
% 3.04/0.99  
% 3.04/0.99  fof(f88,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f43])).
% 3.04/0.99  
% 3.04/0.99  fof(f99,plain,(
% 3.04/0.99    v2_funct_1(sK2)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f14,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f36,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(ennf_transformation,[],[f14])).
% 3.04/0.99  
% 3.04/0.99  fof(f37,plain,(
% 3.04/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(flattening,[],[f36])).
% 3.04/0.99  
% 3.04/0.99  fof(f53,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.04/0.99    inference(nnf_transformation,[],[f37])).
% 3.04/0.99  
% 3.04/0.99  fof(f76,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.04/0.99    inference(cnf_transformation,[],[f53])).
% 3.04/0.99  
% 3.04/0.99  fof(f87,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f43])).
% 3.04/0.99  
% 3.04/0.99  fof(f6,axiom,(
% 3.04/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f26,plain,(
% 3.04/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f6])).
% 3.04/0.99  
% 3.04/0.99  fof(f27,plain,(
% 3.04/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.04/0.99    inference(flattening,[],[f26])).
% 3.04/0.99  
% 3.04/0.99  fof(f66,plain,(
% 3.04/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f27])).
% 3.04/0.99  
% 3.04/0.99  fof(f20,axiom,(
% 3.04/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f47,plain,(
% 3.04/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.04/0.99    inference(ennf_transformation,[],[f20])).
% 3.04/0.99  
% 3.04/0.99  fof(f48,plain,(
% 3.04/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.04/0.99    inference(flattening,[],[f47])).
% 3.04/0.99  
% 3.04/0.99  fof(f91,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f48])).
% 3.04/0.99  
% 3.04/0.99  fof(f100,plain,(
% 3.04/0.99    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  fof(f3,axiom,(
% 3.04/0.99    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f51,plain,(
% 3.04/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.04/0.99    inference(nnf_transformation,[],[f3])).
% 3.04/0.99  
% 3.04/0.99  fof(f52,plain,(
% 3.04/0.99    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.04/0.99    inference(flattening,[],[f51])).
% 3.04/0.99  
% 3.04/0.99  fof(f63,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.04/0.99    inference(cnf_transformation,[],[f52])).
% 3.04/0.99  
% 3.04/0.99  fof(f101,plain,(
% 3.04/0.99    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.04/0.99    inference(equality_resolution,[],[f63])).
% 3.04/0.99  
% 3.04/0.99  fof(f62,plain,(
% 3.04/0.99    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.04/0.99    inference(cnf_transformation,[],[f52])).
% 3.04/0.99  
% 3.04/0.99  fof(f102,plain,(
% 3.04/0.99    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.04/0.99    inference(equality_resolution,[],[f62])).
% 3.04/0.99  
% 3.04/0.99  fof(f1,axiom,(
% 3.04/0.99    v1_xboole_0(k1_xboole_0)),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f59,plain,(
% 3.04/0.99    v1_xboole_0(k1_xboole_0)),
% 3.04/0.99    inference(cnf_transformation,[],[f1])).
% 3.04/0.99  
% 3.04/0.99  fof(f12,axiom,(
% 3.04/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f33,plain,(
% 3.04/0.99    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.04/0.99    inference(ennf_transformation,[],[f12])).
% 3.04/0.99  
% 3.04/0.99  fof(f72,plain,(
% 3.04/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f33])).
% 3.04/0.99  
% 3.04/0.99  fof(f65,plain,(
% 3.04/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f27])).
% 3.04/0.99  
% 3.04/0.99  fof(f19,axiom,(
% 3.04/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.04/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.04/0.99  
% 3.04/0.99  fof(f45,plain,(
% 3.04/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.04/0.99    inference(ennf_transformation,[],[f19])).
% 3.04/0.99  
% 3.04/0.99  fof(f46,plain,(
% 3.04/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.04/0.99    inference(flattening,[],[f45])).
% 3.04/0.99  
% 3.04/0.99  fof(f90,plain,(
% 3.04/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.04/0.99    inference(cnf_transformation,[],[f46])).
% 3.04/0.99  
% 3.04/0.99  fof(f93,plain,(
% 3.04/0.99    ~v2_struct_0(sK1)),
% 3.04/0.99    inference(cnf_transformation,[],[f58])).
% 3.04/0.99  
% 3.04/0.99  cnf(c_36,negated_conjecture,
% 3.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1754,plain,
% 3.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_30,plain,
% 3.04/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_39,negated_conjecture,
% 3.04/0.99      ( l1_struct_0(sK1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_417,plain,
% 3.04/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_39]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_418,plain,
% 3.04/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_417]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_41,negated_conjecture,
% 3.04/0.99      ( l1_struct_0(sK0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f92]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_422,plain,
% 3.04/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_30,c_41]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_423,plain,
% 3.04/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_422]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1795,plain,
% 3.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_1754,c_418,c_423]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_12,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1762,plain,
% 3.04/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.04/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2886,plain,
% 3.04/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1795,c_1762]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_35,negated_conjecture,
% 3.04/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1788,plain,
% 3.04/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_35,c_418,c_423]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3127,plain,
% 3.04/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_2886,c_1788]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3138,plain,
% 3.04/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_3127,c_1795]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_26,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | v1_partfun1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_9,plain,
% 3.04/0.99      ( v4_relat_1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.04/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_24,plain,
% 3.04/0.99      ( ~ v1_partfun1(X0,X1)
% 3.04/0.99      | ~ v4_relat_1(X0,X1)
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | k1_relat_1(X0) = X1 ),
% 3.04/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_429,plain,
% 3.04/0.99      ( ~ v1_partfun1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_relat_1(X0)
% 3.04/0.99      | k1_relat_1(X0) = X1 ),
% 3.04/0.99      inference(resolution,[status(thm)],[c_9,c_24]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_8,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | v1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_433,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_partfun1(X0,X1)
% 3.04/0.99      | k1_relat_1(X0) = X1 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_429,c_24,c_9,c_8]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_434,plain,
% 3.04/0.99      ( ~ v1_partfun1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k1_relat_1(X0) = X1 ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_433]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_515,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | k1_relat_1(X0) = X1
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(resolution,[status(thm)],[c_26,c_434]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_519,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | k1_relat_1(X0) = X1
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_515,c_26,c_8,c_429]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_520,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | k1_relat_1(X0) = X1
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_519]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1750,plain,
% 3.04/0.99      ( k1_relat_1(X0) = X1
% 3.04/0.99      | k1_xboole_0 = X2
% 3.04/0.99      | v1_funct_2(X0,X1,X2) != iProver_top
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.04/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_520]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4183,plain,
% 3.04/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.04/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 3.04/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.04/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_3138,c_1750]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_38,negated_conjecture,
% 3.04/0.99      ( v1_funct_1(sK2) ),
% 3.04/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_37,negated_conjecture,
% 3.04/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f96]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1753,plain,
% 3.04/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1785,plain,
% 3.04/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_1753,c_418,c_423]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3139,plain,
% 3.04/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_3127,c_1785]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3165,plain,
% 3.04/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
% 3.04/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3139]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4213,plain,
% 3.04/0.99      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
% 3.04/0.99      | ~ v1_funct_1(sK2)
% 3.04/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.04/0.99      | k2_relat_1(sK2) = k1_xboole_0 ),
% 3.04/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4183]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_4887,plain,
% 3.04/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.04/0.99      | k2_relat_1(sK2) = k1_xboole_0 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_4183,c_38,c_3165,c_4213]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_27,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v2_funct_1(X0)
% 3.04/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_34,negated_conjecture,
% 3.04/0.99      ( v2_funct_1(sK2) ),
% 3.04/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_668,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.04/0.99      | sK2 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_27,c_34]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_669,plain,
% 3.04/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.04/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | ~ v1_funct_1(sK2)
% 3.04/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_668]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_673,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.04/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.04/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_669,c_38]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_674,plain,
% 3.04/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.04/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_673]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1744,plain,
% 3.04/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 3.04/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.04/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2645,plain,
% 3.04/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 3.04/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1788,c_1744]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2905,plain,
% 3.04/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_2645,c_1785,c_1795]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3134,plain,
% 3.04/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_3127,c_2905]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_22,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.04/0.99      | k1_xboole_0 = X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1755,plain,
% 3.04/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.04/0.99      | k1_xboole_0 = X1
% 3.04/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.04/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5441,plain,
% 3.04/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.04/0.99      | k2_struct_0(sK0) = k1_xboole_0
% 3.04/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_3134,c_1755]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_28,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v2_funct_1(X0)
% 3.04/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f87]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_644,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.04/0.99      | sK2 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_28,c_34]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_645,plain,
% 3.04/0.99      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.04/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 3.04/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.04/0.99      | ~ v1_funct_1(sK2)
% 3.04/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_644]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_649,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.04/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 3.04/0.99      | v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.04/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_645,c_38]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_650,plain,
% 3.04/0.99      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.04/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 3.04/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.04/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_649]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1745,plain,
% 3.04/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 3.04/0.99      | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
% 3.04/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.04/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2360,plain,
% 3.04/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 3.04/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.04/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1788,c_1745]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2456,plain,
% 3.04/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_2360,c_1785,c_1795]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3137,plain,
% 3.04/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_3127,c_2456]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5733,plain,
% 3.04/0.99      ( k2_struct_0(sK0) = k1_xboole_0
% 3.04/0.99      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_5441,c_3137]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5734,plain,
% 3.04/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.04/0.99      | k2_struct_0(sK0) = k1_xboole_0 ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_5733]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3795,plain,
% 3.04/0.99      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_3134,c_1762]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6,plain,
% 3.04/0.99      ( ~ v1_relat_1(X0)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v2_funct_1(X0)
% 3.04/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_706,plain,
% 3.04/0.99      ( ~ v1_relat_1(X0)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.04/0.99      | sK2 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_34]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_707,plain,
% 3.04/0.99      ( ~ v1_relat_1(sK2)
% 3.04/0.99      | ~ v1_funct_1(sK2)
% 3.04/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_706]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_709,plain,
% 3.04/0.99      ( ~ v1_relat_1(sK2)
% 3.04/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_707,c_38]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_746,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.04/0.99      | sK2 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_709]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_747,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_746]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1743,plain,
% 3.04/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.04/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2025,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.04/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_747]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2648,plain,
% 3.04/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1743,c_36,c_2025]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3803,plain,
% 3.04/0.99      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_3795,c_2648]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_32,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v2_funct_1(X0)
% 3.04/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.04/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.04/0.99      inference(cnf_transformation,[],[f91]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_596,plain,
% 3.04/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.04/0.99      | k2_relset_1(X1,X2,X0) != X2
% 3.04/0.99      | sK2 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_32,c_34]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_597,plain,
% 3.04/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.04/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | ~ v1_funct_1(sK2)
% 3.04/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.04/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_596]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_601,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 3.04/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.04/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_597,c_38]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_602,plain,
% 3.04/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.04/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.04/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.04/0.99      inference(renaming,[status(thm)],[c_601]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1747,plain,
% 3.04/0.99      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.04/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 3.04/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.04/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_602]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2466,plain,
% 3.04/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.04/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.04/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_1788,c_1747]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2527,plain,
% 3.04/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_2466,c_1785,c_1795]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_33,negated_conjecture,
% 3.04/0.99      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.04/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1888,plain,
% 3.04/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.04/0.99      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_33,c_418,c_423]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2530,plain,
% 3.04/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 3.04/0.99      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_2527,c_1888]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3135,plain,
% 3.04/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.04/0.99      | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_3127,c_2530]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3992,plain,
% 3.04/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.04/0.99      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_3803,c_3135]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5739,plain,
% 3.04/0.99      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 3.04/0.99      | k2_struct_0(sK0) = k1_xboole_0 ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_5734,c_3992]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_5902,plain,
% 3.04/0.99      ( k2_struct_0(sK0) = k1_xboole_0 | k2_relat_1(sK2) = k1_xboole_0 ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_4887,c_5739]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3133,plain,
% 3.04/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_3127,c_2886]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6437,plain,
% 3.04/0.99      ( k2_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2) = k2_relat_1(sK2)
% 3.04/0.99      | k2_relat_1(sK2) = k1_xboole_0 ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_5902,c_3133]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6952,plain,
% 3.04/0.99      ( k2_relat_1(sK2) = k1_xboole_0
% 3.04/0.99      | v1_funct_2(sK2,k1_xboole_0,k2_relat_1(sK2)) != iProver_top
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) = iProver_top
% 3.04/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_6437,c_1744]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2,plain,
% 3.04/0.99      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.04/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3,plain,
% 3.04/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.04/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6960,plain,
% 3.04/0.99      ( k2_relat_1(sK2) = k1_xboole_0
% 3.04/0.99      | v1_funct_2(sK2,k1_xboole_0,k2_relat_1(sK2)) != iProver_top
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top
% 3.04/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_6952,c_2,c_3]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_0,plain,
% 3.04/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_128,plain,
% 3.04/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6433,plain,
% 3.04/0.99      ( k2_relat_1(sK2) = k1_xboole_0
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) = iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_5902,c_3134]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_6462,plain,
% 3.04/0.99      ( k2_relat_1(sK2) = k1_xboole_0
% 3.04/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_6433,c_2]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_13,plain,
% 3.04/0.99      ( v1_partfun1(X0,X1)
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_xboole_0(X1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_539,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.04/0.99      | ~ v1_xboole_0(X1)
% 3.04/0.99      | k1_relat_1(X0) = X1 ),
% 3.04/0.99      inference(resolution,[status(thm)],[c_13,c_434]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_543,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | ~ v1_xboole_0(X1)
% 3.04/0.99      | k1_relat_1(X0) = X1 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_539,c_24,c_13,c_9,c_8]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1749,plain,
% 3.04/0.99      ( k1_relat_1(X0) = X1
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.04/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_543]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3338,plain,
% 3.04/0.99      ( k1_relat_1(X0) = X1
% 3.04/0.99      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.04/0.99      | v1_xboole_0(X1) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_2,c_1749]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_7169,plain,
% 3.04/0.99      ( k1_relat_1(k2_funct_1(sK2)) = X0
% 3.04/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 3.04/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.04/0.99      inference(superposition,[status(thm)],[c_6462,c_3338]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_7,plain,
% 3.04/0.99      ( ~ v1_relat_1(X0)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | ~ v2_funct_1(X0)
% 3.04/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.04/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_692,plain,
% 3.04/0.99      ( ~ v1_relat_1(X0)
% 3.04/0.99      | ~ v1_funct_1(X0)
% 3.04/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.04/0.99      | sK2 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_7,c_34]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_693,plain,
% 3.04/0.99      ( ~ v1_relat_1(sK2)
% 3.04/0.99      | ~ v1_funct_1(sK2)
% 3.04/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_692]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_695,plain,
% 3.04/0.99      ( ~ v1_relat_1(sK2)
% 3.04/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_693,c_38]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_758,plain,
% 3.04/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.04/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.04/0.99      | sK2 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_8,c_695]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_759,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.04/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_758]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1742,plain,
% 3.04/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.04/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2028,plain,
% 3.04/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.04/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_759]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_2105,plain,
% 3.04/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_1742,c_36,c_2028]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_7173,plain,
% 3.04/0.99      ( k2_relat_1(sK2) = X0
% 3.04/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 3.04/0.99      | v1_xboole_0(X0) != iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_7169,c_2105]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_7195,plain,
% 3.04/0.99      ( k2_relat_1(sK2) = k1_xboole_0
% 3.04/0.99      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.04/0.99      inference(instantiation,[status(thm)],[c_7173]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_7411,plain,
% 3.04/0.99      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_6960,c_128,c_7195]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_31,plain,
% 3.04/0.99      ( v2_struct_0(X0)
% 3.04/0.99      | ~ l1_struct_0(X0)
% 3.04/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.04/0.99      inference(cnf_transformation,[],[f90]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_40,negated_conjecture,
% 3.04/0.99      ( ~ v2_struct_0(sK1) ),
% 3.04/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_404,plain,
% 3.04/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 3.04/0.99      inference(resolution_lifted,[status(thm)],[c_31,c_40]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_405,plain,
% 3.04/0.99      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.04/0.99      inference(unflattening,[status(thm)],[c_404]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_407,plain,
% 3.04/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.04/0.99      inference(global_propositional_subsumption,
% 3.04/0.99                [status(thm)],
% 3.04/0.99                [c_405,c_39]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1751,plain,
% 3.04/0.99      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 3.04/0.99      inference(predicate_to_equality,[status(thm)],[c_407]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_1780,plain,
% 3.04/0.99      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 3.04/0.99      inference(light_normalisation,[status(thm)],[c_1751,c_418]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_3140,plain,
% 3.04/0.99      ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_3127,c_1780]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(c_7429,plain,
% 3.04/0.99      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.04/0.99      inference(demodulation,[status(thm)],[c_7411,c_3140]) ).
% 3.04/0.99  
% 3.04/0.99  cnf(contradiction,plain,
% 3.04/0.99      ( $false ),
% 3.04/0.99      inference(minisat,[status(thm)],[c_7429,c_128]) ).
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.04/0.99  
% 3.04/0.99  ------                               Statistics
% 3.04/0.99  
% 3.04/0.99  ------ General
% 3.04/0.99  
% 3.04/0.99  abstr_ref_over_cycles:                  0
% 3.04/0.99  abstr_ref_under_cycles:                 0
% 3.04/0.99  gc_basic_clause_elim:                   0
% 3.04/0.99  forced_gc_time:                         0
% 3.04/0.99  parsing_time:                           0.01
% 3.04/0.99  unif_index_cands_time:                  0.
% 3.04/0.99  unif_index_add_time:                    0.
% 3.04/0.99  orderings_time:                         0.
% 3.04/0.99  out_proof_time:                         0.015
% 3.04/0.99  total_time:                             0.232
% 3.04/0.99  num_of_symbols:                         55
% 3.04/0.99  num_of_terms:                           6859
% 3.04/0.99  
% 3.04/0.99  ------ Preprocessing
% 3.04/0.99  
% 3.04/0.99  num_of_splits:                          0
% 3.04/0.99  num_of_split_atoms:                     0
% 3.04/0.99  num_of_reused_defs:                     0
% 3.04/0.99  num_eq_ax_congr_red:                    4
% 3.04/0.99  num_of_sem_filtered_clauses:            1
% 3.04/0.99  num_of_subtypes:                        0
% 3.04/0.99  monotx_restored_types:                  0
% 3.04/0.99  sat_num_of_epr_types:                   0
% 3.04/0.99  sat_num_of_non_cyclic_types:            0
% 3.04/0.99  sat_guarded_non_collapsed_types:        0
% 3.04/0.99  num_pure_diseq_elim:                    0
% 3.04/0.99  simp_replaced_by:                       0
% 3.04/0.99  res_preprocessed:                       172
% 3.04/0.99  prep_upred:                             0
% 3.04/0.99  prep_unflattend:                        29
% 3.04/0.99  smt_new_axioms:                         0
% 3.04/0.99  pred_elim_cands:                        4
% 3.04/0.99  pred_elim:                              6
% 3.04/0.99  pred_elim_cl:                           7
% 3.04/0.99  pred_elim_cycles:                       9
% 3.04/0.99  merged_defs:                            0
% 3.04/0.99  merged_defs_ncl:                        0
% 3.04/0.99  bin_hyper_res:                          0
% 3.04/0.99  prep_cycles:                            4
% 3.04/0.99  pred_elim_time:                         0.015
% 3.04/0.99  splitting_time:                         0.
% 3.04/0.99  sem_filter_time:                        0.
% 3.04/0.99  monotx_time:                            0.001
% 3.04/0.99  subtype_inf_time:                       0.
% 3.04/0.99  
% 3.04/0.99  ------ Problem properties
% 3.04/0.99  
% 3.04/0.99  clauses:                                33
% 3.04/0.99  conjectures:                            5
% 3.04/0.99  epr:                                    3
% 3.04/0.99  horn:                                   26
% 3.04/0.99  ground:                                 9
% 3.04/0.99  unary:                                  11
% 3.04/0.99  binary:                                 5
% 3.04/0.99  lits:                                   86
% 3.04/0.99  lits_eq:                                32
% 3.04/0.99  fd_pure:                                0
% 3.04/0.99  fd_pseudo:                              0
% 3.04/0.99  fd_cond:                                5
% 3.04/0.99  fd_pseudo_cond:                         2
% 3.04/0.99  ac_symbols:                             0
% 3.04/0.99  
% 3.04/0.99  ------ Propositional Solver
% 3.04/0.99  
% 3.04/0.99  prop_solver_calls:                      27
% 3.04/0.99  prop_fast_solver_calls:                 1321
% 3.04/0.99  smt_solver_calls:                       0
% 3.04/0.99  smt_fast_solver_calls:                  0
% 3.04/0.99  prop_num_of_clauses:                    2374
% 3.04/0.99  prop_preprocess_simplified:             7942
% 3.04/0.99  prop_fo_subsumed:                       36
% 3.04/0.99  prop_solver_time:                       0.
% 3.04/0.99  smt_solver_time:                        0.
% 3.04/0.99  smt_fast_solver_time:                   0.
% 3.04/0.99  prop_fast_solver_time:                  0.
% 3.04/0.99  prop_unsat_core_time:                   0.
% 3.04/0.99  
% 3.04/0.99  ------ QBF
% 3.04/0.99  
% 3.04/0.99  qbf_q_res:                              0
% 3.04/0.99  qbf_num_tautologies:                    0
% 3.04/0.99  qbf_prep_cycles:                        0
% 3.04/0.99  
% 3.04/0.99  ------ BMC1
% 3.04/0.99  
% 3.04/0.99  bmc1_current_bound:                     -1
% 3.04/0.99  bmc1_last_solved_bound:                 -1
% 3.04/0.99  bmc1_unsat_core_size:                   -1
% 3.04/0.99  bmc1_unsat_core_parents_size:           -1
% 3.04/0.99  bmc1_merge_next_fun:                    0
% 3.04/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.04/0.99  
% 3.04/0.99  ------ Instantiation
% 3.04/0.99  
% 3.04/0.99  inst_num_of_clauses:                    861
% 3.04/0.99  inst_num_in_passive:                    62
% 3.04/0.99  inst_num_in_active:                     378
% 3.04/0.99  inst_num_in_unprocessed:                421
% 3.04/0.99  inst_num_of_loops:                      420
% 3.04/0.99  inst_num_of_learning_restarts:          0
% 3.04/0.99  inst_num_moves_active_passive:          40
% 3.04/0.99  inst_lit_activity:                      0
% 3.04/0.99  inst_lit_activity_moves:                0
% 3.04/0.99  inst_num_tautologies:                   0
% 3.04/0.99  inst_num_prop_implied:                  0
% 3.04/0.99  inst_num_existing_simplified:           0
% 3.04/0.99  inst_num_eq_res_simplified:             0
% 3.04/0.99  inst_num_child_elim:                    0
% 3.04/0.99  inst_num_of_dismatching_blockings:      209
% 3.04/0.99  inst_num_of_non_proper_insts:           663
% 3.04/0.99  inst_num_of_duplicates:                 0
% 3.04/0.99  inst_inst_num_from_inst_to_res:         0
% 3.04/0.99  inst_dismatching_checking_time:         0.
% 3.04/0.99  
% 3.04/0.99  ------ Resolution
% 3.04/0.99  
% 3.04/0.99  res_num_of_clauses:                     0
% 3.04/0.99  res_num_in_passive:                     0
% 3.04/0.99  res_num_in_active:                      0
% 3.04/0.99  res_num_of_loops:                       176
% 3.04/0.99  res_forward_subset_subsumed:            101
% 3.04/0.99  res_backward_subset_subsumed:           2
% 3.04/0.99  res_forward_subsumed:                   0
% 3.04/0.99  res_backward_subsumed:                  0
% 3.04/0.99  res_forward_subsumption_resolution:     1
% 3.04/0.99  res_backward_subsumption_resolution:    0
% 3.04/0.99  res_clause_to_clause_subsumption:       309
% 3.04/0.99  res_orphan_elimination:                 0
% 3.04/0.99  res_tautology_del:                      38
% 3.04/0.99  res_num_eq_res_simplified:              0
% 3.04/0.99  res_num_sel_changes:                    0
% 3.04/0.99  res_moves_from_active_to_pass:          0
% 3.04/0.99  
% 3.04/0.99  ------ Superposition
% 3.04/0.99  
% 3.04/0.99  sup_time_total:                         0.
% 3.04/0.99  sup_time_generating:                    0.
% 3.04/0.99  sup_time_sim_full:                      0.
% 3.04/0.99  sup_time_sim_immed:                     0.
% 3.04/0.99  
% 3.04/0.99  sup_num_of_clauses:                     78
% 3.04/0.99  sup_num_in_active:                      43
% 3.04/0.99  sup_num_in_passive:                     35
% 3.04/0.99  sup_num_of_loops:                       82
% 3.04/0.99  sup_fw_superposition:                   46
% 3.04/0.99  sup_bw_superposition:                   87
% 3.04/0.99  sup_immediate_simplified:               48
% 3.04/0.99  sup_given_eliminated:                   0
% 3.04/0.99  comparisons_done:                       0
% 3.04/0.99  comparisons_avoided:                    15
% 3.04/0.99  
% 3.04/0.99  ------ Simplifications
% 3.04/0.99  
% 3.04/0.99  
% 3.04/0.99  sim_fw_subset_subsumed:                 32
% 3.04/0.99  sim_bw_subset_subsumed:                 18
% 3.04/0.99  sim_fw_subsumed:                        5
% 3.04/0.99  sim_bw_subsumed:                        1
% 3.04/0.99  sim_fw_subsumption_res:                 2
% 3.04/0.99  sim_bw_subsumption_res:                 0
% 3.04/0.99  sim_tautology_del:                      1
% 3.04/0.99  sim_eq_tautology_del:                   15
% 3.04/0.99  sim_eq_res_simp:                        0
% 3.04/0.99  sim_fw_demodulated:                     8
% 3.04/0.99  sim_bw_demodulated:                     31
% 3.04/0.99  sim_light_normalised:                   14
% 3.04/0.99  sim_joinable_taut:                      0
% 3.04/0.99  sim_joinable_simp:                      0
% 3.04/0.99  sim_ac_normalised:                      0
% 3.04/0.99  sim_smt_subsumption:                    0
% 3.04/0.99  
%------------------------------------------------------------------------------
