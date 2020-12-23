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
% DateTime   : Thu Dec  3 12:17:13 EST 2020

% Result     : Theorem 2.82s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :  252 (12750 expanded)
%              Number of clauses        :  164 (3566 expanded)
%              Number of leaves         :   24 (3823 expanded)
%              Depth                    :   27
%              Number of atoms          :  777 (93826 expanded)
%              Number of equality atoms :  342 (31550 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
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
               => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
                 => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f21])).

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
    inference(flattening,[],[f48])).

fof(f56,plain,(
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

fof(f55,plain,(
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

fof(f54,plain,
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

fof(f57,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f56,f55,f54])).

fof(f90,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f81,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f84,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
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
    inference(ennf_transformation,[],[f16])).

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
    inference(flattening,[],[f41])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f91,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f87,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f57])).

fof(f89,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f57])).

fof(f88,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f57])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f37])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f39])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f85,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f82,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f58,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f92,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f57])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f64,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f51])).

fof(f94,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f59])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f67,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_23,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_32,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_380,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_381,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_34,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_385,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_386,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_385])).

cnf(c_1600,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_28,c_381,c_386])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_699,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_27])).

cnf(c_700,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_699])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_704,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_700,c_31])).

cnf(c_705,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_704])).

cnf(c_1563,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_2298,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_1563])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1573,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1607,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1573,c_381,c_386])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1572,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1597,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1572,c_381,c_386])).

cnf(c_2488,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2298,c_1607,c_1597])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_19,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_496,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_16,c_19])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_500,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_496,c_13])).

cnf(c_1568,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_500])).

cnf(c_2494,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2488,c_1568])).

cnf(c_39,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_49,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_651,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_27])).

cnf(c_652,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_651])).

cnf(c_656,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_652,c_31])).

cnf(c_657,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_656])).

cnf(c_1770,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_1771,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1770])).

cnf(c_1779,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_1780,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1779])).

cnf(c_1111,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1859,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_1111])).

cnf(c_1976,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1859])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_675,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_27])).

cnf(c_676,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(unflattening,[status(thm)],[c_675])).

cnf(c_680,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_funct_2(k2_funct_1(sK2),X0,X1)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_676,c_31])).

cnf(c_681,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(renaming,[status(thm)],[c_680])).

cnf(c_1564,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_681])).

cnf(c_2064,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_1564])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1792,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2095,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1792])).

cnf(c_2102,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2095])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_2310,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2311,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2310])).

cnf(c_3733,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2494,c_32,c_39,c_40,c_28,c_49,c_1607,c_1597,c_1771,c_1780,c_1976,c_2064,c_2102,c_2311])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1574,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_2408,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1607,c_1574])).

cnf(c_2648,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2408,c_1600])).

cnf(c_2307,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1607,c_1568])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_36,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_37,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_24,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_45,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_47,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_45])).

cnf(c_1885,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1792])).

cnf(c_1886,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1885])).

cnf(c_1941,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1942,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1941])).

cnf(c_3349,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2307,c_36,c_37,c_38,c_40,c_47,c_1597,c_1886,c_1942])).

cnf(c_3737,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3733,c_2648,c_3349])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1584,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3741,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3737,c_1584])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_627,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_27])).

cnf(c_628,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_627])).

cnf(c_632,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_628,c_31])).

cnf(c_633,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_632])).

cnf(c_1566,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_2153,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_1566])).

cnf(c_2229,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2153,c_1607,c_1597])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1674,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_26,c_381,c_386])).

cnf(c_2232,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_2229,c_1674])).

cnf(c_2655,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2648,c_2232])).

cnf(c_2493,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2488,c_1574])).

cnf(c_3195,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_2493,c_2648])).

cnf(c_3294,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_2655,c_3195])).

cnf(c_3352,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3349,c_3294])).

cnf(c_2654,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2648,c_2488])).

cnf(c_8,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_534,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_13,c_8])).

cnf(c_1569,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_534])).

cnf(c_3269,plain,
    ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2654,c_1569])).

cnf(c_4446,plain,
    ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3269,c_32,c_39,c_40,c_28,c_49,c_1780,c_1976,c_2102,c_2311])).

cnf(c_1581,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_3266,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2654,c_1581])).

cnf(c_4260,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3266,c_32,c_39,c_40,c_28,c_49,c_1780,c_1976,c_2102,c_2311])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1578,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4265,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
    inference(superposition,[status(thm)],[c_4260,c_1578])).

cnf(c_2658,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2648,c_1607])).

cnf(c_3167,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2658,c_1581])).

cnf(c_3641,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3167,c_40,c_1886,c_1942])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_723,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_27])).

cnf(c_724,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(unflattening,[status(thm)],[c_723])).

cnf(c_728,plain,
    ( ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_724,c_31])).

cnf(c_1562,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_3648,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_3641,c_1562])).

cnf(c_4270,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
    inference(light_normalisation,[status(thm)],[c_4265,c_3648])).

cnf(c_4449,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4446,c_4270])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1579,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3647,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3641,c_1579])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1582,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_606,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_27])).

cnf(c_607,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_606])).

cnf(c_611,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_607,c_31])).

cnf(c_1567,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_613,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_1955,plain,
    ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1567,c_40,c_613,c_1886,c_1942])).

cnf(c_1956,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_1955])).

cnf(c_1963,plain,
    ( k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1582,c_1956])).

cnf(c_4169,plain,
    ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3647,c_1963])).

cnf(c_4450,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4449,c_4169])).

cnf(c_4559,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3352,c_4450])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1575,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3267,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2654,c_1575])).

cnf(c_3574,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_3267,c_3349])).

cnf(c_4561,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4559,c_3574])).

cnf(c_4563,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3741,c_4561])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1576,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | k1_relat_1(X0) != k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_4705,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4563,c_1576])).

cnf(c_2014,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | k1_relat_1(sK2) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4770,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4705,c_29,c_1885,c_1941,c_2014,c_3741,c_4561])).

cnf(c_367,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_368,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_367])).

cnf(c_46,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_24])).

cnf(c_370,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_368,c_33,c_32,c_46])).

cnf(c_1570,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_370])).

cnf(c_2660,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2648,c_1570])).

cnf(c_4776,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4770,c_2660])).

cnf(c_3270,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2654,c_1568])).

cnf(c_2143,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2064,c_1607,c_1597])).

cnf(c_2657,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2648,c_2143])).

cnf(c_4565,plain,
    ( v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3270,c_32,c_39,c_40,c_28,c_49,c_1771,c_1780,c_1976,c_2102,c_2311,c_2657,c_4561])).

cnf(c_4569,plain,
    ( v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4565,c_3349])).

cnf(c_4642,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4563,c_4569])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4776,c_4642])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.32  % Computer   : n022.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 20:37:10 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.33  % Running in FOF mode
% 2.82/0.97  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.82/0.97  
% 2.82/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.82/0.97  
% 2.82/0.97  ------  iProver source info
% 2.82/0.97  
% 2.82/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.82/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.82/0.97  git: non_committed_changes: false
% 2.82/0.97  git: last_make_outside_of_git: false
% 2.82/0.97  
% 2.82/0.97  ------ 
% 2.82/0.97  
% 2.82/0.97  ------ Input Options
% 2.82/0.97  
% 2.82/0.97  --out_options                           all
% 2.82/0.97  --tptp_safe_out                         true
% 2.82/0.97  --problem_path                          ""
% 2.82/0.97  --include_path                          ""
% 2.82/0.97  --clausifier                            res/vclausify_rel
% 2.82/0.97  --clausifier_options                    --mode clausify
% 2.82/0.97  --stdin                                 false
% 2.82/0.97  --stats_out                             all
% 2.82/0.97  
% 2.82/0.97  ------ General Options
% 2.82/0.97  
% 2.82/0.97  --fof                                   false
% 2.82/0.97  --time_out_real                         305.
% 2.82/0.97  --time_out_virtual                      -1.
% 2.82/0.97  --symbol_type_check                     false
% 2.82/0.97  --clausify_out                          false
% 2.82/0.97  --sig_cnt_out                           false
% 2.82/0.97  --trig_cnt_out                          false
% 2.82/0.97  --trig_cnt_out_tolerance                1.
% 2.82/0.97  --trig_cnt_out_sk_spl                   false
% 2.82/0.97  --abstr_cl_out                          false
% 2.82/0.97  
% 2.82/0.97  ------ Global Options
% 2.82/0.97  
% 2.82/0.97  --schedule                              default
% 2.82/0.97  --add_important_lit                     false
% 2.82/0.97  --prop_solver_per_cl                    1000
% 2.82/0.97  --min_unsat_core                        false
% 2.82/0.97  --soft_assumptions                      false
% 2.82/0.97  --soft_lemma_size                       3
% 2.82/0.97  --prop_impl_unit_size                   0
% 2.82/0.97  --prop_impl_unit                        []
% 2.82/0.97  --share_sel_clauses                     true
% 2.82/0.97  --reset_solvers                         false
% 2.82/0.97  --bc_imp_inh                            [conj_cone]
% 2.82/0.97  --conj_cone_tolerance                   3.
% 2.82/0.97  --extra_neg_conj                        none
% 2.82/0.97  --large_theory_mode                     true
% 2.82/0.97  --prolific_symb_bound                   200
% 2.82/0.97  --lt_threshold                          2000
% 2.82/0.97  --clause_weak_htbl                      true
% 2.82/0.97  --gc_record_bc_elim                     false
% 2.82/0.97  
% 2.82/0.97  ------ Preprocessing Options
% 2.82/0.97  
% 2.82/0.97  --preprocessing_flag                    true
% 2.82/0.97  --time_out_prep_mult                    0.1
% 2.82/0.97  --splitting_mode                        input
% 2.82/0.97  --splitting_grd                         true
% 2.82/0.97  --splitting_cvd                         false
% 2.82/0.97  --splitting_cvd_svl                     false
% 2.82/0.97  --splitting_nvd                         32
% 2.82/0.97  --sub_typing                            true
% 2.82/0.97  --prep_gs_sim                           true
% 2.82/0.97  --prep_unflatten                        true
% 2.82/0.97  --prep_res_sim                          true
% 2.82/0.97  --prep_upred                            true
% 2.82/0.97  --prep_sem_filter                       exhaustive
% 2.82/0.97  --prep_sem_filter_out                   false
% 2.82/0.97  --pred_elim                             true
% 2.82/0.97  --res_sim_input                         true
% 2.82/0.97  --eq_ax_congr_red                       true
% 2.82/0.97  --pure_diseq_elim                       true
% 2.82/0.97  --brand_transform                       false
% 2.82/0.97  --non_eq_to_eq                          false
% 2.82/0.97  --prep_def_merge                        true
% 2.82/0.97  --prep_def_merge_prop_impl              false
% 2.82/0.97  --prep_def_merge_mbd                    true
% 2.82/0.97  --prep_def_merge_tr_red                 false
% 2.82/0.97  --prep_def_merge_tr_cl                  false
% 2.82/0.97  --smt_preprocessing                     true
% 2.82/0.97  --smt_ac_axioms                         fast
% 2.82/0.97  --preprocessed_out                      false
% 2.82/0.97  --preprocessed_stats                    false
% 2.82/0.97  
% 2.82/0.97  ------ Abstraction refinement Options
% 2.82/0.97  
% 2.82/0.97  --abstr_ref                             []
% 2.82/0.97  --abstr_ref_prep                        false
% 2.82/0.97  --abstr_ref_until_sat                   false
% 2.82/0.97  --abstr_ref_sig_restrict                funpre
% 2.82/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/0.97  --abstr_ref_under                       []
% 2.82/0.97  
% 2.82/0.97  ------ SAT Options
% 2.82/0.97  
% 2.82/0.97  --sat_mode                              false
% 2.82/0.97  --sat_fm_restart_options                ""
% 2.82/0.97  --sat_gr_def                            false
% 2.82/0.97  --sat_epr_types                         true
% 2.82/0.97  --sat_non_cyclic_types                  false
% 2.82/0.97  --sat_finite_models                     false
% 2.82/0.97  --sat_fm_lemmas                         false
% 2.82/0.97  --sat_fm_prep                           false
% 2.82/0.97  --sat_fm_uc_incr                        true
% 2.82/0.97  --sat_out_model                         small
% 2.82/0.97  --sat_out_clauses                       false
% 2.82/0.97  
% 2.82/0.97  ------ QBF Options
% 2.82/0.97  
% 2.82/0.97  --qbf_mode                              false
% 2.82/0.97  --qbf_elim_univ                         false
% 2.82/0.97  --qbf_dom_inst                          none
% 2.82/0.97  --qbf_dom_pre_inst                      false
% 2.82/0.97  --qbf_sk_in                             false
% 2.82/0.97  --qbf_pred_elim                         true
% 2.82/0.97  --qbf_split                             512
% 2.82/0.97  
% 2.82/0.97  ------ BMC1 Options
% 2.82/0.97  
% 2.82/0.97  --bmc1_incremental                      false
% 2.82/0.97  --bmc1_axioms                           reachable_all
% 2.82/0.97  --bmc1_min_bound                        0
% 2.82/0.97  --bmc1_max_bound                        -1
% 2.82/0.97  --bmc1_max_bound_default                -1
% 2.82/0.97  --bmc1_symbol_reachability              true
% 2.82/0.97  --bmc1_property_lemmas                  false
% 2.82/0.97  --bmc1_k_induction                      false
% 2.82/0.97  --bmc1_non_equiv_states                 false
% 2.82/0.97  --bmc1_deadlock                         false
% 2.82/0.97  --bmc1_ucm                              false
% 2.82/0.97  --bmc1_add_unsat_core                   none
% 2.82/0.97  --bmc1_unsat_core_children              false
% 2.82/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/0.97  --bmc1_out_stat                         full
% 2.82/0.97  --bmc1_ground_init                      false
% 2.82/0.97  --bmc1_pre_inst_next_state              false
% 2.82/0.97  --bmc1_pre_inst_state                   false
% 2.82/0.97  --bmc1_pre_inst_reach_state             false
% 2.82/0.97  --bmc1_out_unsat_core                   false
% 2.82/0.97  --bmc1_aig_witness_out                  false
% 2.82/0.97  --bmc1_verbose                          false
% 2.82/0.97  --bmc1_dump_clauses_tptp                false
% 2.82/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.82/0.97  --bmc1_dump_file                        -
% 2.82/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.82/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.82/0.97  --bmc1_ucm_extend_mode                  1
% 2.82/0.97  --bmc1_ucm_init_mode                    2
% 2.82/0.97  --bmc1_ucm_cone_mode                    none
% 2.82/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.82/0.97  --bmc1_ucm_relax_model                  4
% 2.82/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.82/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/0.97  --bmc1_ucm_layered_model                none
% 2.82/0.97  --bmc1_ucm_max_lemma_size               10
% 2.82/0.97  
% 2.82/0.97  ------ AIG Options
% 2.82/0.97  
% 2.82/0.97  --aig_mode                              false
% 2.82/0.97  
% 2.82/0.97  ------ Instantiation Options
% 2.82/0.97  
% 2.82/0.97  --instantiation_flag                    true
% 2.82/0.97  --inst_sos_flag                         false
% 2.82/0.97  --inst_sos_phase                        true
% 2.82/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/0.97  --inst_lit_sel_side                     num_symb
% 2.82/0.97  --inst_solver_per_active                1400
% 2.82/0.97  --inst_solver_calls_frac                1.
% 2.82/0.97  --inst_passive_queue_type               priority_queues
% 2.82/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/0.97  --inst_passive_queues_freq              [25;2]
% 2.82/0.97  --inst_dismatching                      true
% 2.82/0.97  --inst_eager_unprocessed_to_passive     true
% 2.82/0.97  --inst_prop_sim_given                   true
% 2.82/0.97  --inst_prop_sim_new                     false
% 2.82/0.97  --inst_subs_new                         false
% 2.82/0.97  --inst_eq_res_simp                      false
% 2.82/0.97  --inst_subs_given                       false
% 2.82/0.97  --inst_orphan_elimination               true
% 2.82/0.97  --inst_learning_loop_flag               true
% 2.82/0.97  --inst_learning_start                   3000
% 2.82/0.97  --inst_learning_factor                  2
% 2.82/0.97  --inst_start_prop_sim_after_learn       3
% 2.82/0.97  --inst_sel_renew                        solver
% 2.82/0.97  --inst_lit_activity_flag                true
% 2.82/0.97  --inst_restr_to_given                   false
% 2.82/0.97  --inst_activity_threshold               500
% 2.82/0.97  --inst_out_proof                        true
% 2.82/0.97  
% 2.82/0.97  ------ Resolution Options
% 2.82/0.97  
% 2.82/0.97  --resolution_flag                       true
% 2.82/0.97  --res_lit_sel                           adaptive
% 2.82/0.97  --res_lit_sel_side                      none
% 2.82/0.97  --res_ordering                          kbo
% 2.82/0.97  --res_to_prop_solver                    active
% 2.82/0.97  --res_prop_simpl_new                    false
% 2.82/0.97  --res_prop_simpl_given                  true
% 2.82/0.97  --res_passive_queue_type                priority_queues
% 2.82/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/0.97  --res_passive_queues_freq               [15;5]
% 2.82/0.97  --res_forward_subs                      full
% 2.82/0.97  --res_backward_subs                     full
% 2.82/0.97  --res_forward_subs_resolution           true
% 2.82/0.97  --res_backward_subs_resolution          true
% 2.82/0.97  --res_orphan_elimination                true
% 2.82/0.97  --res_time_limit                        2.
% 2.82/0.97  --res_out_proof                         true
% 2.82/0.97  
% 2.82/0.97  ------ Superposition Options
% 2.82/0.97  
% 2.82/0.97  --superposition_flag                    true
% 2.82/0.97  --sup_passive_queue_type                priority_queues
% 2.82/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.82/0.97  --demod_completeness_check              fast
% 2.82/0.97  --demod_use_ground                      true
% 2.82/0.97  --sup_to_prop_solver                    passive
% 2.82/0.97  --sup_prop_simpl_new                    true
% 2.82/0.97  --sup_prop_simpl_given                  true
% 2.82/0.97  --sup_fun_splitting                     false
% 2.82/0.97  --sup_smt_interval                      50000
% 2.82/0.97  
% 2.82/0.97  ------ Superposition Simplification Setup
% 2.82/0.97  
% 2.82/0.97  --sup_indices_passive                   []
% 2.82/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.97  --sup_full_bw                           [BwDemod]
% 2.82/0.97  --sup_immed_triv                        [TrivRules]
% 2.82/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.97  --sup_immed_bw_main                     []
% 2.82/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.97  
% 2.82/0.97  ------ Combination Options
% 2.82/0.97  
% 2.82/0.97  --comb_res_mult                         3
% 2.82/0.97  --comb_sup_mult                         2
% 2.82/0.97  --comb_inst_mult                        10
% 2.82/0.97  
% 2.82/0.97  ------ Debug Options
% 2.82/0.97  
% 2.82/0.97  --dbg_backtrace                         false
% 2.82/0.97  --dbg_dump_prop_clauses                 false
% 2.82/0.97  --dbg_dump_prop_clauses_file            -
% 2.82/0.97  --dbg_out_stat                          false
% 2.82/0.97  ------ Parsing...
% 2.82/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.82/0.97  
% 2.82/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.82/0.97  
% 2.82/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.82/0.97  
% 2.82/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.82/0.97  ------ Proving...
% 2.82/0.97  ------ Problem Properties 
% 2.82/0.97  
% 2.82/0.97  
% 2.82/0.97  clauses                                 27
% 2.82/0.97  conjectures                             5
% 2.82/0.97  EPR                                     4
% 2.82/0.97  Horn                                    26
% 2.82/0.97  unary                                   9
% 2.82/0.97  binary                                  7
% 2.82/0.97  lits                                    63
% 2.82/0.97  lits eq                                 24
% 2.82/0.97  fd_pure                                 0
% 2.82/0.97  fd_pseudo                               0
% 2.82/0.97  fd_cond                                 1
% 2.82/0.97  fd_pseudo_cond                          2
% 2.82/0.97  AC symbols                              0
% 2.82/0.97  
% 2.82/0.97  ------ Schedule dynamic 5 is on 
% 2.82/0.97  
% 2.82/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.82/0.97  
% 2.82/0.97  
% 2.82/0.97  ------ 
% 2.82/0.97  Current options:
% 2.82/0.97  ------ 
% 2.82/0.97  
% 2.82/0.97  ------ Input Options
% 2.82/0.97  
% 2.82/0.97  --out_options                           all
% 2.82/0.97  --tptp_safe_out                         true
% 2.82/0.97  --problem_path                          ""
% 2.82/0.97  --include_path                          ""
% 2.82/0.97  --clausifier                            res/vclausify_rel
% 2.82/0.97  --clausifier_options                    --mode clausify
% 2.82/0.97  --stdin                                 false
% 2.82/0.97  --stats_out                             all
% 2.82/0.97  
% 2.82/0.97  ------ General Options
% 2.82/0.97  
% 2.82/0.97  --fof                                   false
% 2.82/0.97  --time_out_real                         305.
% 2.82/0.97  --time_out_virtual                      -1.
% 2.82/0.97  --symbol_type_check                     false
% 2.82/0.97  --clausify_out                          false
% 2.82/0.97  --sig_cnt_out                           false
% 2.82/0.97  --trig_cnt_out                          false
% 2.82/0.97  --trig_cnt_out_tolerance                1.
% 2.82/0.97  --trig_cnt_out_sk_spl                   false
% 2.82/0.97  --abstr_cl_out                          false
% 2.82/0.97  
% 2.82/0.97  ------ Global Options
% 2.82/0.97  
% 2.82/0.97  --schedule                              default
% 2.82/0.97  --add_important_lit                     false
% 2.82/0.97  --prop_solver_per_cl                    1000
% 2.82/0.97  --min_unsat_core                        false
% 2.82/0.97  --soft_assumptions                      false
% 2.82/0.97  --soft_lemma_size                       3
% 2.82/0.97  --prop_impl_unit_size                   0
% 2.82/0.97  --prop_impl_unit                        []
% 2.82/0.97  --share_sel_clauses                     true
% 2.82/0.97  --reset_solvers                         false
% 2.82/0.97  --bc_imp_inh                            [conj_cone]
% 2.82/0.97  --conj_cone_tolerance                   3.
% 2.82/0.97  --extra_neg_conj                        none
% 2.82/0.97  --large_theory_mode                     true
% 2.82/0.97  --prolific_symb_bound                   200
% 2.82/0.97  --lt_threshold                          2000
% 2.82/0.97  --clause_weak_htbl                      true
% 2.82/0.97  --gc_record_bc_elim                     false
% 2.82/0.97  
% 2.82/0.97  ------ Preprocessing Options
% 2.82/0.97  
% 2.82/0.97  --preprocessing_flag                    true
% 2.82/0.97  --time_out_prep_mult                    0.1
% 2.82/0.97  --splitting_mode                        input
% 2.82/0.97  --splitting_grd                         true
% 2.82/0.97  --splitting_cvd                         false
% 2.82/0.97  --splitting_cvd_svl                     false
% 2.82/0.97  --splitting_nvd                         32
% 2.82/0.97  --sub_typing                            true
% 2.82/0.97  --prep_gs_sim                           true
% 2.82/0.97  --prep_unflatten                        true
% 2.82/0.97  --prep_res_sim                          true
% 2.82/0.97  --prep_upred                            true
% 2.82/0.97  --prep_sem_filter                       exhaustive
% 2.82/0.97  --prep_sem_filter_out                   false
% 2.82/0.97  --pred_elim                             true
% 2.82/0.97  --res_sim_input                         true
% 2.82/0.97  --eq_ax_congr_red                       true
% 2.82/0.97  --pure_diseq_elim                       true
% 2.82/0.97  --brand_transform                       false
% 2.82/0.97  --non_eq_to_eq                          false
% 2.82/0.97  --prep_def_merge                        true
% 2.82/0.97  --prep_def_merge_prop_impl              false
% 2.82/0.97  --prep_def_merge_mbd                    true
% 2.82/0.97  --prep_def_merge_tr_red                 false
% 2.82/0.97  --prep_def_merge_tr_cl                  false
% 2.82/0.97  --smt_preprocessing                     true
% 2.82/0.97  --smt_ac_axioms                         fast
% 2.82/0.97  --preprocessed_out                      false
% 2.82/0.97  --preprocessed_stats                    false
% 2.82/0.97  
% 2.82/0.97  ------ Abstraction refinement Options
% 2.82/0.97  
% 2.82/0.97  --abstr_ref                             []
% 2.82/0.97  --abstr_ref_prep                        false
% 2.82/0.97  --abstr_ref_until_sat                   false
% 2.82/0.97  --abstr_ref_sig_restrict                funpre
% 2.82/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.82/0.97  --abstr_ref_under                       []
% 2.82/0.97  
% 2.82/0.97  ------ SAT Options
% 2.82/0.97  
% 2.82/0.97  --sat_mode                              false
% 2.82/0.97  --sat_fm_restart_options                ""
% 2.82/0.97  --sat_gr_def                            false
% 2.82/0.97  --sat_epr_types                         true
% 2.82/0.97  --sat_non_cyclic_types                  false
% 2.82/0.97  --sat_finite_models                     false
% 2.82/0.97  --sat_fm_lemmas                         false
% 2.82/0.97  --sat_fm_prep                           false
% 2.82/0.97  --sat_fm_uc_incr                        true
% 2.82/0.97  --sat_out_model                         small
% 2.82/0.97  --sat_out_clauses                       false
% 2.82/0.97  
% 2.82/0.97  ------ QBF Options
% 2.82/0.97  
% 2.82/0.97  --qbf_mode                              false
% 2.82/0.97  --qbf_elim_univ                         false
% 2.82/0.97  --qbf_dom_inst                          none
% 2.82/0.97  --qbf_dom_pre_inst                      false
% 2.82/0.97  --qbf_sk_in                             false
% 2.82/0.97  --qbf_pred_elim                         true
% 2.82/0.97  --qbf_split                             512
% 2.82/0.97  
% 2.82/0.97  ------ BMC1 Options
% 2.82/0.97  
% 2.82/0.97  --bmc1_incremental                      false
% 2.82/0.97  --bmc1_axioms                           reachable_all
% 2.82/0.97  --bmc1_min_bound                        0
% 2.82/0.97  --bmc1_max_bound                        -1
% 2.82/0.97  --bmc1_max_bound_default                -1
% 2.82/0.97  --bmc1_symbol_reachability              true
% 2.82/0.97  --bmc1_property_lemmas                  false
% 2.82/0.97  --bmc1_k_induction                      false
% 2.82/0.97  --bmc1_non_equiv_states                 false
% 2.82/0.97  --bmc1_deadlock                         false
% 2.82/0.97  --bmc1_ucm                              false
% 2.82/0.97  --bmc1_add_unsat_core                   none
% 2.82/0.97  --bmc1_unsat_core_children              false
% 2.82/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.82/0.97  --bmc1_out_stat                         full
% 2.82/0.97  --bmc1_ground_init                      false
% 2.82/0.97  --bmc1_pre_inst_next_state              false
% 2.82/0.97  --bmc1_pre_inst_state                   false
% 2.82/0.97  --bmc1_pre_inst_reach_state             false
% 2.82/0.97  --bmc1_out_unsat_core                   false
% 2.82/0.97  --bmc1_aig_witness_out                  false
% 2.82/0.97  --bmc1_verbose                          false
% 2.82/0.97  --bmc1_dump_clauses_tptp                false
% 2.82/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.82/0.97  --bmc1_dump_file                        -
% 2.82/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.82/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.82/0.97  --bmc1_ucm_extend_mode                  1
% 2.82/0.97  --bmc1_ucm_init_mode                    2
% 2.82/0.97  --bmc1_ucm_cone_mode                    none
% 2.82/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.82/0.97  --bmc1_ucm_relax_model                  4
% 2.82/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.82/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.82/0.97  --bmc1_ucm_layered_model                none
% 2.82/0.97  --bmc1_ucm_max_lemma_size               10
% 2.82/0.97  
% 2.82/0.97  ------ AIG Options
% 2.82/0.97  
% 2.82/0.97  --aig_mode                              false
% 2.82/0.97  
% 2.82/0.97  ------ Instantiation Options
% 2.82/0.97  
% 2.82/0.97  --instantiation_flag                    true
% 2.82/0.97  --inst_sos_flag                         false
% 2.82/0.97  --inst_sos_phase                        true
% 2.82/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.82/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.82/0.97  --inst_lit_sel_side                     none
% 2.82/0.97  --inst_solver_per_active                1400
% 2.82/0.97  --inst_solver_calls_frac                1.
% 2.82/0.97  --inst_passive_queue_type               priority_queues
% 2.82/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.82/0.97  --inst_passive_queues_freq              [25;2]
% 2.82/0.97  --inst_dismatching                      true
% 2.82/0.97  --inst_eager_unprocessed_to_passive     true
% 2.82/0.97  --inst_prop_sim_given                   true
% 2.82/0.97  --inst_prop_sim_new                     false
% 2.82/0.97  --inst_subs_new                         false
% 2.82/0.97  --inst_eq_res_simp                      false
% 2.82/0.97  --inst_subs_given                       false
% 2.82/0.97  --inst_orphan_elimination               true
% 2.82/0.97  --inst_learning_loop_flag               true
% 2.82/0.97  --inst_learning_start                   3000
% 2.82/0.97  --inst_learning_factor                  2
% 2.82/0.97  --inst_start_prop_sim_after_learn       3
% 2.82/0.97  --inst_sel_renew                        solver
% 2.82/0.97  --inst_lit_activity_flag                true
% 2.82/0.97  --inst_restr_to_given                   false
% 2.82/0.97  --inst_activity_threshold               500
% 2.82/0.97  --inst_out_proof                        true
% 2.82/0.97  
% 2.82/0.97  ------ Resolution Options
% 2.82/0.97  
% 2.82/0.97  --resolution_flag                       false
% 2.82/0.97  --res_lit_sel                           adaptive
% 2.82/0.97  --res_lit_sel_side                      none
% 2.82/0.97  --res_ordering                          kbo
% 2.82/0.97  --res_to_prop_solver                    active
% 2.82/0.97  --res_prop_simpl_new                    false
% 2.82/0.97  --res_prop_simpl_given                  true
% 2.82/0.97  --res_passive_queue_type                priority_queues
% 2.82/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.82/0.97  --res_passive_queues_freq               [15;5]
% 2.82/0.97  --res_forward_subs                      full
% 2.82/0.97  --res_backward_subs                     full
% 2.82/0.97  --res_forward_subs_resolution           true
% 2.82/0.97  --res_backward_subs_resolution          true
% 2.82/0.97  --res_orphan_elimination                true
% 2.82/0.97  --res_time_limit                        2.
% 2.82/0.97  --res_out_proof                         true
% 2.82/0.97  
% 2.82/0.97  ------ Superposition Options
% 2.82/0.97  
% 2.82/0.97  --superposition_flag                    true
% 2.82/0.97  --sup_passive_queue_type                priority_queues
% 2.82/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.82/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.82/0.97  --demod_completeness_check              fast
% 2.82/0.97  --demod_use_ground                      true
% 2.82/0.97  --sup_to_prop_solver                    passive
% 2.82/0.97  --sup_prop_simpl_new                    true
% 2.82/0.97  --sup_prop_simpl_given                  true
% 2.82/0.97  --sup_fun_splitting                     false
% 2.82/0.97  --sup_smt_interval                      50000
% 2.82/0.97  
% 2.82/0.97  ------ Superposition Simplification Setup
% 2.82/0.97  
% 2.82/0.97  --sup_indices_passive                   []
% 2.82/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.82/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.82/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.97  --sup_full_bw                           [BwDemod]
% 2.82/0.97  --sup_immed_triv                        [TrivRules]
% 2.82/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.82/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.97  --sup_immed_bw_main                     []
% 2.82/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.82/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.82/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.82/0.97  
% 2.82/0.97  ------ Combination Options
% 2.82/0.97  
% 2.82/0.97  --comb_res_mult                         3
% 2.82/0.97  --comb_sup_mult                         2
% 2.82/0.97  --comb_inst_mult                        10
% 2.82/0.97  
% 2.82/0.97  ------ Debug Options
% 2.82/0.97  
% 2.82/0.97  --dbg_backtrace                         false
% 2.82/0.97  --dbg_dump_prop_clauses                 false
% 2.82/0.97  --dbg_dump_prop_clauses_file            -
% 2.82/0.97  --dbg_out_stat                          false
% 2.82/0.97  
% 2.82/0.97  
% 2.82/0.97  
% 2.82/0.97  
% 2.82/0.97  ------ Proving...
% 2.82/0.97  
% 2.82/0.97  
% 2.82/0.97  % SZS status Theorem for theBenchmark.p
% 2.82/0.97  
% 2.82/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 2.82/0.97  
% 2.82/0.97  fof(f20,conjecture,(
% 2.82/0.97    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.82/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.97  
% 2.82/0.97  fof(f21,negated_conjecture,(
% 2.82/0.97    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.82/0.97    inference(negated_conjecture,[],[f20])).
% 2.82/0.97  
% 2.82/0.97  fof(f48,plain,(
% 2.82/0.97    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.82/0.97    inference(ennf_transformation,[],[f21])).
% 2.82/0.97  
% 2.82/0.97  fof(f49,plain,(
% 2.82/0.97    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.82/0.97    inference(flattening,[],[f48])).
% 2.82/0.97  
% 2.82/0.97  fof(f56,plain,(
% 2.82/0.97    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.82/0.97    introduced(choice_axiom,[])).
% 2.82/0.97  
% 2.82/0.97  fof(f55,plain,(
% 2.82/0.97    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.82/0.97    introduced(choice_axiom,[])).
% 2.82/0.97  
% 2.82/0.97  fof(f54,plain,(
% 2.82/0.97    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.82/0.97    introduced(choice_axiom,[])).
% 2.82/0.97  
% 2.82/0.97  fof(f57,plain,(
% 2.82/0.97    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.82/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f56,f55,f54])).
% 2.82/0.97  
% 2.82/0.97  fof(f90,plain,(
% 2.82/0.97    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.82/0.97    inference(cnf_transformation,[],[f57])).
% 2.82/0.97  
% 2.82/0.97  fof(f17,axiom,(
% 2.82/0.97    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.82/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.97  
% 2.82/0.97  fof(f43,plain,(
% 2.82/0.97    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.82/0.97    inference(ennf_transformation,[],[f17])).
% 2.82/0.97  
% 2.82/0.97  fof(f81,plain,(
% 2.82/0.97    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.82/0.97    inference(cnf_transformation,[],[f43])).
% 2.82/0.97  
% 2.82/0.97  fof(f86,plain,(
% 2.82/0.97    l1_struct_0(sK1)),
% 2.82/0.97    inference(cnf_transformation,[],[f57])).
% 2.82/0.97  
% 2.82/0.97  fof(f84,plain,(
% 2.82/0.97    l1_struct_0(sK0)),
% 2.82/0.97    inference(cnf_transformation,[],[f57])).
% 2.82/0.97  
% 2.82/0.97  fof(f16,axiom,(
% 2.82/0.97    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.82/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.97  
% 2.82/0.97  fof(f41,plain,(
% 2.82/0.97    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.82/0.97    inference(ennf_transformation,[],[f16])).
% 2.82/0.97  
% 2.82/0.97  fof(f42,plain,(
% 2.82/0.97    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.82/0.97    inference(flattening,[],[f41])).
% 2.82/0.97  
% 2.82/0.97  fof(f80,plain,(
% 2.82/0.97    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.82/0.97    inference(cnf_transformation,[],[f42])).
% 2.82/0.97  
% 2.82/0.97  fof(f91,plain,(
% 2.82/0.97    v2_funct_1(sK2)),
% 2.82/0.97    inference(cnf_transformation,[],[f57])).
% 2.82/0.97  
% 2.82/0.97  fof(f87,plain,(
% 2.82/0.97    v1_funct_1(sK2)),
% 2.82/0.97    inference(cnf_transformation,[],[f57])).
% 2.82/0.97  
% 2.82/0.97  fof(f89,plain,(
% 2.82/0.97    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.82/0.97    inference(cnf_transformation,[],[f57])).
% 2.82/0.97  
% 2.82/0.97  fof(f88,plain,(
% 2.82/0.97    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.82/0.97    inference(cnf_transformation,[],[f57])).
% 2.82/0.97  
% 2.82/0.97  fof(f14,axiom,(
% 2.82/0.97    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.82/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.97  
% 2.82/0.97  fof(f37,plain,(
% 2.82/0.97    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.82/0.97    inference(ennf_transformation,[],[f14])).
% 2.82/0.97  
% 2.82/0.97  fof(f38,plain,(
% 2.82/0.97    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.82/0.97    inference(flattening,[],[f37])).
% 2.82/0.97  
% 2.82/0.97  fof(f75,plain,(
% 2.82/0.97    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.82/0.97    inference(cnf_transformation,[],[f38])).
% 2.82/0.97  
% 2.82/0.97  fof(f15,axiom,(
% 2.82/0.97    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.82/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.97  
% 2.82/0.97  fof(f39,plain,(
% 2.82/0.97    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.82/0.97    inference(ennf_transformation,[],[f15])).
% 2.82/0.97  
% 2.82/0.97  fof(f40,plain,(
% 2.82/0.97    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.82/0.97    inference(flattening,[],[f39])).
% 2.82/0.97  
% 2.82/0.97  fof(f53,plain,(
% 2.82/0.97    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.82/0.97    inference(nnf_transformation,[],[f40])).
% 2.82/0.97  
% 2.82/0.97  fof(f76,plain,(
% 2.82/0.97    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.82/0.97    inference(cnf_transformation,[],[f53])).
% 2.82/0.97  
% 2.82/0.97  fof(f11,axiom,(
% 2.82/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.82/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.97  
% 2.82/0.97  fof(f22,plain,(
% 2.82/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.82/0.97    inference(pure_predicate_removal,[],[f11])).
% 2.82/0.97  
% 2.82/0.97  fof(f34,plain,(
% 2.82/0.97    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/0.97    inference(ennf_transformation,[],[f22])).
% 2.82/0.97  
% 2.82/0.97  fof(f71,plain,(
% 2.82/0.97    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/0.97    inference(cnf_transformation,[],[f34])).
% 2.82/0.98  
% 2.82/0.98  fof(f78,plain,(
% 2.82/0.98    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.82/0.98    inference(cnf_transformation,[],[f42])).
% 2.82/0.98  
% 2.82/0.98  fof(f79,plain,(
% 2.82/0.98    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.82/0.98    inference(cnf_transformation,[],[f42])).
% 2.82/0.98  
% 2.82/0.98  fof(f3,axiom,(
% 2.82/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f24,plain,(
% 2.82/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.82/0.98    inference(ennf_transformation,[],[f3])).
% 2.82/0.98  
% 2.82/0.98  fof(f62,plain,(
% 2.82/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.82/0.98    inference(cnf_transformation,[],[f24])).
% 2.82/0.98  
% 2.82/0.98  fof(f4,axiom,(
% 2.82/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f63,plain,(
% 2.82/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.82/0.98    inference(cnf_transformation,[],[f4])).
% 2.82/0.98  
% 2.82/0.98  fof(f13,axiom,(
% 2.82/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f36,plain,(
% 2.82/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/0.98    inference(ennf_transformation,[],[f13])).
% 2.82/0.98  
% 2.82/0.98  fof(f73,plain,(
% 2.82/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/0.98    inference(cnf_transformation,[],[f36])).
% 2.82/0.98  
% 2.82/0.98  fof(f85,plain,(
% 2.82/0.98    ~v2_struct_0(sK1)),
% 2.82/0.98    inference(cnf_transformation,[],[f57])).
% 2.82/0.98  
% 2.82/0.98  fof(f18,axiom,(
% 2.82/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f44,plain,(
% 2.82/0.98    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.82/0.98    inference(ennf_transformation,[],[f18])).
% 2.82/0.98  
% 2.82/0.98  fof(f45,plain,(
% 2.82/0.98    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.82/0.98    inference(flattening,[],[f44])).
% 2.82/0.98  
% 2.82/0.98  fof(f82,plain,(
% 2.82/0.98    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.82/0.98    inference(cnf_transformation,[],[f45])).
% 2.82/0.98  
% 2.82/0.98  fof(f1,axiom,(
% 2.82/0.98    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f23,plain,(
% 2.82/0.98    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.82/0.98    inference(ennf_transformation,[],[f1])).
% 2.82/0.98  
% 2.82/0.98  fof(f58,plain,(
% 2.82/0.98    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.82/0.98    inference(cnf_transformation,[],[f23])).
% 2.82/0.98  
% 2.82/0.98  fof(f19,axiom,(
% 2.82/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f46,plain,(
% 2.82/0.98    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.82/0.98    inference(ennf_transformation,[],[f19])).
% 2.82/0.98  
% 2.82/0.98  fof(f47,plain,(
% 2.82/0.98    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.82/0.98    inference(flattening,[],[f46])).
% 2.82/0.98  
% 2.82/0.98  fof(f83,plain,(
% 2.82/0.98    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.82/0.98    inference(cnf_transformation,[],[f47])).
% 2.82/0.98  
% 2.82/0.98  fof(f92,plain,(
% 2.82/0.98    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.82/0.98    inference(cnf_transformation,[],[f57])).
% 2.82/0.98  
% 2.82/0.98  fof(f7,axiom,(
% 2.82/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f27,plain,(
% 2.82/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.82/0.98    inference(ennf_transformation,[],[f7])).
% 2.82/0.98  
% 2.82/0.98  fof(f28,plain,(
% 2.82/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.82/0.98    inference(flattening,[],[f27])).
% 2.82/0.98  
% 2.82/0.98  fof(f66,plain,(
% 2.82/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.82/0.98    inference(cnf_transformation,[],[f28])).
% 2.82/0.98  
% 2.82/0.98  fof(f6,axiom,(
% 2.82/0.98    ! [X0,X1] : (v1_relat_1(X1) => k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)))),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f26,plain,(
% 2.82/0.98    ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.82/0.98    inference(ennf_transformation,[],[f6])).
% 2.82/0.98  
% 2.82/0.98  fof(f65,plain,(
% 2.82/0.98    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k2_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.82/0.98    inference(cnf_transformation,[],[f26])).
% 2.82/0.98  
% 2.82/0.98  fof(f9,axiom,(
% 2.82/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f30,plain,(
% 2.82/0.98    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.82/0.98    inference(ennf_transformation,[],[f9])).
% 2.82/0.98  
% 2.82/0.98  fof(f31,plain,(
% 2.82/0.98    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.82/0.98    inference(flattening,[],[f30])).
% 2.82/0.98  
% 2.82/0.98  fof(f69,plain,(
% 2.82/0.98    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.82/0.98    inference(cnf_transformation,[],[f31])).
% 2.82/0.98  
% 2.82/0.98  fof(f5,axiom,(
% 2.82/0.98    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f25,plain,(
% 2.82/0.98    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 2.82/0.98    inference(ennf_transformation,[],[f5])).
% 2.82/0.98  
% 2.82/0.98  fof(f64,plain,(
% 2.82/0.98    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.82/0.98    inference(cnf_transformation,[],[f25])).
% 2.82/0.98  
% 2.82/0.98  fof(f2,axiom,(
% 2.82/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f50,plain,(
% 2.82/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.82/0.98    inference(nnf_transformation,[],[f2])).
% 2.82/0.98  
% 2.82/0.98  fof(f51,plain,(
% 2.82/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.82/0.98    inference(flattening,[],[f50])).
% 2.82/0.98  
% 2.82/0.98  fof(f59,plain,(
% 2.82/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 2.82/0.98    inference(cnf_transformation,[],[f51])).
% 2.82/0.98  
% 2.82/0.98  fof(f94,plain,(
% 2.82/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 2.82/0.98    inference(equality_resolution,[],[f59])).
% 2.82/0.98  
% 2.82/0.98  fof(f10,axiom,(
% 2.82/0.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & r1_tarski(X0,k1_relat_1(X1))) => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0))),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f32,plain,(
% 2.82/0.98    ! [X0,X1] : ((k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | (~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 2.82/0.98    inference(ennf_transformation,[],[f10])).
% 2.82/0.98  
% 2.82/0.98  fof(f33,plain,(
% 2.82/0.98    ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 2.82/0.98    inference(flattening,[],[f32])).
% 2.82/0.98  
% 2.82/0.98  fof(f70,plain,(
% 2.82/0.98    ( ! [X0,X1] : (k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 | ~v2_funct_1(X1) | ~r1_tarski(X0,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 2.82/0.98    inference(cnf_transformation,[],[f33])).
% 2.82/0.98  
% 2.82/0.98  fof(f12,axiom,(
% 2.82/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f35,plain,(
% 2.82/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.82/0.98    inference(ennf_transformation,[],[f12])).
% 2.82/0.98  
% 2.82/0.98  fof(f72,plain,(
% 2.82/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.82/0.98    inference(cnf_transformation,[],[f35])).
% 2.82/0.98  
% 2.82/0.98  fof(f8,axiom,(
% 2.82/0.98    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.82/0.98    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.82/0.98  
% 2.82/0.98  fof(f29,plain,(
% 2.82/0.98    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.82/0.98    inference(ennf_transformation,[],[f8])).
% 2.82/0.98  
% 2.82/0.98  fof(f52,plain,(
% 2.82/0.98    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.82/0.98    inference(nnf_transformation,[],[f29])).
% 2.82/0.98  
% 2.82/0.98  fof(f67,plain,(
% 2.82/0.98    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.82/0.98    inference(cnf_transformation,[],[f52])).
% 2.82/0.98  
% 2.82/0.98  cnf(c_28,negated_conjecture,
% 2.82/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.82/0.98      inference(cnf_transformation,[],[f90]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_23,plain,
% 2.82/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.82/0.98      inference(cnf_transformation,[],[f81]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_32,negated_conjecture,
% 2.82/0.98      ( l1_struct_0(sK1) ),
% 2.82/0.98      inference(cnf_transformation,[],[f86]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_380,plain,
% 2.82/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.82/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_381,plain,
% 2.82/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.82/0.98      inference(unflattening,[status(thm)],[c_380]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_34,negated_conjecture,
% 2.82/0.98      ( l1_struct_0(sK0) ),
% 2.82/0.98      inference(cnf_transformation,[],[f84]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_385,plain,
% 2.82/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.82/0.98      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_386,plain,
% 2.82/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.82/0.98      inference(unflattening,[status(thm)],[c_385]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1600,plain,
% 2.82/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.82/0.98      inference(light_normalisation,[status(thm)],[c_28,c_381,c_386]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_20,plain,
% 2.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.82/0.98      | ~ v1_funct_1(X0)
% 2.82/0.98      | ~ v2_funct_1(X0)
% 2.82/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.82/0.98      inference(cnf_transformation,[],[f80]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_27,negated_conjecture,
% 2.82/0.98      ( v2_funct_1(sK2) ),
% 2.82/0.98      inference(cnf_transformation,[],[f91]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_699,plain,
% 2.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.82/0.98      | ~ v1_funct_1(X0)
% 2.82/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.82/0.98      | sK2 != X0 ),
% 2.82/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_27]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_700,plain,
% 2.82/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.82/0.98      | ~ v1_funct_1(sK2)
% 2.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.82/0.98      inference(unflattening,[status(thm)],[c_699]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_31,negated_conjecture,
% 2.82/0.98      ( v1_funct_1(sK2) ),
% 2.82/0.98      inference(cnf_transformation,[],[f87]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_704,plain,
% 2.82/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.82/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 2.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_700,c_31]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_705,plain,
% 2.82/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.82/0.98      inference(renaming,[status(thm)],[c_704]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1563,plain,
% 2.82/0.98      ( k2_relset_1(X0,X1,sK2) != X1
% 2.82/0.98      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2298,plain,
% 2.82/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_1600,c_1563]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_29,negated_conjecture,
% 2.82/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.82/0.98      inference(cnf_transformation,[],[f89]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1573,plain,
% 2.82/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1607,plain,
% 2.82/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.82/0.98      inference(light_normalisation,[status(thm)],[c_1573,c_381,c_386]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_30,negated_conjecture,
% 2.82/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.82/0.98      inference(cnf_transformation,[],[f88]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1572,plain,
% 2.82/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1597,plain,
% 2.82/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.82/0.98      inference(light_normalisation,[status(thm)],[c_1572,c_381,c_386]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2488,plain,
% 2.82/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_2298,c_1607,c_1597]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_16,plain,
% 2.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/0.98      | v1_partfun1(X0,X1)
% 2.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | ~ v1_funct_1(X0)
% 2.82/0.98      | v1_xboole_0(X2) ),
% 2.82/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_19,plain,
% 2.82/0.98      ( ~ v1_partfun1(X0,X1)
% 2.82/0.98      | ~ v4_relat_1(X0,X1)
% 2.82/0.98      | ~ v1_relat_1(X0)
% 2.82/0.98      | k1_relat_1(X0) = X1 ),
% 2.82/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_496,plain,
% 2.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/0.98      | ~ v4_relat_1(X0,X1)
% 2.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | ~ v1_funct_1(X0)
% 2.82/0.98      | ~ v1_relat_1(X0)
% 2.82/0.98      | v1_xboole_0(X2)
% 2.82/0.98      | k1_relat_1(X0) = X1 ),
% 2.82/0.98      inference(resolution,[status(thm)],[c_16,c_19]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_13,plain,
% 2.82/0.98      ( v4_relat_1(X0,X1)
% 2.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.82/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_500,plain,
% 2.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | ~ v1_funct_1(X0)
% 2.82/0.98      | ~ v1_relat_1(X0)
% 2.82/0.98      | v1_xboole_0(X2)
% 2.82/0.98      | k1_relat_1(X0) = X1 ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_496,c_13]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1568,plain,
% 2.82/0.98      ( k1_relat_1(X0) = X1
% 2.82/0.98      | v1_funct_2(X0,X1,X2) != iProver_top
% 2.82/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.82/0.98      | v1_funct_1(X0) != iProver_top
% 2.82/0.98      | v1_relat_1(X0) != iProver_top
% 2.82/0.98      | v1_xboole_0(X2) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_500]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2494,plain,
% 2.82/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
% 2.82/0.98      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.82/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.82/0.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.82/0.98      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_2488,c_1568]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_39,plain,
% 2.82/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_40,plain,
% 2.82/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_49,plain,
% 2.82/0.98      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_23]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_22,plain,
% 2.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | ~ v1_funct_1(X0)
% 2.82/0.98      | v1_funct_1(k2_funct_1(X0))
% 2.82/0.98      | ~ v2_funct_1(X0)
% 2.82/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.82/0.98      inference(cnf_transformation,[],[f78]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_651,plain,
% 2.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | ~ v1_funct_1(X0)
% 2.82/0.98      | v1_funct_1(k2_funct_1(X0))
% 2.82/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.82/0.98      | sK2 != X0 ),
% 2.82/0.98      inference(resolution_lifted,[status(thm)],[c_22,c_27]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_652,plain,
% 2.82/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.82/0.98      | v1_funct_1(k2_funct_1(sK2))
% 2.82/0.98      | ~ v1_funct_1(sK2)
% 2.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.82/0.98      inference(unflattening,[status(thm)],[c_651]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_656,plain,
% 2.82/0.98      ( v1_funct_1(k2_funct_1(sK2))
% 2.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.82/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 2.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_652,c_31]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_657,plain,
% 2.82/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.82/0.98      | v1_funct_1(k2_funct_1(sK2))
% 2.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.82/0.98      inference(renaming,[status(thm)],[c_656]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1770,plain,
% 2.82/0.98      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.82/0.98      | v1_funct_1(k2_funct_1(sK2))
% 2.82/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_657]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1771,plain,
% 2.82/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.82/0.98      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.82/0.98      | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_1770]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1779,plain,
% 2.82/0.98      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.82/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_705]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1780,plain,
% 2.82/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.82/0.98      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.82/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 2.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_1779]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1111,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1859,plain,
% 2.82/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 2.82/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.82/0.98      | u1_struct_0(sK1) != X0 ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_1111]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1976,plain,
% 2.82/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.82/0.98      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.82/0.98      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_1859]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_21,plain,
% 2.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/0.98      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | ~ v1_funct_1(X0)
% 2.82/0.98      | ~ v2_funct_1(X0)
% 2.82/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.82/0.98      inference(cnf_transformation,[],[f79]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_675,plain,
% 2.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/0.98      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | ~ v1_funct_1(X0)
% 2.82/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.82/0.98      | sK2 != X0 ),
% 2.82/0.98      inference(resolution_lifted,[status(thm)],[c_21,c_27]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_676,plain,
% 2.82/0.98      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.82/0.98      | ~ v1_funct_2(sK2,X1,X0)
% 2.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.82/0.98      | ~ v1_funct_1(sK2)
% 2.82/0.98      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.82/0.98      inference(unflattening,[status(thm)],[c_675]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_680,plain,
% 2.82/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.82/0.98      | ~ v1_funct_2(sK2,X1,X0)
% 2.82/0.98      | v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.82/0.98      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_676,c_31]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_681,plain,
% 2.82/0.98      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.82/0.98      | ~ v1_funct_2(sK2,X1,X0)
% 2.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.82/0.98      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.82/0.98      inference(renaming,[status(thm)],[c_680]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1564,plain,
% 2.82/0.98      ( k2_relset_1(X0,X1,sK2) != X1
% 2.82/0.98      | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
% 2.82/0.98      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_681]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2064,plain,
% 2.82/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.82/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_1600,c_1564]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4,plain,
% 2.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.82/0.98      | ~ v1_relat_1(X1)
% 2.82/0.98      | v1_relat_1(X0) ),
% 2.82/0.98      inference(cnf_transformation,[],[f62]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1792,plain,
% 2.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | v1_relat_1(X0)
% 2.82/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_4]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2095,plain,
% 2.82/0.98      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 2.82/0.98      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 2.82/0.98      | v1_relat_1(k2_funct_1(sK2)) ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_1792]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2102,plain,
% 2.82/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 2.82/0.98      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 2.82/0.98      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_2095]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_5,plain,
% 2.82/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.82/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2310,plain,
% 2.82/0.98      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2311,plain,
% 2.82/0.98      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_2310]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3733,plain,
% 2.82/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_struct_0(sK1)
% 2.82/0.98      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_2494,c_32,c_39,c_40,c_28,c_49,c_1607,c_1597,c_1771,
% 2.82/0.98                 c_1780,c_1976,c_2064,c_2102,c_2311]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_15,plain,
% 2.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.82/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1574,plain,
% 2.82/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.82/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2408,plain,
% 2.82/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_1607,c_1574]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2648,plain,
% 2.82/0.98      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.82/0.98      inference(demodulation,[status(thm)],[c_2408,c_1600]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2307,plain,
% 2.82/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.82/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.82/0.98      | v1_funct_1(sK2) != iProver_top
% 2.82/0.98      | v1_relat_1(sK2) != iProver_top
% 2.82/0.98      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_1607,c_1568]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_33,negated_conjecture,
% 2.82/0.98      ( ~ v2_struct_0(sK1) ),
% 2.82/0.98      inference(cnf_transformation,[],[f85]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_36,plain,
% 2.82/0.98      ( v2_struct_0(sK1) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_37,plain,
% 2.82/0.98      ( l1_struct_0(sK1) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_38,plain,
% 2.82/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_24,plain,
% 2.82/0.98      ( v2_struct_0(X0)
% 2.82/0.98      | ~ l1_struct_0(X0)
% 2.82/0.98      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.82/0.98      inference(cnf_transformation,[],[f82]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_45,plain,
% 2.82/0.98      ( v2_struct_0(X0) = iProver_top
% 2.82/0.98      | l1_struct_0(X0) != iProver_top
% 2.82/0.98      | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_47,plain,
% 2.82/0.98      ( v2_struct_0(sK1) = iProver_top
% 2.82/0.98      | l1_struct_0(sK1) != iProver_top
% 2.82/0.98      | v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_45]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1885,plain,
% 2.82/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.82/0.98      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.82/0.98      | v1_relat_1(sK2) ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_1792]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1886,plain,
% 2.82/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.82/0.98      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.82/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_1885]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1941,plain,
% 2.82/0.98      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_5]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1942,plain,
% 2.82/0.98      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_1941]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3349,plain,
% 2.82/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_2307,c_36,c_37,c_38,c_40,c_47,c_1597,c_1886,c_1942]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3737,plain,
% 2.82/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.82/0.98      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 2.82/0.98      inference(light_normalisation,[status(thm)],[c_3733,c_2648,c_3349]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_0,plain,
% 2.82/0.98      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.82/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1584,plain,
% 2.82/0.98      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3741,plain,
% 2.82/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.82/0.98      | k1_relat_1(sK2) = k1_xboole_0 ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_3737,c_1584]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_25,plain,
% 2.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | ~ v1_funct_1(X0)
% 2.82/0.98      | ~ v2_funct_1(X0)
% 2.82/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.82/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.82/0.98      inference(cnf_transformation,[],[f83]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_627,plain,
% 2.82/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.82/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | ~ v1_funct_1(X0)
% 2.82/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.82/0.98      | k2_relset_1(X1,X2,X0) != X2
% 2.82/0.98      | sK2 != X0 ),
% 2.82/0.98      inference(resolution_lifted,[status(thm)],[c_25,c_27]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_628,plain,
% 2.82/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.82/0.98      | ~ v1_funct_1(sK2)
% 2.82/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.82/0.98      inference(unflattening,[status(thm)],[c_627]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_632,plain,
% 2.82/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.82/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 2.82/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_628,c_31]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_633,plain,
% 2.82/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 2.82/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.82/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.82/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.82/0.98      inference(renaming,[status(thm)],[c_632]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1566,plain,
% 2.82/0.98      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.82/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 2.82/0.98      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2153,plain,
% 2.82/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.82/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.82/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_1600,c_1566]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2229,plain,
% 2.82/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_2153,c_1607,c_1597]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_26,negated_conjecture,
% 2.82/0.98      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.82/0.98      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.82/0.98      inference(cnf_transformation,[],[f92]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1674,plain,
% 2.82/0.98      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.82/0.98      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.82/0.98      inference(light_normalisation,[status(thm)],[c_26,c_381,c_386]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2232,plain,
% 2.82/0.98      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.82/0.98      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.82/0.98      inference(demodulation,[status(thm)],[c_2229,c_1674]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2655,plain,
% 2.82/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.82/0.98      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.82/0.98      inference(demodulation,[status(thm)],[c_2648,c_2232]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2493,plain,
% 2.82/0.98      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_2488,c_1574]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3195,plain,
% 2.82/0.98      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.82/0.98      inference(light_normalisation,[status(thm)],[c_2493,c_2648]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3294,plain,
% 2.82/0.98      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.82/0.98      | k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.82/0.98      inference(light_normalisation,[status(thm)],[c_2655,c_3195]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3352,plain,
% 2.82/0.98      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.82/0.98      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 2.82/0.98      inference(demodulation,[status(thm)],[c_3349,c_3294]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2654,plain,
% 2.82/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.82/0.98      inference(demodulation,[status(thm)],[c_2648,c_2488]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_8,plain,
% 2.82/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 2.82/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_534,plain,
% 2.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | ~ v1_relat_1(X0)
% 2.82/0.98      | k7_relat_1(X0,X1) = X0 ),
% 2.82/0.98      inference(resolution,[status(thm)],[c_13,c_8]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1569,plain,
% 2.82/0.98      ( k7_relat_1(X0,X1) = X0
% 2.82/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.82/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_534]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3269,plain,
% 2.82/0.98      ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2)
% 2.82/0.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_2654,c_1569]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4446,plain,
% 2.82/0.98      ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2) ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_3269,c_32,c_39,c_40,c_28,c_49,c_1780,c_1976,c_2102,
% 2.82/0.98                 c_2311]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1581,plain,
% 2.82/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.82/0.98      | v1_relat_1(X1) != iProver_top
% 2.82/0.98      | v1_relat_1(X0) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3266,plain,
% 2.82/0.98      ( v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))) != iProver_top
% 2.82/0.98      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_2654,c_1581]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4260,plain,
% 2.82/0.98      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_3266,c_32,c_39,c_40,c_28,c_49,c_1780,c_1976,c_2102,
% 2.82/0.98                 c_2311]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_7,plain,
% 2.82/0.98      ( ~ v1_relat_1(X0)
% 2.82/0.98      | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 2.82/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1578,plain,
% 2.82/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 2.82/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4265,plain,
% 2.82/0.98      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_4260,c_1578]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2658,plain,
% 2.82/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.82/0.98      inference(demodulation,[status(thm)],[c_2648,c_1607]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3167,plain,
% 2.82/0.98      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
% 2.82/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_2658,c_1581]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3641,plain,
% 2.82/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_3167,c_40,c_1886,c_1942]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_11,plain,
% 2.82/0.98      ( ~ v1_funct_1(X0)
% 2.82/0.98      | ~ v2_funct_1(X0)
% 2.82/0.98      | ~ v1_relat_1(X0)
% 2.82/0.98      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 2.82/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_723,plain,
% 2.82/0.98      ( ~ v1_funct_1(X0)
% 2.82/0.98      | ~ v1_relat_1(X0)
% 2.82/0.98      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 2.82/0.98      | sK2 != X0 ),
% 2.82/0.98      inference(resolution_lifted,[status(thm)],[c_11,c_27]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_724,plain,
% 2.82/0.98      ( ~ v1_funct_1(sK2)
% 2.82/0.98      | ~ v1_relat_1(sK2)
% 2.82/0.98      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.82/0.98      inference(unflattening,[status(thm)],[c_723]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_728,plain,
% 2.82/0.98      ( ~ v1_relat_1(sK2)
% 2.82/0.98      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_724,c_31]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1562,plain,
% 2.82/0.98      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
% 2.82/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3648,plain,
% 2.82/0.98      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_3641,c_1562]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4270,plain,
% 2.82/0.98      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k10_relat_1(sK2,X0) ),
% 2.82/0.98      inference(light_normalisation,[status(thm)],[c_4265,c_3648]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4449,plain,
% 2.82/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_4446,c_4270]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_6,plain,
% 2.82/0.98      ( ~ v1_relat_1(X0)
% 2.82/0.98      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 2.82/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1579,plain,
% 2.82/0.98      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 2.82/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3647,plain,
% 2.82/0.98      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_3641,c_1579]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3,plain,
% 2.82/0.98      ( r1_tarski(X0,X0) ),
% 2.82/0.98      inference(cnf_transformation,[],[f94]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1582,plain,
% 2.82/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_12,plain,
% 2.82/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 2.82/0.98      | ~ v1_funct_1(X1)
% 2.82/0.98      | ~ v2_funct_1(X1)
% 2.82/0.98      | ~ v1_relat_1(X1)
% 2.82/0.98      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ),
% 2.82/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_606,plain,
% 2.82/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 2.82/0.98      | ~ v1_funct_1(X1)
% 2.82/0.98      | ~ v1_relat_1(X1)
% 2.82/0.98      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
% 2.82/0.98      | sK2 != X1 ),
% 2.82/0.98      inference(resolution_lifted,[status(thm)],[c_12,c_27]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_607,plain,
% 2.82/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 2.82/0.98      | ~ v1_funct_1(sK2)
% 2.82/0.98      | ~ v1_relat_1(sK2)
% 2.82/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 2.82/0.98      inference(unflattening,[status(thm)],[c_606]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_611,plain,
% 2.82/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 2.82/0.98      | ~ v1_relat_1(sK2)
% 2.82/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_607,c_31]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1567,plain,
% 2.82/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 2.82/0.98      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 2.82/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_613,plain,
% 2.82/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 2.82/0.98      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 2.82/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1955,plain,
% 2.82/0.98      ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 2.82/0.98      | k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0 ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_1567,c_40,c_613,c_1886,c_1942]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1956,plain,
% 2.82/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,X0)) = X0
% 2.82/0.98      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 2.82/0.98      inference(renaming,[status(thm)],[c_1955]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1963,plain,
% 2.82/0.98      ( k10_relat_1(sK2,k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2) ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_1582,c_1956]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4169,plain,
% 2.82/0.98      ( k10_relat_1(sK2,k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 2.82/0.98      inference(demodulation,[status(thm)],[c_3647,c_1963]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4450,plain,
% 2.82/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.82/0.98      inference(light_normalisation,[status(thm)],[c_4449,c_4169]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4559,plain,
% 2.82/0.98      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_3352,c_4450]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_14,plain,
% 2.82/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.82/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.82/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1575,plain,
% 2.82/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.82/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3267,plain,
% 2.82/0.98      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_2654,c_1575]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3574,plain,
% 2.82/0.98      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.82/0.98      inference(light_normalisation,[status(thm)],[c_3267,c_3349]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4561,plain,
% 2.82/0.98      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.82/0.98      inference(light_normalisation,[status(thm)],[c_4559,c_3574]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4563,plain,
% 2.82/0.98      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_3741,c_4561]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_10,plain,
% 2.82/0.98      ( ~ v1_relat_1(X0)
% 2.82/0.98      | k2_relat_1(X0) = k1_xboole_0
% 2.82/0.98      | k1_relat_1(X0) != k1_xboole_0 ),
% 2.82/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1576,plain,
% 2.82/0.98      ( k2_relat_1(X0) = k1_xboole_0
% 2.82/0.98      | k1_relat_1(X0) != k1_xboole_0
% 2.82/0.98      | v1_relat_1(X0) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4705,plain,
% 2.82/0.98      ( k2_relat_1(sK2) = k1_xboole_0 | v1_relat_1(sK2) != iProver_top ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_4563,c_1576]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2014,plain,
% 2.82/0.98      ( ~ v1_relat_1(sK2)
% 2.82/0.98      | k2_relat_1(sK2) = k1_xboole_0
% 2.82/0.98      | k1_relat_1(sK2) != k1_xboole_0 ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_10]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4770,plain,
% 2.82/0.98      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_4705,c_29,c_1885,c_1941,c_2014,c_3741,c_4561]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_367,plain,
% 2.82/0.98      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.82/0.98      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_368,plain,
% 2.82/0.98      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.82/0.98      inference(unflattening,[status(thm)],[c_367]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_46,plain,
% 2.82/0.98      ( v2_struct_0(sK1)
% 2.82/0.98      | ~ l1_struct_0(sK1)
% 2.82/0.98      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.82/0.98      inference(instantiation,[status(thm)],[c_24]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_370,plain,
% 2.82/0.98      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_368,c_33,c_32,c_46]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_1570,plain,
% 2.82/0.98      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 2.82/0.98      inference(predicate_to_equality,[status(thm)],[c_370]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2660,plain,
% 2.82/0.98      ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 2.82/0.98      inference(demodulation,[status(thm)],[c_2648,c_1570]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4776,plain,
% 2.82/0.98      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.82/0.98      inference(demodulation,[status(thm)],[c_4770,c_2660]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_3270,plain,
% 2.82/0.98      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.82/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.82/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.82/0.98      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 2.82/0.98      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 2.82/0.98      inference(superposition,[status(thm)],[c_2654,c_1568]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2143,plain,
% 2.82/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_2064,c_1607,c_1597]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_2657,plain,
% 2.82/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 2.82/0.98      inference(demodulation,[status(thm)],[c_2648,c_2143]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4565,plain,
% 2.82/0.98      ( v1_xboole_0(k2_struct_0(sK0)) = iProver_top ),
% 2.82/0.98      inference(global_propositional_subsumption,
% 2.82/0.98                [status(thm)],
% 2.82/0.98                [c_3270,c_32,c_39,c_40,c_28,c_49,c_1771,c_1780,c_1976,
% 2.82/0.98                 c_2102,c_2311,c_2657,c_4561]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4569,plain,
% 2.82/0.98      ( v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 2.82/0.98      inference(light_normalisation,[status(thm)],[c_4565,c_3349]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(c_4642,plain,
% 2.82/0.98      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.82/0.98      inference(demodulation,[status(thm)],[c_4563,c_4569]) ).
% 2.82/0.98  
% 2.82/0.98  cnf(contradiction,plain,
% 2.82/0.98      ( $false ),
% 2.82/0.98      inference(minisat,[status(thm)],[c_4776,c_4642]) ).
% 2.82/0.98  
% 2.82/0.98  
% 2.82/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.82/0.98  
% 2.82/0.98  ------                               Statistics
% 2.82/0.98  
% 2.82/0.98  ------ General
% 2.82/0.98  
% 2.82/0.98  abstr_ref_over_cycles:                  0
% 2.82/0.98  abstr_ref_under_cycles:                 0
% 2.82/0.98  gc_basic_clause_elim:                   0
% 2.82/0.98  forced_gc_time:                         0
% 2.82/0.98  parsing_time:                           0.01
% 2.82/0.98  unif_index_cands_time:                  0.
% 2.82/0.98  unif_index_add_time:                    0.
% 2.82/0.98  orderings_time:                         0.
% 2.82/0.98  out_proof_time:                         0.014
% 2.82/0.98  total_time:                             0.168
% 2.82/0.98  num_of_symbols:                         59
% 2.82/0.98  num_of_terms:                           3620
% 2.82/0.98  
% 2.82/0.98  ------ Preprocessing
% 2.82/0.98  
% 2.82/0.98  num_of_splits:                          0
% 2.82/0.98  num_of_split_atoms:                     0
% 2.82/0.98  num_of_reused_defs:                     0
% 2.82/0.98  num_eq_ax_congr_red:                    14
% 2.82/0.98  num_of_sem_filtered_clauses:            1
% 2.82/0.98  num_of_subtypes:                        0
% 2.82/0.98  monotx_restored_types:                  0
% 2.82/0.98  sat_num_of_epr_types:                   0
% 2.82/0.98  sat_num_of_non_cyclic_types:            0
% 2.82/0.98  sat_guarded_non_collapsed_types:        0
% 2.82/0.98  num_pure_diseq_elim:                    0
% 2.82/0.98  simp_replaced_by:                       0
% 2.82/0.98  res_preprocessed:                       155
% 2.82/0.98  prep_upred:                             0
% 2.82/0.98  prep_unflattend:                        23
% 2.82/0.98  smt_new_axioms:                         0
% 2.82/0.98  pred_elim_cands:                        6
% 2.82/0.98  pred_elim:                              5
% 2.82/0.98  pred_elim_cl:                           6
% 2.82/0.98  pred_elim_cycles:                       11
% 2.82/0.98  merged_defs:                            0
% 2.82/0.98  merged_defs_ncl:                        0
% 2.82/0.98  bin_hyper_res:                          0
% 2.82/0.98  prep_cycles:                            4
% 2.82/0.98  pred_elim_time:                         0.012
% 2.82/0.98  splitting_time:                         0.
% 2.82/0.98  sem_filter_time:                        0.
% 2.82/0.98  monotx_time:                            0.
% 2.82/0.98  subtype_inf_time:                       0.
% 2.82/0.98  
% 2.82/0.98  ------ Problem properties
% 2.82/0.98  
% 2.82/0.98  clauses:                                27
% 2.82/0.98  conjectures:                            5
% 2.82/0.98  epr:                                    4
% 2.82/0.98  horn:                                   26
% 2.82/0.98  ground:                                 8
% 2.82/0.98  unary:                                  9
% 2.82/0.98  binary:                                 7
% 2.82/0.98  lits:                                   63
% 2.82/0.98  lits_eq:                                24
% 2.82/0.98  fd_pure:                                0
% 2.82/0.98  fd_pseudo:                              0
% 2.82/0.98  fd_cond:                                1
% 2.82/0.98  fd_pseudo_cond:                         2
% 2.82/0.98  ac_symbols:                             0
% 2.82/0.98  
% 2.82/0.98  ------ Propositional Solver
% 2.82/0.98  
% 2.82/0.98  prop_solver_calls:                      29
% 2.82/0.98  prop_fast_solver_calls:                 1092
% 2.82/0.98  smt_solver_calls:                       0
% 2.82/0.98  smt_fast_solver_calls:                  0
% 2.82/0.98  prop_num_of_clauses:                    1652
% 2.82/0.98  prop_preprocess_simplified:             5963
% 2.82/0.98  prop_fo_subsumed:                       35
% 2.82/0.98  prop_solver_time:                       0.
% 2.82/0.98  smt_solver_time:                        0.
% 2.82/0.98  smt_fast_solver_time:                   0.
% 2.82/0.98  prop_fast_solver_time:                  0.
% 2.82/0.98  prop_unsat_core_time:                   0.
% 2.82/0.98  
% 2.82/0.98  ------ QBF
% 2.82/0.98  
% 2.82/0.98  qbf_q_res:                              0
% 2.82/0.98  qbf_num_tautologies:                    0
% 2.82/0.98  qbf_prep_cycles:                        0
% 2.82/0.98  
% 2.82/0.98  ------ BMC1
% 2.82/0.98  
% 2.82/0.98  bmc1_current_bound:                     -1
% 2.82/0.98  bmc1_last_solved_bound:                 -1
% 2.82/0.98  bmc1_unsat_core_size:                   -1
% 2.82/0.98  bmc1_unsat_core_parents_size:           -1
% 2.82/0.98  bmc1_merge_next_fun:                    0
% 2.82/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.82/0.98  
% 2.82/0.98  ------ Instantiation
% 2.82/0.98  
% 2.82/0.98  inst_num_of_clauses:                    564
% 2.82/0.98  inst_num_in_passive:                    50
% 2.82/0.98  inst_num_in_active:                     344
% 2.82/0.98  inst_num_in_unprocessed:                170
% 2.82/0.98  inst_num_of_loops:                      370
% 2.82/0.98  inst_num_of_learning_restarts:          0
% 2.82/0.98  inst_num_moves_active_passive:          22
% 2.82/0.98  inst_lit_activity:                      0
% 2.82/0.98  inst_lit_activity_moves:                0
% 2.82/0.98  inst_num_tautologies:                   0
% 2.82/0.98  inst_num_prop_implied:                  0
% 2.82/0.98  inst_num_existing_simplified:           0
% 2.82/0.98  inst_num_eq_res_simplified:             0
% 2.82/0.98  inst_num_child_elim:                    0
% 2.82/0.98  inst_num_of_dismatching_blockings:      109
% 2.82/0.98  inst_num_of_non_proper_insts:           685
% 2.82/0.98  inst_num_of_duplicates:                 0
% 2.82/0.98  inst_inst_num_from_inst_to_res:         0
% 2.82/0.98  inst_dismatching_checking_time:         0.
% 2.82/0.98  
% 2.82/0.98  ------ Resolution
% 2.82/0.98  
% 2.82/0.98  res_num_of_clauses:                     0
% 2.82/0.98  res_num_in_passive:                     0
% 2.82/0.98  res_num_in_active:                      0
% 2.82/0.98  res_num_of_loops:                       159
% 2.82/0.98  res_forward_subset_subsumed:            78
% 2.82/0.98  res_backward_subset_subsumed:           4
% 2.82/0.98  res_forward_subsumed:                   0
% 2.82/0.98  res_backward_subsumed:                  0
% 2.82/0.98  res_forward_subsumption_resolution:     0
% 2.82/0.98  res_backward_subsumption_resolution:    0
% 2.82/0.98  res_clause_to_clause_subsumption:       106
% 2.82/0.98  res_orphan_elimination:                 0
% 2.82/0.98  res_tautology_del:                      116
% 2.82/0.98  res_num_eq_res_simplified:              0
% 2.82/0.98  res_num_sel_changes:                    0
% 2.82/0.98  res_moves_from_active_to_pass:          0
% 2.82/0.98  
% 2.82/0.98  ------ Superposition
% 2.82/0.98  
% 2.82/0.98  sup_time_total:                         0.
% 2.82/0.98  sup_time_generating:                    0.
% 2.82/0.98  sup_time_sim_full:                      0.
% 2.82/0.98  sup_time_sim_immed:                     0.
% 2.82/0.98  
% 2.82/0.98  sup_num_of_clauses:                     54
% 2.82/0.98  sup_num_in_active:                      28
% 2.82/0.98  sup_num_in_passive:                     26
% 2.82/0.98  sup_num_of_loops:                       73
% 2.82/0.98  sup_fw_superposition:                   14
% 2.82/0.98  sup_bw_superposition:                   45
% 2.82/0.98  sup_immediate_simplified:               15
% 2.82/0.98  sup_given_eliminated:                   0
% 2.82/0.98  comparisons_done:                       0
% 2.82/0.98  comparisons_avoided:                    3
% 2.82/0.98  
% 2.82/0.98  ------ Simplifications
% 2.82/0.98  
% 2.82/0.98  
% 2.82/0.98  sim_fw_subset_subsumed:                 12
% 2.82/0.98  sim_bw_subset_subsumed:                 3
% 2.82/0.98  sim_fw_subsumed:                        1
% 2.82/0.98  sim_bw_subsumed:                        1
% 2.82/0.98  sim_fw_subsumption_res:                 0
% 2.82/0.98  sim_bw_subsumption_res:                 0
% 2.82/0.98  sim_tautology_del:                      0
% 2.82/0.98  sim_eq_tautology_del:                   2
% 2.82/0.98  sim_eq_res_simp:                        0
% 2.82/0.98  sim_fw_demodulated:                     0
% 2.82/0.98  sim_bw_demodulated:                     44
% 2.82/0.98  sim_light_normalised:                   14
% 2.82/0.98  sim_joinable_taut:                      0
% 2.82/0.98  sim_joinable_simp:                      0
% 2.82/0.98  sim_ac_normalised:                      0
% 2.82/0.98  sim_smt_subsumption:                    0
% 2.82/0.98  
%------------------------------------------------------------------------------
