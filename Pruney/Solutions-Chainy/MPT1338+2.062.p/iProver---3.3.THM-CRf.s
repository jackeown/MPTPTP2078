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
% DateTime   : Thu Dec  3 12:17:12 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  161 (11234 expanded)
%              Number of clauses        :   92 (3124 expanded)
%              Number of leaves         :   18 (3248 expanded)
%              Depth                    :   24
%              Number of atoms          :  542 (79622 expanded)
%              Number of equality atoms :  222 (25829 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f17,conjecture,(
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

fof(f18,negated_conjecture,(
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
    inference(negated_conjecture,[],[f17])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f48,plain,(
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

fof(f47,plain,(
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

fof(f46,plain,
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

fof(f49,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f48,f47,f46])).

fof(f82,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f49])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f71,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f77,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f28])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f80,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f81,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f49])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f83,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k1_xboole_0 = k1_relat_1(X0)
      <=> k1_xboole_0 = k2_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f43,plain,(
    ! [X0] :
      ( ( ( k1_xboole_0 = k1_relat_1(X0)
          | k1_xboole_0 != k2_relat_1(X0) )
        & ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 != k1_relat_1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_relat_1(X0)
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f24,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f57,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1173,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_21,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_388,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_33])).

cnf(c_389,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_388])).

cnf(c_35,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_393,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_35])).

cnf(c_394,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_1210,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1173,c_389,c_394])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_20,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_502,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_20])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_504,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_8])).

cnf(c_1166,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_1503,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1210,c_1166])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1172,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1204,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1172,c_389,c_394])).

cnf(c_1345,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1204])).

cnf(c_22,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_375,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_376,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_375])).

cnf(c_378,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_376,c_33])).

cnf(c_1170,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_378])).

cnf(c_1199,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1170,c_389])).

cnf(c_1346,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1199])).

cnf(c_1504,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(k2_struct_0(sK1))
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1503])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1415,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_1532,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1629,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1978,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1503,c_32,c_30,c_1345,c_1346,c_1504,c_1532,c_1629])).

cnf(c_1983,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1978,c_1210])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1183,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2643,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1983,c_1183])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1207,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_29,c_389,c_394])).

cnf(c_1985,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1978,c_1207])).

cnf(c_2781,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2643,c_1985])).

cnf(c_3082,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2781,c_1983])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1177,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3809,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3082,c_1177])).

cnf(c_39,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k2_relat_1(X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1894,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) != k1_xboole_0
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_439,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_28])).

cnf(c_440,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_444,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_440,c_32])).

cnf(c_445,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_444])).

cnf(c_1169,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_445])).

cnf(c_1757,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1207,c_1169])).

cnf(c_1821,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1757,c_1204,c_1210])).

cnf(c_27,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1295,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_27,c_389,c_394])).

cnf(c_1824,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1821,c_1295])).

cnf(c_1981,plain,
    ( k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1978,c_1824])).

cnf(c_3081,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2781,c_1981])).

cnf(c_1984,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1978,c_1204])).

cnf(c_3084,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2781,c_1984])).

cnf(c_1982,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1978,c_1821])).

cnf(c_3083,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2781,c_1982])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1175,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3360,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3083,c_1175])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1176,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3559,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3083,c_1176])).

cnf(c_4464,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3559,c_39,c_3082,c_3084])).

cnf(c_4473,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4464,c_1177])).

cnf(c_4474,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4464,c_1183])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_477,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_28])).

cnf(c_478,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_477])).

cnf(c_480,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_478,c_32])).

cnf(c_1167,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_480])).

cnf(c_1658,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1167,c_32,c_30,c_478,c_1532,c_1629])).

cnf(c_4476,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4474,c_1658])).

cnf(c_4752,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3809,c_39,c_30,c_1532,c_1629,c_1894,c_3081,c_3082,c_3084,c_3360,c_4473,c_4476])).

cnf(c_3085,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2781,c_1199])).

cnf(c_4762,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4752,c_3085])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_115,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4762,c_115])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.46/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.46/0.99  
% 2.46/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.46/0.99  
% 2.46/0.99  ------  iProver source info
% 2.46/0.99  
% 2.46/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.46/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.46/0.99  git: non_committed_changes: false
% 2.46/0.99  git: last_make_outside_of_git: false
% 2.46/0.99  
% 2.46/0.99  ------ 
% 2.46/0.99  
% 2.46/0.99  ------ Input Options
% 2.46/0.99  
% 2.46/0.99  --out_options                           all
% 2.46/0.99  --tptp_safe_out                         true
% 2.46/0.99  --problem_path                          ""
% 2.46/0.99  --include_path                          ""
% 2.46/0.99  --clausifier                            res/vclausify_rel
% 2.46/0.99  --clausifier_options                    --mode clausify
% 2.46/0.99  --stdin                                 false
% 2.46/0.99  --stats_out                             all
% 2.46/0.99  
% 2.46/0.99  ------ General Options
% 2.46/0.99  
% 2.46/0.99  --fof                                   false
% 2.46/0.99  --time_out_real                         305.
% 2.46/0.99  --time_out_virtual                      -1.
% 2.46/0.99  --symbol_type_check                     false
% 2.46/0.99  --clausify_out                          false
% 2.46/0.99  --sig_cnt_out                           false
% 2.46/0.99  --trig_cnt_out                          false
% 2.46/0.99  --trig_cnt_out_tolerance                1.
% 2.46/0.99  --trig_cnt_out_sk_spl                   false
% 2.46/0.99  --abstr_cl_out                          false
% 2.46/0.99  
% 2.46/0.99  ------ Global Options
% 2.46/0.99  
% 2.46/0.99  --schedule                              default
% 2.46/0.99  --add_important_lit                     false
% 2.46/0.99  --prop_solver_per_cl                    1000
% 2.46/0.99  --min_unsat_core                        false
% 2.46/0.99  --soft_assumptions                      false
% 2.46/0.99  --soft_lemma_size                       3
% 2.46/0.99  --prop_impl_unit_size                   0
% 2.46/0.99  --prop_impl_unit                        []
% 2.46/0.99  --share_sel_clauses                     true
% 2.46/0.99  --reset_solvers                         false
% 2.46/0.99  --bc_imp_inh                            [conj_cone]
% 2.46/0.99  --conj_cone_tolerance                   3.
% 2.46/0.99  --extra_neg_conj                        none
% 2.46/0.99  --large_theory_mode                     true
% 2.46/0.99  --prolific_symb_bound                   200
% 2.46/0.99  --lt_threshold                          2000
% 2.46/0.99  --clause_weak_htbl                      true
% 2.46/0.99  --gc_record_bc_elim                     false
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing Options
% 2.46/0.99  
% 2.46/0.99  --preprocessing_flag                    true
% 2.46/0.99  --time_out_prep_mult                    0.1
% 2.46/0.99  --splitting_mode                        input
% 2.46/0.99  --splitting_grd                         true
% 2.46/0.99  --splitting_cvd                         false
% 2.46/0.99  --splitting_cvd_svl                     false
% 2.46/0.99  --splitting_nvd                         32
% 2.46/0.99  --sub_typing                            true
% 2.46/0.99  --prep_gs_sim                           true
% 2.46/0.99  --prep_unflatten                        true
% 2.46/0.99  --prep_res_sim                          true
% 2.46/0.99  --prep_upred                            true
% 2.46/0.99  --prep_sem_filter                       exhaustive
% 2.46/0.99  --prep_sem_filter_out                   false
% 2.46/0.99  --pred_elim                             true
% 2.46/0.99  --res_sim_input                         true
% 2.46/0.99  --eq_ax_congr_red                       true
% 2.46/0.99  --pure_diseq_elim                       true
% 2.46/0.99  --brand_transform                       false
% 2.46/0.99  --non_eq_to_eq                          false
% 2.46/0.99  --prep_def_merge                        true
% 2.46/0.99  --prep_def_merge_prop_impl              false
% 2.46/0.99  --prep_def_merge_mbd                    true
% 2.46/0.99  --prep_def_merge_tr_red                 false
% 2.46/0.99  --prep_def_merge_tr_cl                  false
% 2.46/0.99  --smt_preprocessing                     true
% 2.46/0.99  --smt_ac_axioms                         fast
% 2.46/0.99  --preprocessed_out                      false
% 2.46/0.99  --preprocessed_stats                    false
% 2.46/0.99  
% 2.46/0.99  ------ Abstraction refinement Options
% 2.46/0.99  
% 2.46/0.99  --abstr_ref                             []
% 2.46/0.99  --abstr_ref_prep                        false
% 2.46/0.99  --abstr_ref_until_sat                   false
% 2.46/0.99  --abstr_ref_sig_restrict                funpre
% 2.46/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/0.99  --abstr_ref_under                       []
% 2.46/0.99  
% 2.46/0.99  ------ SAT Options
% 2.46/0.99  
% 2.46/0.99  --sat_mode                              false
% 2.46/0.99  --sat_fm_restart_options                ""
% 2.46/0.99  --sat_gr_def                            false
% 2.46/0.99  --sat_epr_types                         true
% 2.46/0.99  --sat_non_cyclic_types                  false
% 2.46/0.99  --sat_finite_models                     false
% 2.46/0.99  --sat_fm_lemmas                         false
% 2.46/0.99  --sat_fm_prep                           false
% 2.46/0.99  --sat_fm_uc_incr                        true
% 2.46/0.99  --sat_out_model                         small
% 2.46/0.99  --sat_out_clauses                       false
% 2.46/0.99  
% 2.46/0.99  ------ QBF Options
% 2.46/0.99  
% 2.46/0.99  --qbf_mode                              false
% 2.46/0.99  --qbf_elim_univ                         false
% 2.46/0.99  --qbf_dom_inst                          none
% 2.46/0.99  --qbf_dom_pre_inst                      false
% 2.46/0.99  --qbf_sk_in                             false
% 2.46/0.99  --qbf_pred_elim                         true
% 2.46/0.99  --qbf_split                             512
% 2.46/0.99  
% 2.46/0.99  ------ BMC1 Options
% 2.46/0.99  
% 2.46/0.99  --bmc1_incremental                      false
% 2.46/0.99  --bmc1_axioms                           reachable_all
% 2.46/0.99  --bmc1_min_bound                        0
% 2.46/0.99  --bmc1_max_bound                        -1
% 2.46/0.99  --bmc1_max_bound_default                -1
% 2.46/0.99  --bmc1_symbol_reachability              true
% 2.46/0.99  --bmc1_property_lemmas                  false
% 2.46/0.99  --bmc1_k_induction                      false
% 2.46/0.99  --bmc1_non_equiv_states                 false
% 2.46/0.99  --bmc1_deadlock                         false
% 2.46/0.99  --bmc1_ucm                              false
% 2.46/0.99  --bmc1_add_unsat_core                   none
% 2.46/0.99  --bmc1_unsat_core_children              false
% 2.46/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/0.99  --bmc1_out_stat                         full
% 2.46/0.99  --bmc1_ground_init                      false
% 2.46/0.99  --bmc1_pre_inst_next_state              false
% 2.46/0.99  --bmc1_pre_inst_state                   false
% 2.46/0.99  --bmc1_pre_inst_reach_state             false
% 2.46/0.99  --bmc1_out_unsat_core                   false
% 2.46/0.99  --bmc1_aig_witness_out                  false
% 2.46/0.99  --bmc1_verbose                          false
% 2.46/0.99  --bmc1_dump_clauses_tptp                false
% 2.46/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.46/0.99  --bmc1_dump_file                        -
% 2.46/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.46/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.46/0.99  --bmc1_ucm_extend_mode                  1
% 2.46/0.99  --bmc1_ucm_init_mode                    2
% 2.46/0.99  --bmc1_ucm_cone_mode                    none
% 2.46/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.46/0.99  --bmc1_ucm_relax_model                  4
% 2.46/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.46/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/0.99  --bmc1_ucm_layered_model                none
% 2.46/0.99  --bmc1_ucm_max_lemma_size               10
% 2.46/0.99  
% 2.46/0.99  ------ AIG Options
% 2.46/0.99  
% 2.46/0.99  --aig_mode                              false
% 2.46/0.99  
% 2.46/0.99  ------ Instantiation Options
% 2.46/0.99  
% 2.46/0.99  --instantiation_flag                    true
% 2.46/0.99  --inst_sos_flag                         false
% 2.46/0.99  --inst_sos_phase                        true
% 2.46/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/0.99  --inst_lit_sel_side                     num_symb
% 2.46/0.99  --inst_solver_per_active                1400
% 2.46/0.99  --inst_solver_calls_frac                1.
% 2.46/0.99  --inst_passive_queue_type               priority_queues
% 2.46/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/0.99  --inst_passive_queues_freq              [25;2]
% 2.46/0.99  --inst_dismatching                      true
% 2.46/0.99  --inst_eager_unprocessed_to_passive     true
% 2.46/0.99  --inst_prop_sim_given                   true
% 2.46/0.99  --inst_prop_sim_new                     false
% 2.46/0.99  --inst_subs_new                         false
% 2.46/0.99  --inst_eq_res_simp                      false
% 2.46/0.99  --inst_subs_given                       false
% 2.46/0.99  --inst_orphan_elimination               true
% 2.46/0.99  --inst_learning_loop_flag               true
% 2.46/0.99  --inst_learning_start                   3000
% 2.46/0.99  --inst_learning_factor                  2
% 2.46/0.99  --inst_start_prop_sim_after_learn       3
% 2.46/0.99  --inst_sel_renew                        solver
% 2.46/0.99  --inst_lit_activity_flag                true
% 2.46/0.99  --inst_restr_to_given                   false
% 2.46/0.99  --inst_activity_threshold               500
% 2.46/0.99  --inst_out_proof                        true
% 2.46/0.99  
% 2.46/0.99  ------ Resolution Options
% 2.46/0.99  
% 2.46/0.99  --resolution_flag                       true
% 2.46/0.99  --res_lit_sel                           adaptive
% 2.46/0.99  --res_lit_sel_side                      none
% 2.46/0.99  --res_ordering                          kbo
% 2.46/0.99  --res_to_prop_solver                    active
% 2.46/0.99  --res_prop_simpl_new                    false
% 2.46/0.99  --res_prop_simpl_given                  true
% 2.46/0.99  --res_passive_queue_type                priority_queues
% 2.46/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/0.99  --res_passive_queues_freq               [15;5]
% 2.46/0.99  --res_forward_subs                      full
% 2.46/0.99  --res_backward_subs                     full
% 2.46/0.99  --res_forward_subs_resolution           true
% 2.46/0.99  --res_backward_subs_resolution          true
% 2.46/0.99  --res_orphan_elimination                true
% 2.46/0.99  --res_time_limit                        2.
% 2.46/0.99  --res_out_proof                         true
% 2.46/0.99  
% 2.46/0.99  ------ Superposition Options
% 2.46/0.99  
% 2.46/0.99  --superposition_flag                    true
% 2.46/0.99  --sup_passive_queue_type                priority_queues
% 2.46/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.46/0.99  --demod_completeness_check              fast
% 2.46/0.99  --demod_use_ground                      true
% 2.46/0.99  --sup_to_prop_solver                    passive
% 2.46/0.99  --sup_prop_simpl_new                    true
% 2.46/0.99  --sup_prop_simpl_given                  true
% 2.46/0.99  --sup_fun_splitting                     false
% 2.46/0.99  --sup_smt_interval                      50000
% 2.46/0.99  
% 2.46/0.99  ------ Superposition Simplification Setup
% 2.46/0.99  
% 2.46/0.99  --sup_indices_passive                   []
% 2.46/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_full_bw                           [BwDemod]
% 2.46/0.99  --sup_immed_triv                        [TrivRules]
% 2.46/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_immed_bw_main                     []
% 2.46/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.99  
% 2.46/0.99  ------ Combination Options
% 2.46/0.99  
% 2.46/0.99  --comb_res_mult                         3
% 2.46/0.99  --comb_sup_mult                         2
% 2.46/0.99  --comb_inst_mult                        10
% 2.46/0.99  
% 2.46/0.99  ------ Debug Options
% 2.46/0.99  
% 2.46/0.99  --dbg_backtrace                         false
% 2.46/0.99  --dbg_dump_prop_clauses                 false
% 2.46/0.99  --dbg_dump_prop_clauses_file            -
% 2.46/0.99  --dbg_out_stat                          false
% 2.46/0.99  ------ Parsing...
% 2.46/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.46/0.99  ------ Proving...
% 2.46/0.99  ------ Problem Properties 
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  clauses                                 29
% 2.46/0.99  conjectures                             5
% 2.46/0.99  EPR                                     2
% 2.46/0.99  Horn                                    24
% 2.46/0.99  unary                                   9
% 2.46/0.99  binary                                  5
% 2.46/0.99  lits                                    74
% 2.46/0.99  lits eq                                 24
% 2.46/0.99  fd_pure                                 0
% 2.46/0.99  fd_pseudo                               0
% 2.46/0.99  fd_cond                                 3
% 2.46/0.99  fd_pseudo_cond                          1
% 2.46/0.99  AC symbols                              0
% 2.46/0.99  
% 2.46/0.99  ------ Schedule dynamic 5 is on 
% 2.46/0.99  
% 2.46/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  ------ 
% 2.46/0.99  Current options:
% 2.46/0.99  ------ 
% 2.46/0.99  
% 2.46/0.99  ------ Input Options
% 2.46/0.99  
% 2.46/0.99  --out_options                           all
% 2.46/0.99  --tptp_safe_out                         true
% 2.46/0.99  --problem_path                          ""
% 2.46/0.99  --include_path                          ""
% 2.46/0.99  --clausifier                            res/vclausify_rel
% 2.46/0.99  --clausifier_options                    --mode clausify
% 2.46/0.99  --stdin                                 false
% 2.46/0.99  --stats_out                             all
% 2.46/0.99  
% 2.46/0.99  ------ General Options
% 2.46/0.99  
% 2.46/0.99  --fof                                   false
% 2.46/0.99  --time_out_real                         305.
% 2.46/0.99  --time_out_virtual                      -1.
% 2.46/0.99  --symbol_type_check                     false
% 2.46/0.99  --clausify_out                          false
% 2.46/0.99  --sig_cnt_out                           false
% 2.46/0.99  --trig_cnt_out                          false
% 2.46/0.99  --trig_cnt_out_tolerance                1.
% 2.46/0.99  --trig_cnt_out_sk_spl                   false
% 2.46/0.99  --abstr_cl_out                          false
% 2.46/0.99  
% 2.46/0.99  ------ Global Options
% 2.46/0.99  
% 2.46/0.99  --schedule                              default
% 2.46/0.99  --add_important_lit                     false
% 2.46/0.99  --prop_solver_per_cl                    1000
% 2.46/0.99  --min_unsat_core                        false
% 2.46/0.99  --soft_assumptions                      false
% 2.46/0.99  --soft_lemma_size                       3
% 2.46/0.99  --prop_impl_unit_size                   0
% 2.46/0.99  --prop_impl_unit                        []
% 2.46/0.99  --share_sel_clauses                     true
% 2.46/0.99  --reset_solvers                         false
% 2.46/0.99  --bc_imp_inh                            [conj_cone]
% 2.46/0.99  --conj_cone_tolerance                   3.
% 2.46/0.99  --extra_neg_conj                        none
% 2.46/0.99  --large_theory_mode                     true
% 2.46/0.99  --prolific_symb_bound                   200
% 2.46/0.99  --lt_threshold                          2000
% 2.46/0.99  --clause_weak_htbl                      true
% 2.46/0.99  --gc_record_bc_elim                     false
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing Options
% 2.46/0.99  
% 2.46/0.99  --preprocessing_flag                    true
% 2.46/0.99  --time_out_prep_mult                    0.1
% 2.46/0.99  --splitting_mode                        input
% 2.46/0.99  --splitting_grd                         true
% 2.46/0.99  --splitting_cvd                         false
% 2.46/0.99  --splitting_cvd_svl                     false
% 2.46/0.99  --splitting_nvd                         32
% 2.46/0.99  --sub_typing                            true
% 2.46/0.99  --prep_gs_sim                           true
% 2.46/0.99  --prep_unflatten                        true
% 2.46/0.99  --prep_res_sim                          true
% 2.46/0.99  --prep_upred                            true
% 2.46/0.99  --prep_sem_filter                       exhaustive
% 2.46/0.99  --prep_sem_filter_out                   false
% 2.46/0.99  --pred_elim                             true
% 2.46/0.99  --res_sim_input                         true
% 2.46/0.99  --eq_ax_congr_red                       true
% 2.46/0.99  --pure_diseq_elim                       true
% 2.46/0.99  --brand_transform                       false
% 2.46/0.99  --non_eq_to_eq                          false
% 2.46/0.99  --prep_def_merge                        true
% 2.46/0.99  --prep_def_merge_prop_impl              false
% 2.46/0.99  --prep_def_merge_mbd                    true
% 2.46/0.99  --prep_def_merge_tr_red                 false
% 2.46/0.99  --prep_def_merge_tr_cl                  false
% 2.46/0.99  --smt_preprocessing                     true
% 2.46/0.99  --smt_ac_axioms                         fast
% 2.46/0.99  --preprocessed_out                      false
% 2.46/0.99  --preprocessed_stats                    false
% 2.46/0.99  
% 2.46/0.99  ------ Abstraction refinement Options
% 2.46/0.99  
% 2.46/0.99  --abstr_ref                             []
% 2.46/0.99  --abstr_ref_prep                        false
% 2.46/0.99  --abstr_ref_until_sat                   false
% 2.46/0.99  --abstr_ref_sig_restrict                funpre
% 2.46/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/0.99  --abstr_ref_under                       []
% 2.46/0.99  
% 2.46/0.99  ------ SAT Options
% 2.46/0.99  
% 2.46/0.99  --sat_mode                              false
% 2.46/0.99  --sat_fm_restart_options                ""
% 2.46/0.99  --sat_gr_def                            false
% 2.46/0.99  --sat_epr_types                         true
% 2.46/0.99  --sat_non_cyclic_types                  false
% 2.46/0.99  --sat_finite_models                     false
% 2.46/0.99  --sat_fm_lemmas                         false
% 2.46/0.99  --sat_fm_prep                           false
% 2.46/0.99  --sat_fm_uc_incr                        true
% 2.46/0.99  --sat_out_model                         small
% 2.46/0.99  --sat_out_clauses                       false
% 2.46/0.99  
% 2.46/0.99  ------ QBF Options
% 2.46/0.99  
% 2.46/0.99  --qbf_mode                              false
% 2.46/0.99  --qbf_elim_univ                         false
% 2.46/0.99  --qbf_dom_inst                          none
% 2.46/0.99  --qbf_dom_pre_inst                      false
% 2.46/0.99  --qbf_sk_in                             false
% 2.46/0.99  --qbf_pred_elim                         true
% 2.46/0.99  --qbf_split                             512
% 2.46/0.99  
% 2.46/0.99  ------ BMC1 Options
% 2.46/0.99  
% 2.46/0.99  --bmc1_incremental                      false
% 2.46/0.99  --bmc1_axioms                           reachable_all
% 2.46/0.99  --bmc1_min_bound                        0
% 2.46/0.99  --bmc1_max_bound                        -1
% 2.46/0.99  --bmc1_max_bound_default                -1
% 2.46/0.99  --bmc1_symbol_reachability              true
% 2.46/0.99  --bmc1_property_lemmas                  false
% 2.46/0.99  --bmc1_k_induction                      false
% 2.46/0.99  --bmc1_non_equiv_states                 false
% 2.46/0.99  --bmc1_deadlock                         false
% 2.46/0.99  --bmc1_ucm                              false
% 2.46/0.99  --bmc1_add_unsat_core                   none
% 2.46/0.99  --bmc1_unsat_core_children              false
% 2.46/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/0.99  --bmc1_out_stat                         full
% 2.46/0.99  --bmc1_ground_init                      false
% 2.46/0.99  --bmc1_pre_inst_next_state              false
% 2.46/0.99  --bmc1_pre_inst_state                   false
% 2.46/0.99  --bmc1_pre_inst_reach_state             false
% 2.46/0.99  --bmc1_out_unsat_core                   false
% 2.46/0.99  --bmc1_aig_witness_out                  false
% 2.46/0.99  --bmc1_verbose                          false
% 2.46/0.99  --bmc1_dump_clauses_tptp                false
% 2.46/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.46/0.99  --bmc1_dump_file                        -
% 2.46/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.46/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.46/0.99  --bmc1_ucm_extend_mode                  1
% 2.46/0.99  --bmc1_ucm_init_mode                    2
% 2.46/0.99  --bmc1_ucm_cone_mode                    none
% 2.46/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.46/0.99  --bmc1_ucm_relax_model                  4
% 2.46/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.46/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/0.99  --bmc1_ucm_layered_model                none
% 2.46/0.99  --bmc1_ucm_max_lemma_size               10
% 2.46/0.99  
% 2.46/0.99  ------ AIG Options
% 2.46/0.99  
% 2.46/0.99  --aig_mode                              false
% 2.46/0.99  
% 2.46/0.99  ------ Instantiation Options
% 2.46/0.99  
% 2.46/0.99  --instantiation_flag                    true
% 2.46/0.99  --inst_sos_flag                         false
% 2.46/0.99  --inst_sos_phase                        true
% 2.46/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/0.99  --inst_lit_sel_side                     none
% 2.46/0.99  --inst_solver_per_active                1400
% 2.46/0.99  --inst_solver_calls_frac                1.
% 2.46/0.99  --inst_passive_queue_type               priority_queues
% 2.46/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/0.99  --inst_passive_queues_freq              [25;2]
% 2.46/0.99  --inst_dismatching                      true
% 2.46/0.99  --inst_eager_unprocessed_to_passive     true
% 2.46/0.99  --inst_prop_sim_given                   true
% 2.46/0.99  --inst_prop_sim_new                     false
% 2.46/0.99  --inst_subs_new                         false
% 2.46/0.99  --inst_eq_res_simp                      false
% 2.46/0.99  --inst_subs_given                       false
% 2.46/0.99  --inst_orphan_elimination               true
% 2.46/0.99  --inst_learning_loop_flag               true
% 2.46/0.99  --inst_learning_start                   3000
% 2.46/0.99  --inst_learning_factor                  2
% 2.46/0.99  --inst_start_prop_sim_after_learn       3
% 2.46/0.99  --inst_sel_renew                        solver
% 2.46/0.99  --inst_lit_activity_flag                true
% 2.46/0.99  --inst_restr_to_given                   false
% 2.46/0.99  --inst_activity_threshold               500
% 2.46/0.99  --inst_out_proof                        true
% 2.46/0.99  
% 2.46/0.99  ------ Resolution Options
% 2.46/0.99  
% 2.46/0.99  --resolution_flag                       false
% 2.46/0.99  --res_lit_sel                           adaptive
% 2.46/0.99  --res_lit_sel_side                      none
% 2.46/0.99  --res_ordering                          kbo
% 2.46/0.99  --res_to_prop_solver                    active
% 2.46/0.99  --res_prop_simpl_new                    false
% 2.46/0.99  --res_prop_simpl_given                  true
% 2.46/0.99  --res_passive_queue_type                priority_queues
% 2.46/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/0.99  --res_passive_queues_freq               [15;5]
% 2.46/0.99  --res_forward_subs                      full
% 2.46/0.99  --res_backward_subs                     full
% 2.46/0.99  --res_forward_subs_resolution           true
% 2.46/0.99  --res_backward_subs_resolution          true
% 2.46/0.99  --res_orphan_elimination                true
% 2.46/0.99  --res_time_limit                        2.
% 2.46/0.99  --res_out_proof                         true
% 2.46/0.99  
% 2.46/0.99  ------ Superposition Options
% 2.46/0.99  
% 2.46/0.99  --superposition_flag                    true
% 2.46/0.99  --sup_passive_queue_type                priority_queues
% 2.46/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.46/0.99  --demod_completeness_check              fast
% 2.46/0.99  --demod_use_ground                      true
% 2.46/0.99  --sup_to_prop_solver                    passive
% 2.46/0.99  --sup_prop_simpl_new                    true
% 2.46/0.99  --sup_prop_simpl_given                  true
% 2.46/0.99  --sup_fun_splitting                     false
% 2.46/0.99  --sup_smt_interval                      50000
% 2.46/0.99  
% 2.46/0.99  ------ Superposition Simplification Setup
% 2.46/0.99  
% 2.46/0.99  --sup_indices_passive                   []
% 2.46/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_full_bw                           [BwDemod]
% 2.46/0.99  --sup_immed_triv                        [TrivRules]
% 2.46/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_immed_bw_main                     []
% 2.46/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/0.99  
% 2.46/0.99  ------ Combination Options
% 2.46/0.99  
% 2.46/0.99  --comb_res_mult                         3
% 2.46/0.99  --comb_sup_mult                         2
% 2.46/0.99  --comb_inst_mult                        10
% 2.46/0.99  
% 2.46/0.99  ------ Debug Options
% 2.46/0.99  
% 2.46/0.99  --dbg_backtrace                         false
% 2.46/0.99  --dbg_dump_prop_clauses                 false
% 2.46/0.99  --dbg_dump_prop_clauses_file            -
% 2.46/0.99  --dbg_out_stat                          false
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  ------ Proving...
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  % SZS status Theorem for theBenchmark.p
% 2.46/0.99  
% 2.46/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.46/0.99  
% 2.46/0.99  fof(f17,conjecture,(
% 2.46/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f18,negated_conjecture,(
% 2.46/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.46/0.99    inference(negated_conjecture,[],[f17])).
% 2.46/0.99  
% 2.46/0.99  fof(f41,plain,(
% 2.46/0.99    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.46/0.99    inference(ennf_transformation,[],[f18])).
% 2.46/0.99  
% 2.46/0.99  fof(f42,plain,(
% 2.46/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.46/0.99    inference(flattening,[],[f41])).
% 2.46/0.99  
% 2.46/0.99  fof(f48,plain,(
% 2.46/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.46/0.99    introduced(choice_axiom,[])).
% 2.46/0.99  
% 2.46/0.99  fof(f47,plain,(
% 2.46/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.46/0.99    introduced(choice_axiom,[])).
% 2.46/0.99  
% 2.46/0.99  fof(f46,plain,(
% 2.46/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.46/0.99    introduced(choice_axiom,[])).
% 2.46/0.99  
% 2.46/0.99  fof(f49,plain,(
% 2.46/0.99    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.46/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f48,f47,f46])).
% 2.46/0.99  
% 2.46/0.99  fof(f82,plain,(
% 2.46/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.46/0.99    inference(cnf_transformation,[],[f49])).
% 2.46/0.99  
% 2.46/0.99  fof(f13,axiom,(
% 2.46/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f34,plain,(
% 2.46/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.46/0.99    inference(ennf_transformation,[],[f13])).
% 2.46/0.99  
% 2.46/0.99  fof(f71,plain,(
% 2.46/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.46/0.99    inference(cnf_transformation,[],[f34])).
% 2.46/0.99  
% 2.46/0.99  fof(f79,plain,(
% 2.46/0.99    l1_struct_0(sK1)),
% 2.46/0.99    inference(cnf_transformation,[],[f49])).
% 2.46/0.99  
% 2.46/0.99  fof(f77,plain,(
% 2.46/0.99    l1_struct_0(sK0)),
% 2.46/0.99    inference(cnf_transformation,[],[f49])).
% 2.46/0.99  
% 2.46/0.99  fof(f10,axiom,(
% 2.46/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f28,plain,(
% 2.46/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.46/0.99    inference(ennf_transformation,[],[f10])).
% 2.46/0.99  
% 2.46/0.99  fof(f29,plain,(
% 2.46/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.46/0.99    inference(flattening,[],[f28])).
% 2.46/0.99  
% 2.46/0.99  fof(f62,plain,(
% 2.46/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.46/0.99    inference(cnf_transformation,[],[f29])).
% 2.46/0.99  
% 2.46/0.99  fof(f12,axiom,(
% 2.46/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f32,plain,(
% 2.46/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.46/0.99    inference(ennf_transformation,[],[f12])).
% 2.46/0.99  
% 2.46/0.99  fof(f33,plain,(
% 2.46/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.46/0.99    inference(flattening,[],[f32])).
% 2.46/0.99  
% 2.46/0.99  fof(f45,plain,(
% 2.46/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.46/0.99    inference(nnf_transformation,[],[f33])).
% 2.46/0.99  
% 2.46/0.99  fof(f69,plain,(
% 2.46/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.46/0.99    inference(cnf_transformation,[],[f45])).
% 2.46/0.99  
% 2.46/0.99  fof(f7,axiom,(
% 2.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f19,plain,(
% 2.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.46/0.99    inference(pure_predicate_removal,[],[f7])).
% 2.46/0.99  
% 2.46/0.99  fof(f25,plain,(
% 2.46/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/0.99    inference(ennf_transformation,[],[f19])).
% 2.46/0.99  
% 2.46/0.99  fof(f58,plain,(
% 2.46/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/0.99    inference(cnf_transformation,[],[f25])).
% 2.46/0.99  
% 2.46/0.99  fof(f80,plain,(
% 2.46/0.99    v1_funct_1(sK2)),
% 2.46/0.99    inference(cnf_transformation,[],[f49])).
% 2.46/0.99  
% 2.46/0.99  fof(f81,plain,(
% 2.46/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.46/0.99    inference(cnf_transformation,[],[f49])).
% 2.46/0.99  
% 2.46/0.99  fof(f14,axiom,(
% 2.46/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f35,plain,(
% 2.46/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.46/0.99    inference(ennf_transformation,[],[f14])).
% 2.46/0.99  
% 2.46/0.99  fof(f36,plain,(
% 2.46/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.46/0.99    inference(flattening,[],[f35])).
% 2.46/0.99  
% 2.46/0.99  fof(f72,plain,(
% 2.46/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.46/0.99    inference(cnf_transformation,[],[f36])).
% 2.46/0.99  
% 2.46/0.99  fof(f78,plain,(
% 2.46/0.99    ~v2_struct_0(sK1)),
% 2.46/0.99    inference(cnf_transformation,[],[f49])).
% 2.46/0.99  
% 2.46/0.99  fof(f2,axiom,(
% 2.46/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f20,plain,(
% 2.46/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.46/0.99    inference(ennf_transformation,[],[f2])).
% 2.46/0.99  
% 2.46/0.99  fof(f51,plain,(
% 2.46/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.46/0.99    inference(cnf_transformation,[],[f20])).
% 2.46/0.99  
% 2.46/0.99  fof(f4,axiom,(
% 2.46/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f53,plain,(
% 2.46/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.46/0.99    inference(cnf_transformation,[],[f4])).
% 2.46/0.99  
% 2.46/0.99  fof(f9,axiom,(
% 2.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f27,plain,(
% 2.46/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/0.99    inference(ennf_transformation,[],[f9])).
% 2.46/0.99  
% 2.46/0.99  fof(f60,plain,(
% 2.46/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/0.99    inference(cnf_transformation,[],[f27])).
% 2.46/0.99  
% 2.46/0.99  fof(f83,plain,(
% 2.46/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.46/0.99    inference(cnf_transformation,[],[f49])).
% 2.46/0.99  
% 2.46/0.99  fof(f11,axiom,(
% 2.46/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f30,plain,(
% 2.46/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/0.99    inference(ennf_transformation,[],[f11])).
% 2.46/0.99  
% 2.46/0.99  fof(f31,plain,(
% 2.46/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/0.99    inference(flattening,[],[f30])).
% 2.46/0.99  
% 2.46/0.99  fof(f44,plain,(
% 2.46/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/0.99    inference(nnf_transformation,[],[f31])).
% 2.46/0.99  
% 2.46/0.99  fof(f63,plain,(
% 2.46/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/0.99    inference(cnf_transformation,[],[f44])).
% 2.46/0.99  
% 2.46/0.99  fof(f5,axiom,(
% 2.46/0.99    ! [X0] : (v1_relat_1(X0) => (k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f22,plain,(
% 2.46/0.99    ! [X0] : ((k1_xboole_0 = k1_relat_1(X0) <=> k1_xboole_0 = k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.46/0.99    inference(ennf_transformation,[],[f5])).
% 2.46/0.99  
% 2.46/0.99  fof(f43,plain,(
% 2.46/0.99    ! [X0] : (((k1_xboole_0 = k1_relat_1(X0) | k1_xboole_0 != k2_relat_1(X0)) & (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.46/0.99    inference(nnf_transformation,[],[f22])).
% 2.46/0.99  
% 2.46/0.99  fof(f54,plain,(
% 2.46/0.99    ( ! [X0] : (k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 2.46/0.99    inference(cnf_transformation,[],[f43])).
% 2.46/0.99  
% 2.46/0.99  fof(f15,axiom,(
% 2.46/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f37,plain,(
% 2.46/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.46/0.99    inference(ennf_transformation,[],[f15])).
% 2.46/0.99  
% 2.46/0.99  fof(f38,plain,(
% 2.46/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.46/0.99    inference(flattening,[],[f37])).
% 2.46/0.99  
% 2.46/0.99  fof(f73,plain,(
% 2.46/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.46/0.99    inference(cnf_transformation,[],[f38])).
% 2.46/0.99  
% 2.46/0.99  fof(f84,plain,(
% 2.46/0.99    v2_funct_1(sK2)),
% 2.46/0.99    inference(cnf_transformation,[],[f49])).
% 2.46/0.99  
% 2.46/0.99  fof(f85,plain,(
% 2.46/0.99    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.46/0.99    inference(cnf_transformation,[],[f49])).
% 2.46/0.99  
% 2.46/0.99  fof(f16,axiom,(
% 2.46/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f39,plain,(
% 2.46/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.46/0.99    inference(ennf_transformation,[],[f16])).
% 2.46/0.99  
% 2.46/0.99  fof(f40,plain,(
% 2.46/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.46/0.99    inference(flattening,[],[f39])).
% 2.46/0.99  
% 2.46/0.99  fof(f75,plain,(
% 2.46/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.46/0.99    inference(cnf_transformation,[],[f40])).
% 2.46/0.99  
% 2.46/0.99  fof(f76,plain,(
% 2.46/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.46/0.99    inference(cnf_transformation,[],[f40])).
% 2.46/0.99  
% 2.46/0.99  fof(f6,axiom,(
% 2.46/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f23,plain,(
% 2.46/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.46/0.99    inference(ennf_transformation,[],[f6])).
% 2.46/0.99  
% 2.46/0.99  fof(f24,plain,(
% 2.46/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.46/0.99    inference(flattening,[],[f23])).
% 2.46/0.99  
% 2.46/0.99  fof(f57,plain,(
% 2.46/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.46/0.99    inference(cnf_transformation,[],[f24])).
% 2.46/0.99  
% 2.46/0.99  fof(f1,axiom,(
% 2.46/0.99    v1_xboole_0(k1_xboole_0)),
% 2.46/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.46/0.99  
% 2.46/0.99  fof(f50,plain,(
% 2.46/0.99    v1_xboole_0(k1_xboole_0)),
% 2.46/0.99    inference(cnf_transformation,[],[f1])).
% 2.46/0.99  
% 2.46/0.99  cnf(c_30,negated_conjecture,
% 2.46/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.46/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1173,plain,
% 2.46/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_21,plain,
% 2.46/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.46/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_33,negated_conjecture,
% 2.46/0.99      ( l1_struct_0(sK1) ),
% 2.46/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_388,plain,
% 2.46/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.46/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_33]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_389,plain,
% 2.46/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.46/0.99      inference(unflattening,[status(thm)],[c_388]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_35,negated_conjecture,
% 2.46/0.99      ( l1_struct_0(sK0) ),
% 2.46/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_393,plain,
% 2.46/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.46/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_35]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_394,plain,
% 2.46/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.46/0.99      inference(unflattening,[status(thm)],[c_393]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1210,plain,
% 2.46/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.46/0.99      inference(light_normalisation,[status(thm)],[c_1173,c_389,c_394]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_11,plain,
% 2.46/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/0.99      | v1_partfun1(X0,X1)
% 2.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/0.99      | ~ v1_funct_1(X0)
% 2.46/0.99      | v1_xboole_0(X2) ),
% 2.46/0.99      inference(cnf_transformation,[],[f62]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_20,plain,
% 2.46/0.99      ( ~ v1_partfun1(X0,X1)
% 2.46/0.99      | ~ v4_relat_1(X0,X1)
% 2.46/0.99      | ~ v1_relat_1(X0)
% 2.46/0.99      | k1_relat_1(X0) = X1 ),
% 2.46/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_502,plain,
% 2.46/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/0.99      | ~ v4_relat_1(X0,X1)
% 2.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/0.99      | ~ v1_funct_1(X0)
% 2.46/0.99      | ~ v1_relat_1(X0)
% 2.46/0.99      | v1_xboole_0(X2)
% 2.46/0.99      | k1_relat_1(X0) = X1 ),
% 2.46/0.99      inference(resolution,[status(thm)],[c_11,c_20]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_8,plain,
% 2.46/0.99      ( v4_relat_1(X0,X1)
% 2.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.46/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_504,plain,
% 2.46/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/0.99      | ~ v1_funct_1(X0)
% 2.46/0.99      | ~ v1_relat_1(X0)
% 2.46/0.99      | v1_xboole_0(X2)
% 2.46/0.99      | k1_relat_1(X0) = X1 ),
% 2.46/0.99      inference(global_propositional_subsumption,
% 2.46/0.99                [status(thm)],
% 2.46/0.99                [c_502,c_8]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1166,plain,
% 2.46/0.99      ( k1_relat_1(X0) = X1
% 2.46/0.99      | v1_funct_2(X0,X1,X2) != iProver_top
% 2.46/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.46/0.99      | v1_funct_1(X0) != iProver_top
% 2.46/0.99      | v1_relat_1(X0) != iProver_top
% 2.46/0.99      | v1_xboole_0(X2) = iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1503,plain,
% 2.46/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.46/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.46/0.99      | v1_funct_1(sK2) != iProver_top
% 2.46/0.99      | v1_relat_1(sK2) != iProver_top
% 2.46/0.99      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top ),
% 2.46/0.99      inference(superposition,[status(thm)],[c_1210,c_1166]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_32,negated_conjecture,
% 2.46/0.99      ( v1_funct_1(sK2) ),
% 2.46/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_31,negated_conjecture,
% 2.46/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.46/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1172,plain,
% 2.46/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1204,plain,
% 2.46/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.46/0.99      inference(light_normalisation,[status(thm)],[c_1172,c_389,c_394]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1345,plain,
% 2.46/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
% 2.46/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1204]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_22,plain,
% 2.46/0.99      ( v2_struct_0(X0)
% 2.46/0.99      | ~ l1_struct_0(X0)
% 2.46/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.46/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_34,negated_conjecture,
% 2.46/0.99      ( ~ v2_struct_0(sK1) ),
% 2.46/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_375,plain,
% 2.46/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.46/0.99      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_376,plain,
% 2.46/0.99      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.46/0.99      inference(unflattening,[status(thm)],[c_375]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_378,plain,
% 2.46/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.46/0.99      inference(global_propositional_subsumption,
% 2.46/0.99                [status(thm)],
% 2.46/0.99                [c_376,c_33]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1170,plain,
% 2.46/0.99      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_378]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1199,plain,
% 2.46/0.99      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 2.46/0.99      inference(light_normalisation,[status(thm)],[c_1170,c_389]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1346,plain,
% 2.46/0.99      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.46/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1199]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1504,plain,
% 2.46/0.99      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
% 2.46/0.99      | ~ v1_funct_1(sK2)
% 2.46/0.99      | ~ v1_relat_1(sK2)
% 2.46/0.99      | v1_xboole_0(k2_struct_0(sK1))
% 2.46/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.46/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1503]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1,plain,
% 2.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.46/0.99      | ~ v1_relat_1(X1)
% 2.46/0.99      | v1_relat_1(X0) ),
% 2.46/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1415,plain,
% 2.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/0.99      | v1_relat_1(X0)
% 2.46/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1532,plain,
% 2.46/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.46/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.46/0.99      | v1_relat_1(sK2) ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_1415]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3,plain,
% 2.46/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.46/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1629,plain,
% 2.46/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1978,plain,
% 2.46/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.46/0.99      inference(global_propositional_subsumption,
% 2.46/0.99                [status(thm)],
% 2.46/0.99                [c_1503,c_32,c_30,c_1345,c_1346,c_1504,c_1532,c_1629]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1983,plain,
% 2.46/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_1978,c_1210]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_10,plain,
% 2.46/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.46/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1183,plain,
% 2.46/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.46/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_2643,plain,
% 2.46/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.46/0.99      inference(superposition,[status(thm)],[c_1983,c_1183]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_29,negated_conjecture,
% 2.46/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.46/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1207,plain,
% 2.46/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.46/0.99      inference(light_normalisation,[status(thm)],[c_29,c_389,c_394]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1985,plain,
% 2.46/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_1978,c_1207]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_2781,plain,
% 2.46/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_2643,c_1985]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3082,plain,
% 2.46/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_2781,c_1983]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_18,plain,
% 2.46/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.46/0.99      | k1_xboole_0 = X2 ),
% 2.46/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1177,plain,
% 2.46/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 2.46/0.99      | k1_xboole_0 = X1
% 2.46/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.46/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3809,plain,
% 2.46/0.99      ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k1_relat_1(sK2)
% 2.46/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 2.46/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top ),
% 2.46/0.99      inference(superposition,[status(thm)],[c_3082,c_1177]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_39,plain,
% 2.46/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_5,plain,
% 2.46/0.99      ( ~ v1_relat_1(X0)
% 2.46/0.99      | k1_relat_1(X0) != k1_xboole_0
% 2.46/0.99      | k2_relat_1(X0) = k1_xboole_0 ),
% 2.46/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1894,plain,
% 2.46/0.99      ( ~ v1_relat_1(sK2)
% 2.46/0.99      | k1_relat_1(sK2) != k1_xboole_0
% 2.46/0.99      | k2_relat_1(sK2) = k1_xboole_0 ),
% 2.46/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_23,plain,
% 2.46/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/0.99      | ~ v1_funct_1(X0)
% 2.46/0.99      | ~ v2_funct_1(X0)
% 2.46/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.46/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.46/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_28,negated_conjecture,
% 2.46/0.99      ( v2_funct_1(sK2) ),
% 2.46/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_439,plain,
% 2.46/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/0.99      | ~ v1_funct_1(X0)
% 2.46/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.46/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.46/0.99      | sK2 != X0 ),
% 2.46/0.99      inference(resolution_lifted,[status(thm)],[c_23,c_28]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_440,plain,
% 2.46/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.46/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.46/0.99      | ~ v1_funct_1(sK2)
% 2.46/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.46/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.46/0.99      inference(unflattening,[status(thm)],[c_439]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_444,plain,
% 2.46/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.46/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.46/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.46/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.46/0.99      inference(global_propositional_subsumption,
% 2.46/0.99                [status(thm)],
% 2.46/0.99                [c_440,c_32]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_445,plain,
% 2.46/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.46/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.46/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.46/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.46/0.99      inference(renaming,[status(thm)],[c_444]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1169,plain,
% 2.46/0.99      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.46/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 2.46/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.46/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_445]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1757,plain,
% 2.46/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.46/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.46/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.46/0.99      inference(superposition,[status(thm)],[c_1207,c_1169]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1821,plain,
% 2.46/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.46/0.99      inference(global_propositional_subsumption,
% 2.46/0.99                [status(thm)],
% 2.46/0.99                [c_1757,c_1204,c_1210]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_27,negated_conjecture,
% 2.46/0.99      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.46/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.46/0.99      inference(cnf_transformation,[],[f85]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1295,plain,
% 2.46/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.46/0.99      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.46/0.99      inference(light_normalisation,[status(thm)],[c_27,c_389,c_394]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1824,plain,
% 2.46/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 2.46/0.99      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_1821,c_1295]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1981,plain,
% 2.46/0.99      ( k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 2.46/0.99      | k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_1978,c_1824]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3081,plain,
% 2.46/0.99      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.46/0.99      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_2781,c_1981]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1984,plain,
% 2.46/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) = iProver_top ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_1978,c_1204]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3084,plain,
% 2.46/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_2781,c_1984]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1982,plain,
% 2.46/0.99      ( k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_1978,c_1821]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3083,plain,
% 2.46/0.99      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_2781,c_1982]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_25,plain,
% 2.46/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/0.99      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 2.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/0.99      | ~ v1_funct_1(X0) ),
% 2.46/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1175,plain,
% 2.46/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.46/0.99      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 2.46/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.46/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3360,plain,
% 2.46/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.46/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.46/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.46/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.46/0.99      inference(superposition,[status(thm)],[c_3083,c_1175]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_24,plain,
% 2.46/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/0.99      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.46/0.99      | ~ v1_funct_1(X0) ),
% 2.46/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1176,plain,
% 2.46/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.46/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.46/0.99      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 2.46/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3559,plain,
% 2.46/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.46/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.46/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.46/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.46/0.99      inference(superposition,[status(thm)],[c_3083,c_1176]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_4464,plain,
% 2.46/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.46/0.99      inference(global_propositional_subsumption,
% 2.46/0.99                [status(thm)],
% 2.46/0.99                [c_3559,c_39,c_3082,c_3084]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_4473,plain,
% 2.46/0.99      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.46/0.99      | k1_relat_1(sK2) = k1_xboole_0
% 2.46/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 2.46/0.99      inference(superposition,[status(thm)],[c_4464,c_1177]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_4474,plain,
% 2.46/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.46/0.99      inference(superposition,[status(thm)],[c_4464,c_1183]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_6,plain,
% 2.46/0.99      ( ~ v1_funct_1(X0)
% 2.46/0.99      | ~ v2_funct_1(X0)
% 2.46/0.99      | ~ v1_relat_1(X0)
% 2.46/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.46/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_477,plain,
% 2.46/0.99      ( ~ v1_funct_1(X0)
% 2.46/0.99      | ~ v1_relat_1(X0)
% 2.46/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.46/0.99      | sK2 != X0 ),
% 2.46/0.99      inference(resolution_lifted,[status(thm)],[c_6,c_28]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_478,plain,
% 2.46/0.99      ( ~ v1_funct_1(sK2)
% 2.46/0.99      | ~ v1_relat_1(sK2)
% 2.46/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.46/0.99      inference(unflattening,[status(thm)],[c_477]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_480,plain,
% 2.46/0.99      ( ~ v1_relat_1(sK2)
% 2.46/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.46/0.99      inference(global_propositional_subsumption,
% 2.46/0.99                [status(thm)],
% 2.46/0.99                [c_478,c_32]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1167,plain,
% 2.46/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.46/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_480]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_1658,plain,
% 2.46/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.46/0.99      inference(global_propositional_subsumption,
% 2.46/0.99                [status(thm)],
% 2.46/0.99                [c_1167,c_32,c_30,c_478,c_1532,c_1629]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_4476,plain,
% 2.46/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.46/0.99      inference(light_normalisation,[status(thm)],[c_4474,c_1658]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_4752,plain,
% 2.46/0.99      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 2.46/0.99      inference(global_propositional_subsumption,
% 2.46/0.99                [status(thm)],
% 2.46/0.99                [c_3809,c_39,c_30,c_1532,c_1629,c_1894,c_3081,c_3082,
% 2.46/0.99                 c_3084,c_3360,c_4473,c_4476]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_3085,plain,
% 2.46/0.99      ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_2781,c_1199]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_4762,plain,
% 2.46/0.99      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.46/0.99      inference(demodulation,[status(thm)],[c_4752,c_3085]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_0,plain,
% 2.46/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.46/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(c_115,plain,
% 2.46/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.46/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.46/0.99  
% 2.46/0.99  cnf(contradiction,plain,
% 2.46/0.99      ( $false ),
% 2.46/0.99      inference(minisat,[status(thm)],[c_4762,c_115]) ).
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.46/0.99  
% 2.46/0.99  ------                               Statistics
% 2.46/0.99  
% 2.46/0.99  ------ General
% 2.46/0.99  
% 2.46/0.99  abstr_ref_over_cycles:                  0
% 2.46/0.99  abstr_ref_under_cycles:                 0
% 2.46/0.99  gc_basic_clause_elim:                   0
% 2.46/0.99  forced_gc_time:                         0
% 2.46/0.99  parsing_time:                           0.014
% 2.46/0.99  unif_index_cands_time:                  0.
% 2.46/0.99  unif_index_add_time:                    0.
% 2.46/0.99  orderings_time:                         0.
% 2.46/0.99  out_proof_time:                         0.011
% 2.46/0.99  total_time:                             0.172
% 2.46/0.99  num_of_symbols:                         55
% 2.46/0.99  num_of_terms:                           5012
% 2.46/0.99  
% 2.46/0.99  ------ Preprocessing
% 2.46/0.99  
% 2.46/0.99  num_of_splits:                          0
% 2.46/0.99  num_of_split_atoms:                     0
% 2.46/0.99  num_of_reused_defs:                     0
% 2.46/0.99  num_eq_ax_congr_red:                    3
% 2.46/0.99  num_of_sem_filtered_clauses:            1
% 2.46/0.99  num_of_subtypes:                        0
% 2.46/0.99  monotx_restored_types:                  0
% 2.46/0.99  sat_num_of_epr_types:                   0
% 2.46/0.99  sat_num_of_non_cyclic_types:            0
% 2.46/0.99  sat_guarded_non_collapsed_types:        0
% 2.46/0.99  num_pure_diseq_elim:                    0
% 2.46/0.99  simp_replaced_by:                       0
% 2.46/0.99  res_preprocessed:                       157
% 2.46/0.99  prep_upred:                             0
% 2.46/0.99  prep_unflattend:                        10
% 2.46/0.99  smt_new_axioms:                         0
% 2.46/0.99  pred_elim_cands:                        5
% 2.46/0.99  pred_elim:                              5
% 2.46/0.99  pred_elim_cl:                           6
% 2.46/0.99  pred_elim_cycles:                       8
% 2.46/0.99  merged_defs:                            0
% 2.46/0.99  merged_defs_ncl:                        0
% 2.46/0.99  bin_hyper_res:                          0
% 2.46/0.99  prep_cycles:                            4
% 2.46/0.99  pred_elim_time:                         0.005
% 2.46/0.99  splitting_time:                         0.
% 2.46/0.99  sem_filter_time:                        0.
% 2.46/0.99  monotx_time:                            0.001
% 2.46/0.99  subtype_inf_time:                       0.
% 2.46/0.99  
% 2.46/0.99  ------ Problem properties
% 2.46/0.99  
% 2.46/0.99  clauses:                                29
% 2.46/0.99  conjectures:                            5
% 2.46/0.99  epr:                                    2
% 2.46/0.99  horn:                                   24
% 2.46/0.99  ground:                                 11
% 2.46/0.99  unary:                                  9
% 2.46/0.99  binary:                                 5
% 2.46/0.99  lits:                                   74
% 2.46/0.99  lits_eq:                                24
% 2.46/0.99  fd_pure:                                0
% 2.46/0.99  fd_pseudo:                              0
% 2.46/0.99  fd_cond:                                3
% 2.46/0.99  fd_pseudo_cond:                         1
% 2.46/0.99  ac_symbols:                             0
% 2.46/0.99  
% 2.46/0.99  ------ Propositional Solver
% 2.46/0.99  
% 2.46/0.99  prop_solver_calls:                      28
% 2.46/0.99  prop_fast_solver_calls:                 1037
% 2.46/0.99  smt_solver_calls:                       0
% 2.46/0.99  smt_fast_solver_calls:                  0
% 2.46/0.99  prop_num_of_clauses:                    1597
% 2.46/0.99  prop_preprocess_simplified:             5626
% 2.46/0.99  prop_fo_subsumed:                       31
% 2.46/0.99  prop_solver_time:                       0.
% 2.46/0.99  smt_solver_time:                        0.
% 2.46/0.99  smt_fast_solver_time:                   0.
% 2.46/0.99  prop_fast_solver_time:                  0.
% 2.46/0.99  prop_unsat_core_time:                   0.
% 2.46/0.99  
% 2.46/0.99  ------ QBF
% 2.46/0.99  
% 2.46/0.99  qbf_q_res:                              0
% 2.46/0.99  qbf_num_tautologies:                    0
% 2.46/0.99  qbf_prep_cycles:                        0
% 2.46/0.99  
% 2.46/0.99  ------ BMC1
% 2.46/0.99  
% 2.46/0.99  bmc1_current_bound:                     -1
% 2.46/0.99  bmc1_last_solved_bound:                 -1
% 2.46/0.99  bmc1_unsat_core_size:                   -1
% 2.46/0.99  bmc1_unsat_core_parents_size:           -1
% 2.46/0.99  bmc1_merge_next_fun:                    0
% 2.46/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.46/0.99  
% 2.46/0.99  ------ Instantiation
% 2.46/0.99  
% 2.46/0.99  inst_num_of_clauses:                    569
% 2.46/0.99  inst_num_in_passive:                    100
% 2.46/0.99  inst_num_in_active:                     289
% 2.46/0.99  inst_num_in_unprocessed:                180
% 2.46/0.99  inst_num_of_loops:                      300
% 2.46/0.99  inst_num_of_learning_restarts:          0
% 2.46/0.99  inst_num_moves_active_passive:          7
% 2.46/0.99  inst_lit_activity:                      0
% 2.46/0.99  inst_lit_activity_moves:                0
% 2.46/0.99  inst_num_tautologies:                   0
% 2.46/0.99  inst_num_prop_implied:                  0
% 2.46/0.99  inst_num_existing_simplified:           0
% 2.46/0.99  inst_num_eq_res_simplified:             0
% 2.46/0.99  inst_num_child_elim:                    0
% 2.46/0.99  inst_num_of_dismatching_blockings:      80
% 2.46/0.99  inst_num_of_non_proper_insts:           437
% 2.46/0.99  inst_num_of_duplicates:                 0
% 2.46/0.99  inst_inst_num_from_inst_to_res:         0
% 2.46/0.99  inst_dismatching_checking_time:         0.
% 2.46/0.99  
% 2.46/0.99  ------ Resolution
% 2.46/0.99  
% 2.46/0.99  res_num_of_clauses:                     0
% 2.46/0.99  res_num_in_passive:                     0
% 2.46/0.99  res_num_in_active:                      0
% 2.46/0.99  res_num_of_loops:                       161
% 2.46/0.99  res_forward_subset_subsumed:            49
% 2.46/0.99  res_backward_subset_subsumed:           2
% 2.46/0.99  res_forward_subsumed:                   0
% 2.46/0.99  res_backward_subsumed:                  0
% 2.46/0.99  res_forward_subsumption_resolution:     0
% 2.46/0.99  res_backward_subsumption_resolution:    0
% 2.46/0.99  res_clause_to_clause_subsumption:       108
% 2.46/0.99  res_orphan_elimination:                 0
% 2.46/0.99  res_tautology_del:                      48
% 2.46/0.99  res_num_eq_res_simplified:              0
% 2.46/0.99  res_num_sel_changes:                    0
% 2.46/0.99  res_moves_from_active_to_pass:          0
% 2.46/0.99  
% 2.46/0.99  ------ Superposition
% 2.46/0.99  
% 2.46/0.99  sup_time_total:                         0.
% 2.46/0.99  sup_time_generating:                    0.
% 2.46/0.99  sup_time_sim_full:                      0.
% 2.46/0.99  sup_time_sim_immed:                     0.
% 2.46/0.99  
% 2.46/0.99  sup_num_of_clauses:                     45
% 2.46/0.99  sup_num_in_active:                      30
% 2.46/0.99  sup_num_in_passive:                     15
% 2.46/0.99  sup_num_of_loops:                       59
% 2.46/0.99  sup_fw_superposition:                   12
% 2.46/0.99  sup_bw_superposition:                   28
% 2.46/0.99  sup_immediate_simplified:               18
% 2.46/0.99  sup_given_eliminated:                   0
% 2.46/0.99  comparisons_done:                       0
% 2.46/0.99  comparisons_avoided:                    0
% 2.46/0.99  
% 2.46/0.99  ------ Simplifications
% 2.46/0.99  
% 2.46/0.99  
% 2.46/0.99  sim_fw_subset_subsumed:                 5
% 2.46/0.99  sim_bw_subset_subsumed:                 1
% 2.46/0.99  sim_fw_subsumed:                        0
% 2.46/0.99  sim_bw_subsumed:                        0
% 2.46/0.99  sim_fw_subsumption_res:                 1
% 2.46/0.99  sim_bw_subsumption_res:                 0
% 2.46/0.99  sim_tautology_del:                      0
% 2.46/0.99  sim_eq_tautology_del:                   3
% 2.46/0.99  sim_eq_res_simp:                        1
% 2.46/0.99  sim_fw_demodulated:                     2
% 2.46/0.99  sim_bw_demodulated:                     29
% 2.46/0.99  sim_light_normalised:                   17
% 2.46/0.99  sim_joinable_taut:                      0
% 2.46/0.99  sim_joinable_simp:                      0
% 2.46/0.99  sim_ac_normalised:                      0
% 2.46/0.99  sim_smt_subsumption:                    0
% 2.46/0.99  
%------------------------------------------------------------------------------
