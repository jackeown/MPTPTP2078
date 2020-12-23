%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:00 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.35s
% Verified   : 
% Statistics : Number of formulae       :  175 (2093 expanded)
%              Number of clauses        :  106 ( 572 expanded)
%              Number of leaves         :   19 ( 621 expanded)
%              Depth                    :   20
%              Number of atoms          :  611 (15024 expanded)
%              Number of equality atoms :  242 (5106 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

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

fof(f47,plain,(
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

fof(f46,plain,(
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

fof(f45,plain,
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

fof(f48,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f47,f46,f45])).

fof(f81,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f48])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f73,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f78,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f76,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
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

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f63,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f79,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f80,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f48])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f48])).

fof(f84,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f11,axiom,(
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

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f50,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f77,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f52,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1847,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_24,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_33,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_390,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_391,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_390])).

cnf(c_35,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_395,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_35])).

cnf(c_396,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_395])).

cnf(c_1878,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1847,c_391,c_396])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1856,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2300,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1878,c_1856])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1875,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_29,c_391,c_396])).

cnf(c_3096,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2300,c_1875])).

cnf(c_3249,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3096,c_1878])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_5,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_15,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_402,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_5,c_15])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_406,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_402,c_15,c_5,c_4])).

cnf(c_407,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_406])).

cnf(c_522,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_17,c_407])).

cnf(c_526,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_522,c_17,c_407])).

cnf(c_527,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_526])).

cnf(c_1843,plain,
    ( k1_relat_1(X0) = X1
    | k1_xboole_0 = X2
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_527])).

cnf(c_4061,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3249,c_1843])).

cnf(c_32,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_31,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1846,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1872,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1846,c_391,c_396])).

cnf(c_3250,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3096,c_1872])).

cnf(c_3276,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3250])).

cnf(c_4080,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4061])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_28,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_581,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_28])).

cnf(c_582,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_581])).

cnf(c_586,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_582,c_32])).

cnf(c_587,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_586])).

cnf(c_1841,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_587])).

cnf(c_2480,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_1841])).

cnf(c_2538,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2480,c_1872,c_1878])).

cnf(c_27,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1969,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_27,c_391,c_396])).

cnf(c_2541,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2538,c_1969])).

cnf(c_3246,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3096,c_2541])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1857,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2879,plain,
    ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1878,c_1857])).

cnf(c_2880,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK0))
    | v1_xboole_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2879])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_629,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_630,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(unflattening,[status(thm)],[c_629])).

cnf(c_634,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_funct_2(k2_funct_1(sK2),X0,X1)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_630,c_32])).

cnf(c_635,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(renaming,[status(thm)],[c_634])).

cnf(c_1839,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_2383,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_1839])).

cnf(c_2470,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2383,c_1872,c_1878])).

cnf(c_3248,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3096,c_2470])).

cnf(c_1,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1859,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_25,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_34,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_377,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_378,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_377])).

cnf(c_380,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_33])).

cnf(c_1844,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_380])).

cnf(c_1869,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1844,c_391])).

cnf(c_3251,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3096,c_1869])).

cnf(c_3484,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1859,c_3251])).

cnf(c_3485,plain,
    ( ~ v1_xboole_0(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3484])).

cnf(c_1379,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4001,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_struct_0(sK0))
    | k2_struct_0(sK0) != X0 ),
    inference(instantiation,[status(thm)],[c_1379])).

cnf(c_4003,plain,
    ( v1_xboole_0(k2_struct_0(sK0))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_struct_0(sK0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4001])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_653,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_654,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_658,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_654,c_32])).

cnf(c_659,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_658])).

cnf(c_1838,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_2597,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1875,c_1838])).

cnf(c_3018,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2597,c_1872,c_1878])).

cnf(c_3245,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3096,c_3018])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1850,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4351,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3245,c_1850])).

cnf(c_4890,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3246,c_0,c_2880,c_3248,c_3485,c_4003,c_4351])).

cnf(c_3025,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3018,c_1856])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_691,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_2,c_28])).

cnf(c_692,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_691])).

cnf(c_694,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_692,c_32])).

cnf(c_1836,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_694])).

cnf(c_2088,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2139,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1836,c_32,c_30,c_692,c_2088])).

cnf(c_3027,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3025,c_2139])).

cnf(c_4057,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3027,c_3096])).

cnf(c_4892,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4890,c_4057])).

cnf(c_5231,plain,
    ( k2_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4061,c_32,c_3276,c_4080,c_4892])).

cnf(c_5247,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5231,c_3251])).

cnf(c_117,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5247,c_117])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:13:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.35/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.35/0.99  
% 2.35/0.99  ------  iProver source info
% 2.35/0.99  
% 2.35/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.35/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.35/0.99  git: non_committed_changes: false
% 2.35/0.99  git: last_make_outside_of_git: false
% 2.35/0.99  
% 2.35/0.99  ------ 
% 2.35/0.99  
% 2.35/0.99  ------ Input Options
% 2.35/0.99  
% 2.35/0.99  --out_options                           all
% 2.35/0.99  --tptp_safe_out                         true
% 2.35/0.99  --problem_path                          ""
% 2.35/0.99  --include_path                          ""
% 2.35/0.99  --clausifier                            res/vclausify_rel
% 2.35/0.99  --clausifier_options                    --mode clausify
% 2.35/0.99  --stdin                                 false
% 2.35/0.99  --stats_out                             all
% 2.35/0.99  
% 2.35/0.99  ------ General Options
% 2.35/0.99  
% 2.35/0.99  --fof                                   false
% 2.35/0.99  --time_out_real                         305.
% 2.35/0.99  --time_out_virtual                      -1.
% 2.35/0.99  --symbol_type_check                     false
% 2.35/0.99  --clausify_out                          false
% 2.35/0.99  --sig_cnt_out                           false
% 2.35/0.99  --trig_cnt_out                          false
% 2.35/0.99  --trig_cnt_out_tolerance                1.
% 2.35/0.99  --trig_cnt_out_sk_spl                   false
% 2.35/0.99  --abstr_cl_out                          false
% 2.35/0.99  
% 2.35/0.99  ------ Global Options
% 2.35/0.99  
% 2.35/0.99  --schedule                              default
% 2.35/0.99  --add_important_lit                     false
% 2.35/0.99  --prop_solver_per_cl                    1000
% 2.35/0.99  --min_unsat_core                        false
% 2.35/0.99  --soft_assumptions                      false
% 2.35/0.99  --soft_lemma_size                       3
% 2.35/0.99  --prop_impl_unit_size                   0
% 2.35/0.99  --prop_impl_unit                        []
% 2.35/0.99  --share_sel_clauses                     true
% 2.35/0.99  --reset_solvers                         false
% 2.35/0.99  --bc_imp_inh                            [conj_cone]
% 2.35/0.99  --conj_cone_tolerance                   3.
% 2.35/0.99  --extra_neg_conj                        none
% 2.35/0.99  --large_theory_mode                     true
% 2.35/0.99  --prolific_symb_bound                   200
% 2.35/0.99  --lt_threshold                          2000
% 2.35/0.99  --clause_weak_htbl                      true
% 2.35/0.99  --gc_record_bc_elim                     false
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing Options
% 2.35/0.99  
% 2.35/0.99  --preprocessing_flag                    true
% 2.35/0.99  --time_out_prep_mult                    0.1
% 2.35/0.99  --splitting_mode                        input
% 2.35/0.99  --splitting_grd                         true
% 2.35/0.99  --splitting_cvd                         false
% 2.35/0.99  --splitting_cvd_svl                     false
% 2.35/0.99  --splitting_nvd                         32
% 2.35/0.99  --sub_typing                            true
% 2.35/0.99  --prep_gs_sim                           true
% 2.35/0.99  --prep_unflatten                        true
% 2.35/0.99  --prep_res_sim                          true
% 2.35/0.99  --prep_upred                            true
% 2.35/0.99  --prep_sem_filter                       exhaustive
% 2.35/0.99  --prep_sem_filter_out                   false
% 2.35/0.99  --pred_elim                             true
% 2.35/0.99  --res_sim_input                         true
% 2.35/0.99  --eq_ax_congr_red                       true
% 2.35/0.99  --pure_diseq_elim                       true
% 2.35/0.99  --brand_transform                       false
% 2.35/0.99  --non_eq_to_eq                          false
% 2.35/0.99  --prep_def_merge                        true
% 2.35/0.99  --prep_def_merge_prop_impl              false
% 2.35/0.99  --prep_def_merge_mbd                    true
% 2.35/0.99  --prep_def_merge_tr_red                 false
% 2.35/0.99  --prep_def_merge_tr_cl                  false
% 2.35/0.99  --smt_preprocessing                     true
% 2.35/0.99  --smt_ac_axioms                         fast
% 2.35/0.99  --preprocessed_out                      false
% 2.35/0.99  --preprocessed_stats                    false
% 2.35/0.99  
% 2.35/0.99  ------ Abstraction refinement Options
% 2.35/0.99  
% 2.35/0.99  --abstr_ref                             []
% 2.35/0.99  --abstr_ref_prep                        false
% 2.35/0.99  --abstr_ref_until_sat                   false
% 2.35/0.99  --abstr_ref_sig_restrict                funpre
% 2.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.99  --abstr_ref_under                       []
% 2.35/0.99  
% 2.35/0.99  ------ SAT Options
% 2.35/0.99  
% 2.35/0.99  --sat_mode                              false
% 2.35/0.99  --sat_fm_restart_options                ""
% 2.35/0.99  --sat_gr_def                            false
% 2.35/0.99  --sat_epr_types                         true
% 2.35/0.99  --sat_non_cyclic_types                  false
% 2.35/0.99  --sat_finite_models                     false
% 2.35/0.99  --sat_fm_lemmas                         false
% 2.35/0.99  --sat_fm_prep                           false
% 2.35/0.99  --sat_fm_uc_incr                        true
% 2.35/0.99  --sat_out_model                         small
% 2.35/0.99  --sat_out_clauses                       false
% 2.35/0.99  
% 2.35/0.99  ------ QBF Options
% 2.35/0.99  
% 2.35/0.99  --qbf_mode                              false
% 2.35/0.99  --qbf_elim_univ                         false
% 2.35/0.99  --qbf_dom_inst                          none
% 2.35/0.99  --qbf_dom_pre_inst                      false
% 2.35/0.99  --qbf_sk_in                             false
% 2.35/0.99  --qbf_pred_elim                         true
% 2.35/0.99  --qbf_split                             512
% 2.35/0.99  
% 2.35/0.99  ------ BMC1 Options
% 2.35/0.99  
% 2.35/0.99  --bmc1_incremental                      false
% 2.35/0.99  --bmc1_axioms                           reachable_all
% 2.35/0.99  --bmc1_min_bound                        0
% 2.35/0.99  --bmc1_max_bound                        -1
% 2.35/0.99  --bmc1_max_bound_default                -1
% 2.35/0.99  --bmc1_symbol_reachability              true
% 2.35/0.99  --bmc1_property_lemmas                  false
% 2.35/0.99  --bmc1_k_induction                      false
% 2.35/0.99  --bmc1_non_equiv_states                 false
% 2.35/0.99  --bmc1_deadlock                         false
% 2.35/0.99  --bmc1_ucm                              false
% 2.35/0.99  --bmc1_add_unsat_core                   none
% 2.35/0.99  --bmc1_unsat_core_children              false
% 2.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.99  --bmc1_out_stat                         full
% 2.35/0.99  --bmc1_ground_init                      false
% 2.35/0.99  --bmc1_pre_inst_next_state              false
% 2.35/0.99  --bmc1_pre_inst_state                   false
% 2.35/0.99  --bmc1_pre_inst_reach_state             false
% 2.35/0.99  --bmc1_out_unsat_core                   false
% 2.35/0.99  --bmc1_aig_witness_out                  false
% 2.35/0.99  --bmc1_verbose                          false
% 2.35/0.99  --bmc1_dump_clauses_tptp                false
% 2.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.99  --bmc1_dump_file                        -
% 2.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.99  --bmc1_ucm_extend_mode                  1
% 2.35/0.99  --bmc1_ucm_init_mode                    2
% 2.35/0.99  --bmc1_ucm_cone_mode                    none
% 2.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.99  --bmc1_ucm_relax_model                  4
% 2.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.99  --bmc1_ucm_layered_model                none
% 2.35/0.99  --bmc1_ucm_max_lemma_size               10
% 2.35/0.99  
% 2.35/0.99  ------ AIG Options
% 2.35/0.99  
% 2.35/0.99  --aig_mode                              false
% 2.35/0.99  
% 2.35/0.99  ------ Instantiation Options
% 2.35/0.99  
% 2.35/0.99  --instantiation_flag                    true
% 2.35/0.99  --inst_sos_flag                         false
% 2.35/0.99  --inst_sos_phase                        true
% 2.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel_side                     num_symb
% 2.35/0.99  --inst_solver_per_active                1400
% 2.35/0.99  --inst_solver_calls_frac                1.
% 2.35/0.99  --inst_passive_queue_type               priority_queues
% 2.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.99  --inst_passive_queues_freq              [25;2]
% 2.35/0.99  --inst_dismatching                      true
% 2.35/0.99  --inst_eager_unprocessed_to_passive     true
% 2.35/0.99  --inst_prop_sim_given                   true
% 2.35/0.99  --inst_prop_sim_new                     false
% 2.35/0.99  --inst_subs_new                         false
% 2.35/0.99  --inst_eq_res_simp                      false
% 2.35/0.99  --inst_subs_given                       false
% 2.35/0.99  --inst_orphan_elimination               true
% 2.35/0.99  --inst_learning_loop_flag               true
% 2.35/0.99  --inst_learning_start                   3000
% 2.35/0.99  --inst_learning_factor                  2
% 2.35/0.99  --inst_start_prop_sim_after_learn       3
% 2.35/0.99  --inst_sel_renew                        solver
% 2.35/0.99  --inst_lit_activity_flag                true
% 2.35/0.99  --inst_restr_to_given                   false
% 2.35/0.99  --inst_activity_threshold               500
% 2.35/0.99  --inst_out_proof                        true
% 2.35/0.99  
% 2.35/0.99  ------ Resolution Options
% 2.35/0.99  
% 2.35/0.99  --resolution_flag                       true
% 2.35/0.99  --res_lit_sel                           adaptive
% 2.35/0.99  --res_lit_sel_side                      none
% 2.35/0.99  --res_ordering                          kbo
% 2.35/0.99  --res_to_prop_solver                    active
% 2.35/0.99  --res_prop_simpl_new                    false
% 2.35/0.99  --res_prop_simpl_given                  true
% 2.35/0.99  --res_passive_queue_type                priority_queues
% 2.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.99  --res_passive_queues_freq               [15;5]
% 2.35/0.99  --res_forward_subs                      full
% 2.35/0.99  --res_backward_subs                     full
% 2.35/0.99  --res_forward_subs_resolution           true
% 2.35/0.99  --res_backward_subs_resolution          true
% 2.35/0.99  --res_orphan_elimination                true
% 2.35/0.99  --res_time_limit                        2.
% 2.35/0.99  --res_out_proof                         true
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Options
% 2.35/0.99  
% 2.35/0.99  --superposition_flag                    true
% 2.35/0.99  --sup_passive_queue_type                priority_queues
% 2.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.99  --demod_completeness_check              fast
% 2.35/0.99  --demod_use_ground                      true
% 2.35/0.99  --sup_to_prop_solver                    passive
% 2.35/0.99  --sup_prop_simpl_new                    true
% 2.35/0.99  --sup_prop_simpl_given                  true
% 2.35/0.99  --sup_fun_splitting                     false
% 2.35/0.99  --sup_smt_interval                      50000
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Simplification Setup
% 2.35/0.99  
% 2.35/0.99  --sup_indices_passive                   []
% 2.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_full_bw                           [BwDemod]
% 2.35/0.99  --sup_immed_triv                        [TrivRules]
% 2.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_immed_bw_main                     []
% 2.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  
% 2.35/0.99  ------ Combination Options
% 2.35/0.99  
% 2.35/0.99  --comb_res_mult                         3
% 2.35/0.99  --comb_sup_mult                         2
% 2.35/0.99  --comb_inst_mult                        10
% 2.35/0.99  
% 2.35/0.99  ------ Debug Options
% 2.35/0.99  
% 2.35/0.99  --dbg_backtrace                         false
% 2.35/0.99  --dbg_dump_prop_clauses                 false
% 2.35/0.99  --dbg_dump_prop_clauses_file            -
% 2.35/0.99  --dbg_out_stat                          false
% 2.35/0.99  ------ Parsing...
% 2.35/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.35/0.99  ------ Proving...
% 2.35/0.99  ------ Problem Properties 
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  clauses                                 29
% 2.35/0.99  conjectures                             5
% 2.35/0.99  EPR                                     2
% 2.35/0.99  Horn                                    24
% 2.35/0.99  unary                                   8
% 2.35/0.99  binary                                  6
% 2.35/0.99  lits                                    76
% 2.35/0.99  lits eq                                 25
% 2.35/0.99  fd_pure                                 0
% 2.35/0.99  fd_pseudo                               0
% 2.35/0.99  fd_cond                                 3
% 2.35/0.99  fd_pseudo_cond                          1
% 2.35/0.99  AC symbols                              0
% 2.35/0.99  
% 2.35/0.99  ------ Schedule dynamic 5 is on 
% 2.35/0.99  
% 2.35/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  ------ 
% 2.35/0.99  Current options:
% 2.35/0.99  ------ 
% 2.35/0.99  
% 2.35/0.99  ------ Input Options
% 2.35/0.99  
% 2.35/0.99  --out_options                           all
% 2.35/0.99  --tptp_safe_out                         true
% 2.35/0.99  --problem_path                          ""
% 2.35/0.99  --include_path                          ""
% 2.35/0.99  --clausifier                            res/vclausify_rel
% 2.35/0.99  --clausifier_options                    --mode clausify
% 2.35/0.99  --stdin                                 false
% 2.35/0.99  --stats_out                             all
% 2.35/0.99  
% 2.35/0.99  ------ General Options
% 2.35/0.99  
% 2.35/0.99  --fof                                   false
% 2.35/0.99  --time_out_real                         305.
% 2.35/0.99  --time_out_virtual                      -1.
% 2.35/0.99  --symbol_type_check                     false
% 2.35/0.99  --clausify_out                          false
% 2.35/0.99  --sig_cnt_out                           false
% 2.35/0.99  --trig_cnt_out                          false
% 2.35/0.99  --trig_cnt_out_tolerance                1.
% 2.35/0.99  --trig_cnt_out_sk_spl                   false
% 2.35/0.99  --abstr_cl_out                          false
% 2.35/0.99  
% 2.35/0.99  ------ Global Options
% 2.35/0.99  
% 2.35/0.99  --schedule                              default
% 2.35/0.99  --add_important_lit                     false
% 2.35/0.99  --prop_solver_per_cl                    1000
% 2.35/0.99  --min_unsat_core                        false
% 2.35/0.99  --soft_assumptions                      false
% 2.35/0.99  --soft_lemma_size                       3
% 2.35/0.99  --prop_impl_unit_size                   0
% 2.35/0.99  --prop_impl_unit                        []
% 2.35/0.99  --share_sel_clauses                     true
% 2.35/0.99  --reset_solvers                         false
% 2.35/0.99  --bc_imp_inh                            [conj_cone]
% 2.35/0.99  --conj_cone_tolerance                   3.
% 2.35/0.99  --extra_neg_conj                        none
% 2.35/0.99  --large_theory_mode                     true
% 2.35/0.99  --prolific_symb_bound                   200
% 2.35/0.99  --lt_threshold                          2000
% 2.35/0.99  --clause_weak_htbl                      true
% 2.35/0.99  --gc_record_bc_elim                     false
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing Options
% 2.35/0.99  
% 2.35/0.99  --preprocessing_flag                    true
% 2.35/0.99  --time_out_prep_mult                    0.1
% 2.35/0.99  --splitting_mode                        input
% 2.35/0.99  --splitting_grd                         true
% 2.35/0.99  --splitting_cvd                         false
% 2.35/0.99  --splitting_cvd_svl                     false
% 2.35/0.99  --splitting_nvd                         32
% 2.35/0.99  --sub_typing                            true
% 2.35/0.99  --prep_gs_sim                           true
% 2.35/0.99  --prep_unflatten                        true
% 2.35/0.99  --prep_res_sim                          true
% 2.35/0.99  --prep_upred                            true
% 2.35/0.99  --prep_sem_filter                       exhaustive
% 2.35/0.99  --prep_sem_filter_out                   false
% 2.35/0.99  --pred_elim                             true
% 2.35/0.99  --res_sim_input                         true
% 2.35/0.99  --eq_ax_congr_red                       true
% 2.35/0.99  --pure_diseq_elim                       true
% 2.35/0.99  --brand_transform                       false
% 2.35/0.99  --non_eq_to_eq                          false
% 2.35/0.99  --prep_def_merge                        true
% 2.35/0.99  --prep_def_merge_prop_impl              false
% 2.35/0.99  --prep_def_merge_mbd                    true
% 2.35/0.99  --prep_def_merge_tr_red                 false
% 2.35/0.99  --prep_def_merge_tr_cl                  false
% 2.35/0.99  --smt_preprocessing                     true
% 2.35/0.99  --smt_ac_axioms                         fast
% 2.35/0.99  --preprocessed_out                      false
% 2.35/0.99  --preprocessed_stats                    false
% 2.35/0.99  
% 2.35/0.99  ------ Abstraction refinement Options
% 2.35/0.99  
% 2.35/0.99  --abstr_ref                             []
% 2.35/0.99  --abstr_ref_prep                        false
% 2.35/0.99  --abstr_ref_until_sat                   false
% 2.35/0.99  --abstr_ref_sig_restrict                funpre
% 2.35/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.35/0.99  --abstr_ref_under                       []
% 2.35/0.99  
% 2.35/0.99  ------ SAT Options
% 2.35/0.99  
% 2.35/0.99  --sat_mode                              false
% 2.35/0.99  --sat_fm_restart_options                ""
% 2.35/0.99  --sat_gr_def                            false
% 2.35/0.99  --sat_epr_types                         true
% 2.35/0.99  --sat_non_cyclic_types                  false
% 2.35/0.99  --sat_finite_models                     false
% 2.35/0.99  --sat_fm_lemmas                         false
% 2.35/0.99  --sat_fm_prep                           false
% 2.35/0.99  --sat_fm_uc_incr                        true
% 2.35/0.99  --sat_out_model                         small
% 2.35/0.99  --sat_out_clauses                       false
% 2.35/0.99  
% 2.35/0.99  ------ QBF Options
% 2.35/0.99  
% 2.35/0.99  --qbf_mode                              false
% 2.35/0.99  --qbf_elim_univ                         false
% 2.35/0.99  --qbf_dom_inst                          none
% 2.35/0.99  --qbf_dom_pre_inst                      false
% 2.35/0.99  --qbf_sk_in                             false
% 2.35/0.99  --qbf_pred_elim                         true
% 2.35/0.99  --qbf_split                             512
% 2.35/0.99  
% 2.35/0.99  ------ BMC1 Options
% 2.35/0.99  
% 2.35/0.99  --bmc1_incremental                      false
% 2.35/0.99  --bmc1_axioms                           reachable_all
% 2.35/0.99  --bmc1_min_bound                        0
% 2.35/0.99  --bmc1_max_bound                        -1
% 2.35/0.99  --bmc1_max_bound_default                -1
% 2.35/0.99  --bmc1_symbol_reachability              true
% 2.35/0.99  --bmc1_property_lemmas                  false
% 2.35/0.99  --bmc1_k_induction                      false
% 2.35/0.99  --bmc1_non_equiv_states                 false
% 2.35/0.99  --bmc1_deadlock                         false
% 2.35/0.99  --bmc1_ucm                              false
% 2.35/0.99  --bmc1_add_unsat_core                   none
% 2.35/0.99  --bmc1_unsat_core_children              false
% 2.35/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.35/0.99  --bmc1_out_stat                         full
% 2.35/0.99  --bmc1_ground_init                      false
% 2.35/0.99  --bmc1_pre_inst_next_state              false
% 2.35/0.99  --bmc1_pre_inst_state                   false
% 2.35/0.99  --bmc1_pre_inst_reach_state             false
% 2.35/0.99  --bmc1_out_unsat_core                   false
% 2.35/0.99  --bmc1_aig_witness_out                  false
% 2.35/0.99  --bmc1_verbose                          false
% 2.35/0.99  --bmc1_dump_clauses_tptp                false
% 2.35/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.35/0.99  --bmc1_dump_file                        -
% 2.35/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.35/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.35/0.99  --bmc1_ucm_extend_mode                  1
% 2.35/0.99  --bmc1_ucm_init_mode                    2
% 2.35/0.99  --bmc1_ucm_cone_mode                    none
% 2.35/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.35/0.99  --bmc1_ucm_relax_model                  4
% 2.35/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.35/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.35/0.99  --bmc1_ucm_layered_model                none
% 2.35/0.99  --bmc1_ucm_max_lemma_size               10
% 2.35/0.99  
% 2.35/0.99  ------ AIG Options
% 2.35/0.99  
% 2.35/0.99  --aig_mode                              false
% 2.35/0.99  
% 2.35/0.99  ------ Instantiation Options
% 2.35/0.99  
% 2.35/0.99  --instantiation_flag                    true
% 2.35/0.99  --inst_sos_flag                         false
% 2.35/0.99  --inst_sos_phase                        true
% 2.35/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.35/0.99  --inst_lit_sel_side                     none
% 2.35/0.99  --inst_solver_per_active                1400
% 2.35/0.99  --inst_solver_calls_frac                1.
% 2.35/0.99  --inst_passive_queue_type               priority_queues
% 2.35/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.35/0.99  --inst_passive_queues_freq              [25;2]
% 2.35/0.99  --inst_dismatching                      true
% 2.35/0.99  --inst_eager_unprocessed_to_passive     true
% 2.35/0.99  --inst_prop_sim_given                   true
% 2.35/0.99  --inst_prop_sim_new                     false
% 2.35/0.99  --inst_subs_new                         false
% 2.35/0.99  --inst_eq_res_simp                      false
% 2.35/0.99  --inst_subs_given                       false
% 2.35/0.99  --inst_orphan_elimination               true
% 2.35/0.99  --inst_learning_loop_flag               true
% 2.35/0.99  --inst_learning_start                   3000
% 2.35/0.99  --inst_learning_factor                  2
% 2.35/0.99  --inst_start_prop_sim_after_learn       3
% 2.35/0.99  --inst_sel_renew                        solver
% 2.35/0.99  --inst_lit_activity_flag                true
% 2.35/0.99  --inst_restr_to_given                   false
% 2.35/0.99  --inst_activity_threshold               500
% 2.35/0.99  --inst_out_proof                        true
% 2.35/0.99  
% 2.35/0.99  ------ Resolution Options
% 2.35/0.99  
% 2.35/0.99  --resolution_flag                       false
% 2.35/0.99  --res_lit_sel                           adaptive
% 2.35/0.99  --res_lit_sel_side                      none
% 2.35/0.99  --res_ordering                          kbo
% 2.35/0.99  --res_to_prop_solver                    active
% 2.35/0.99  --res_prop_simpl_new                    false
% 2.35/0.99  --res_prop_simpl_given                  true
% 2.35/0.99  --res_passive_queue_type                priority_queues
% 2.35/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.35/0.99  --res_passive_queues_freq               [15;5]
% 2.35/0.99  --res_forward_subs                      full
% 2.35/0.99  --res_backward_subs                     full
% 2.35/0.99  --res_forward_subs_resolution           true
% 2.35/0.99  --res_backward_subs_resolution          true
% 2.35/0.99  --res_orphan_elimination                true
% 2.35/0.99  --res_time_limit                        2.
% 2.35/0.99  --res_out_proof                         true
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Options
% 2.35/0.99  
% 2.35/0.99  --superposition_flag                    true
% 2.35/0.99  --sup_passive_queue_type                priority_queues
% 2.35/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.35/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.35/0.99  --demod_completeness_check              fast
% 2.35/0.99  --demod_use_ground                      true
% 2.35/0.99  --sup_to_prop_solver                    passive
% 2.35/0.99  --sup_prop_simpl_new                    true
% 2.35/0.99  --sup_prop_simpl_given                  true
% 2.35/0.99  --sup_fun_splitting                     false
% 2.35/0.99  --sup_smt_interval                      50000
% 2.35/0.99  
% 2.35/0.99  ------ Superposition Simplification Setup
% 2.35/0.99  
% 2.35/0.99  --sup_indices_passive                   []
% 2.35/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.35/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.35/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_full_bw                           [BwDemod]
% 2.35/0.99  --sup_immed_triv                        [TrivRules]
% 2.35/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.35/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_immed_bw_main                     []
% 2.35/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.35/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.35/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.35/0.99  
% 2.35/0.99  ------ Combination Options
% 2.35/0.99  
% 2.35/0.99  --comb_res_mult                         3
% 2.35/0.99  --comb_sup_mult                         2
% 2.35/0.99  --comb_inst_mult                        10
% 2.35/0.99  
% 2.35/0.99  ------ Debug Options
% 2.35/0.99  
% 2.35/0.99  --dbg_backtrace                         false
% 2.35/0.99  --dbg_dump_prop_clauses                 false
% 2.35/0.99  --dbg_dump_prop_clauses_file            -
% 2.35/0.99  --dbg_out_stat                          false
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  ------ Proving...
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  % SZS status Theorem for theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  fof(f16,conjecture,(
% 2.35/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f17,negated_conjecture,(
% 2.35/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.35/0.99    inference(negated_conjecture,[],[f16])).
% 2.35/0.99  
% 2.35/0.99  fof(f41,plain,(
% 2.35/0.99    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.35/0.99    inference(ennf_transformation,[],[f17])).
% 2.35/0.99  
% 2.35/0.99  fof(f42,plain,(
% 2.35/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.35/0.99    inference(flattening,[],[f41])).
% 2.35/0.99  
% 2.35/0.99  fof(f47,plain,(
% 2.35/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.35/0.99    introduced(choice_axiom,[])).
% 2.35/0.99  
% 2.35/0.99  fof(f46,plain,(
% 2.35/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.35/0.99    introduced(choice_axiom,[])).
% 2.35/0.99  
% 2.35/0.99  fof(f45,plain,(
% 2.35/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.35/0.99    introduced(choice_axiom,[])).
% 2.35/0.99  
% 2.35/0.99  fof(f48,plain,(
% 2.35/0.99    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.35/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f47,f46,f45])).
% 2.35/0.99  
% 2.35/0.99  fof(f81,plain,(
% 2.35/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.35/0.99    inference(cnf_transformation,[],[f48])).
% 2.35/0.99  
% 2.35/0.99  fof(f13,axiom,(
% 2.35/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f36,plain,(
% 2.35/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.35/0.99    inference(ennf_transformation,[],[f13])).
% 2.35/0.99  
% 2.35/0.99  fof(f73,plain,(
% 2.35/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f36])).
% 2.35/0.99  
% 2.35/0.99  fof(f78,plain,(
% 2.35/0.99    l1_struct_0(sK1)),
% 2.35/0.99    inference(cnf_transformation,[],[f48])).
% 2.35/0.99  
% 2.35/0.99  fof(f76,plain,(
% 2.35/0.99    l1_struct_0(sK0)),
% 2.35/0.99    inference(cnf_transformation,[],[f48])).
% 2.35/0.99  
% 2.35/0.99  fof(f7,axiom,(
% 2.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f25,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.99    inference(ennf_transformation,[],[f7])).
% 2.35/0.99  
% 2.35/0.99  fof(f56,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f25])).
% 2.35/0.99  
% 2.35/0.99  fof(f82,plain,(
% 2.35/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.35/0.99    inference(cnf_transformation,[],[f48])).
% 2.35/0.99  
% 2.35/0.99  fof(f10,axiom,(
% 2.35/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f30,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.35/0.99    inference(ennf_transformation,[],[f10])).
% 2.35/0.99  
% 2.35/0.99  fof(f31,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.35/0.99    inference(flattening,[],[f30])).
% 2.35/0.99  
% 2.35/0.99  fof(f65,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f31])).
% 2.35/0.99  
% 2.35/0.99  fof(f5,axiom,(
% 2.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f18,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.35/0.99    inference(pure_predicate_removal,[],[f5])).
% 2.35/0.99  
% 2.35/0.99  fof(f23,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.99    inference(ennf_transformation,[],[f18])).
% 2.35/0.99  
% 2.35/0.99  fof(f54,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f23])).
% 2.35/0.99  
% 2.35/0.99  fof(f9,axiom,(
% 2.35/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f28,plain,(
% 2.35/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.35/0.99    inference(ennf_transformation,[],[f9])).
% 2.35/0.99  
% 2.35/0.99  fof(f29,plain,(
% 2.35/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.35/0.99    inference(flattening,[],[f28])).
% 2.35/0.99  
% 2.35/0.99  fof(f44,plain,(
% 2.35/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.35/0.99    inference(nnf_transformation,[],[f29])).
% 2.35/0.99  
% 2.35/0.99  fof(f63,plain,(
% 2.35/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f44])).
% 2.35/0.99  
% 2.35/0.99  fof(f4,axiom,(
% 2.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f22,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.99    inference(ennf_transformation,[],[f4])).
% 2.35/0.99  
% 2.35/0.99  fof(f53,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f22])).
% 2.35/0.99  
% 2.35/0.99  fof(f79,plain,(
% 2.35/0.99    v1_funct_1(sK2)),
% 2.35/0.99    inference(cnf_transformation,[],[f48])).
% 2.35/0.99  
% 2.35/0.99  fof(f80,plain,(
% 2.35/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.35/0.99    inference(cnf_transformation,[],[f48])).
% 2.35/0.99  
% 2.35/0.99  fof(f15,axiom,(
% 2.35/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f39,plain,(
% 2.35/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.35/0.99    inference(ennf_transformation,[],[f15])).
% 2.35/0.99  
% 2.35/0.99  fof(f40,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.35/0.99    inference(flattening,[],[f39])).
% 2.35/0.99  
% 2.35/0.99  fof(f75,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f40])).
% 2.35/0.99  
% 2.35/0.99  fof(f83,plain,(
% 2.35/0.99    v2_funct_1(sK2)),
% 2.35/0.99    inference(cnf_transformation,[],[f48])).
% 2.35/0.99  
% 2.35/0.99  fof(f84,plain,(
% 2.35/0.99    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.35/0.99    inference(cnf_transformation,[],[f48])).
% 2.35/0.99  
% 2.35/0.99  fof(f1,axiom,(
% 2.35/0.99    v1_xboole_0(k1_xboole_0)),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f49,plain,(
% 2.35/0.99    v1_xboole_0(k1_xboole_0)),
% 2.35/0.99    inference(cnf_transformation,[],[f1])).
% 2.35/0.99  
% 2.35/0.99  fof(f6,axiom,(
% 2.35/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f24,plain,(
% 2.35/0.99    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.35/0.99    inference(ennf_transformation,[],[f6])).
% 2.35/0.99  
% 2.35/0.99  fof(f55,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f24])).
% 2.35/0.99  
% 2.35/0.99  fof(f11,axiom,(
% 2.35/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f32,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.35/0.99    inference(ennf_transformation,[],[f11])).
% 2.35/0.99  
% 2.35/0.99  fof(f33,plain,(
% 2.35/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.35/0.99    inference(flattening,[],[f32])).
% 2.35/0.99  
% 2.35/0.99  fof(f68,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f33])).
% 2.35/0.99  
% 2.35/0.99  fof(f2,axiom,(
% 2.35/0.99    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f19,plain,(
% 2.35/0.99    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 2.35/0.99    inference(ennf_transformation,[],[f2])).
% 2.35/0.99  
% 2.35/0.99  fof(f50,plain,(
% 2.35/0.99    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f19])).
% 2.35/0.99  
% 2.35/0.99  fof(f14,axiom,(
% 2.35/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f37,plain,(
% 2.35/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.35/0.99    inference(ennf_transformation,[],[f14])).
% 2.35/0.99  
% 2.35/0.99  fof(f38,plain,(
% 2.35/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.35/0.99    inference(flattening,[],[f37])).
% 2.35/0.99  
% 2.35/0.99  fof(f74,plain,(
% 2.35/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f38])).
% 2.35/0.99  
% 2.35/0.99  fof(f77,plain,(
% 2.35/0.99    ~v2_struct_0(sK1)),
% 2.35/0.99    inference(cnf_transformation,[],[f48])).
% 2.35/0.99  
% 2.35/0.99  fof(f69,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f33])).
% 2.35/0.99  
% 2.35/0.99  fof(f8,axiom,(
% 2.35/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f26,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.99    inference(ennf_transformation,[],[f8])).
% 2.35/0.99  
% 2.35/0.99  fof(f27,plain,(
% 2.35/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.99    inference(flattening,[],[f26])).
% 2.35/0.99  
% 2.35/0.99  fof(f43,plain,(
% 2.35/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.35/0.99    inference(nnf_transformation,[],[f27])).
% 2.35/0.99  
% 2.35/0.99  fof(f57,plain,(
% 2.35/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.35/0.99    inference(cnf_transformation,[],[f43])).
% 2.35/0.99  
% 2.35/0.99  fof(f3,axiom,(
% 2.35/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.35/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.35/0.99  
% 2.35/0.99  fof(f20,plain,(
% 2.35/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.35/0.99    inference(ennf_transformation,[],[f3])).
% 2.35/0.99  
% 2.35/0.99  fof(f21,plain,(
% 2.35/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.35/0.99    inference(flattening,[],[f20])).
% 2.35/0.99  
% 2.35/0.99  fof(f52,plain,(
% 2.35/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.35/0.99    inference(cnf_transformation,[],[f21])).
% 2.35/0.99  
% 2.35/0.99  cnf(c_30,negated_conjecture,
% 2.35/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.35/0.99      inference(cnf_transformation,[],[f81]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1847,plain,
% 2.35/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_24,plain,
% 2.35/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_33,negated_conjecture,
% 2.35/0.99      ( l1_struct_0(sK1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_390,plain,
% 2.35/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_391,plain,
% 2.35/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.35/0.99      inference(unflattening,[status(thm)],[c_390]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_35,negated_conjecture,
% 2.35/0.99      ( l1_struct_0(sK0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_395,plain,
% 2.35/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_24,c_35]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_396,plain,
% 2.35/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.35/0.99      inference(unflattening,[status(thm)],[c_395]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1878,plain,
% 2.35/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_1847,c_391,c_396]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_7,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1856,plain,
% 2.35/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.35/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2300,plain,
% 2.35/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1878,c_1856]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_29,negated_conjecture,
% 2.35/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f82]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1875,plain,
% 2.35/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_29,c_391,c_396]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3096,plain,
% 2.35/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_2300,c_1875]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3249,plain,
% 2.35/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_3096,c_1878]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_17,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | v1_partfun1(X0,X1)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | k1_xboole_0 = X2 ),
% 2.35/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_5,plain,
% 2.35/0.99      ( v4_relat_1(X0,X1)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.35/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_15,plain,
% 2.35/0.99      ( ~ v1_partfun1(X0,X1)
% 2.35/0.99      | ~ v4_relat_1(X0,X1)
% 2.35/0.99      | ~ v1_relat_1(X0)
% 2.35/0.99      | k1_relat_1(X0) = X1 ),
% 2.35/0.99      inference(cnf_transformation,[],[f63]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_402,plain,
% 2.35/0.99      ( ~ v1_partfun1(X0,X1)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_relat_1(X0)
% 2.35/0.99      | k1_relat_1(X0) = X1 ),
% 2.35/0.99      inference(resolution,[status(thm)],[c_5,c_15]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | v1_relat_1(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_406,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_partfun1(X0,X1)
% 2.35/0.99      | k1_relat_1(X0) = X1 ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_402,c_15,c_5,c_4]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_407,plain,
% 2.35/0.99      ( ~ v1_partfun1(X0,X1)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | k1_relat_1(X0) = X1 ),
% 2.35/0.99      inference(renaming,[status(thm)],[c_406]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_522,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | k1_relat_1(X0) = X1
% 2.35/0.99      | k1_xboole_0 = X2 ),
% 2.35/0.99      inference(resolution,[status(thm)],[c_17,c_407]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_526,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | k1_relat_1(X0) = X1
% 2.35/0.99      | k1_xboole_0 = X2 ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_522,c_17,c_407]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_527,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | k1_relat_1(X0) = X1
% 2.35/0.99      | k1_xboole_0 = X2 ),
% 2.35/0.99      inference(renaming,[status(thm)],[c_526]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1843,plain,
% 2.35/0.99      ( k1_relat_1(X0) = X1
% 2.35/0.99      | k1_xboole_0 = X2
% 2.35/0.99      | v1_funct_2(X0,X1,X2) != iProver_top
% 2.35/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.35/0.99      | v1_funct_1(X0) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_527]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4061,plain,
% 2.35/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.35/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 2.35/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.35/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_3249,c_1843]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_32,negated_conjecture,
% 2.35/0.99      ( v1_funct_1(sK2) ),
% 2.35/0.99      inference(cnf_transformation,[],[f79]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_31,negated_conjecture,
% 2.35/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.35/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1846,plain,
% 2.35/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1872,plain,
% 2.35/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_1846,c_391,c_396]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3250,plain,
% 2.35/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_3096,c_1872]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3276,plain,
% 2.35/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
% 2.35/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3250]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4080,plain,
% 2.35/0.99      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
% 2.35/0.99      | ~ v1_funct_1(sK2)
% 2.35/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.35/0.99      | k2_relat_1(sK2) = k1_xboole_0 ),
% 2.35/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_4061]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_26,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | ~ v2_funct_1(X0)
% 2.35/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.35/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.35/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_28,negated_conjecture,
% 2.35/0.99      ( v2_funct_1(sK2) ),
% 2.35/0.99      inference(cnf_transformation,[],[f83]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_581,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.35/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.35/0.99      | sK2 != X0 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_26,c_28]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_582,plain,
% 2.35/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.35/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.35/0.99      | ~ v1_funct_1(sK2)
% 2.35/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.35/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.35/0.99      inference(unflattening,[status(thm)],[c_581]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_586,plain,
% 2.35/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.35/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.35/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.35/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_582,c_32]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_587,plain,
% 2.35/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.35/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.35/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.35/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.35/0.99      inference(renaming,[status(thm)],[c_586]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1841,plain,
% 2.35/0.99      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.35/0.99      | k2_relset_1(X0,X1,sK2) != X1
% 2.35/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.35/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_587]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2480,plain,
% 2.35/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.35/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.35/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1875,c_1841]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2538,plain,
% 2.35/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_2480,c_1872,c_1878]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_27,negated_conjecture,
% 2.35/0.99      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.35/0.99      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f84]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1969,plain,
% 2.35/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.35/0.99      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_27,c_391,c_396]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2541,plain,
% 2.35/0.99      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 2.35/0.99      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_2538,c_1969]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3246,plain,
% 2.35/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.35/0.99      | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_3096,c_2541]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_0,plain,
% 2.35/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_6,plain,
% 2.35/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_xboole_0(X1)
% 2.35/0.99      | v1_xboole_0(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1857,plain,
% 2.35/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.35/0.99      | v1_xboole_0(X1) != iProver_top
% 2.35/0.99      | v1_xboole_0(X0) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2879,plain,
% 2.35/0.99      ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top
% 2.35/0.99      | v1_xboole_0(sK2) = iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1878,c_1857]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2880,plain,
% 2.35/0.99      ( ~ v1_xboole_0(k2_struct_0(sK0)) | v1_xboole_0(sK2) ),
% 2.35/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_2879]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_19,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | ~ v2_funct_1(X0)
% 2.35/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.35/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_629,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.35/0.99      | sK2 != X0 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_630,plain,
% 2.35/0.99      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.35/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 2.35/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.35/0.99      | ~ v1_funct_1(sK2)
% 2.35/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.35/0.99      inference(unflattening,[status(thm)],[c_629]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_634,plain,
% 2.35/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.35/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 2.35/0.99      | v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.35/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_630,c_32]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_635,plain,
% 2.35/0.99      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 2.35/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 2.35/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.35/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 2.35/0.99      inference(renaming,[status(thm)],[c_634]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1839,plain,
% 2.35/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 2.35/0.99      | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
% 2.35/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.35/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2383,plain,
% 2.35/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.35/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.35/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1875,c_1839]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2470,plain,
% 2.35/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_2383,c_1872,c_1878]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3248,plain,
% 2.35/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_3096,c_2470]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1,plain,
% 2.35/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0)) ),
% 2.35/0.99      inference(cnf_transformation,[],[f50]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1859,plain,
% 2.35/0.99      ( v1_xboole_0(X0) != iProver_top
% 2.35/0.99      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_25,plain,
% 2.35/0.99      ( v2_struct_0(X0)
% 2.35/0.99      | ~ l1_struct_0(X0)
% 2.35/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.35/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_34,negated_conjecture,
% 2.35/0.99      ( ~ v2_struct_0(sK1) ),
% 2.35/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_377,plain,
% 2.35/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_378,plain,
% 2.35/0.99      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.35/0.99      inference(unflattening,[status(thm)],[c_377]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_380,plain,
% 2.35/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_378,c_33]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1844,plain,
% 2.35/0.99      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_380]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1869,plain,
% 2.35/0.99      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_1844,c_391]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3251,plain,
% 2.35/0.99      ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_3096,c_1869]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3484,plain,
% 2.35/0.99      ( v1_xboole_0(sK2) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1859,c_3251]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3485,plain,
% 2.35/0.99      ( ~ v1_xboole_0(sK2) ),
% 2.35/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_3484]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1379,plain,
% 2.35/0.99      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.35/0.99      theory(equality) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4001,plain,
% 2.35/0.99      ( ~ v1_xboole_0(X0)
% 2.35/0.99      | v1_xboole_0(k2_struct_0(sK0))
% 2.35/0.99      | k2_struct_0(sK0) != X0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_1379]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4003,plain,
% 2.35/0.99      ( v1_xboole_0(k2_struct_0(sK0))
% 2.35/0.99      | ~ v1_xboole_0(k1_xboole_0)
% 2.35/0.99      | k2_struct_0(sK0) != k1_xboole_0 ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_4001]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_18,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | ~ v2_funct_1(X0)
% 2.35/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.35/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_653,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | k2_relset_1(X1,X2,X0) != X2
% 2.35/0.99      | sK2 != X0 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_654,plain,
% 2.35/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.35/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.35/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.35/0.99      | ~ v1_funct_1(sK2)
% 2.35/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.35/0.99      inference(unflattening,[status(thm)],[c_653]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_658,plain,
% 2.35/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.35/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.35/0.99      | ~ v1_funct_2(sK2,X0,X1)
% 2.35/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_654,c_32]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_659,plain,
% 2.35/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 2.35/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.35/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.35/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.35/0.99      inference(renaming,[status(thm)],[c_658]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1838,plain,
% 2.35/0.99      ( k2_relset_1(X0,X1,sK2) != X1
% 2.35/0.99      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.35/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 2.35/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2597,plain,
% 2.35/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.35/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.35/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_1875,c_1838]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3018,plain,
% 2.35/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_2597,c_1872,c_1878]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3245,plain,
% 2.35/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_3096,c_3018]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_13,plain,
% 2.35/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.35/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.35/0.99      | k1_relset_1(X1,X2,X0) = X1
% 2.35/0.99      | k1_xboole_0 = X2 ),
% 2.35/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1850,plain,
% 2.35/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 2.35/0.99      | k1_xboole_0 = X1
% 2.35/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.35/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4351,plain,
% 2.35/0.99      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.35/0.99      | k2_struct_0(sK0) = k1_xboole_0
% 2.35/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_3245,c_1850]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4890,plain,
% 2.35/0.99      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_3246,c_0,c_2880,c_3248,c_3485,c_4003,c_4351]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3025,plain,
% 2.35/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.35/0.99      inference(superposition,[status(thm)],[c_3018,c_1856]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2,plain,
% 2.35/0.99      ( ~ v1_relat_1(X0)
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | ~ v2_funct_1(X0)
% 2.35/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.35/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_691,plain,
% 2.35/0.99      ( ~ v1_relat_1(X0)
% 2.35/0.99      | ~ v1_funct_1(X0)
% 2.35/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.35/0.99      | sK2 != X0 ),
% 2.35/0.99      inference(resolution_lifted,[status(thm)],[c_2,c_28]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_692,plain,
% 2.35/0.99      ( ~ v1_relat_1(sK2)
% 2.35/0.99      | ~ v1_funct_1(sK2)
% 2.35/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.35/0.99      inference(unflattening,[status(thm)],[c_691]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_694,plain,
% 2.35/0.99      ( ~ v1_relat_1(sK2)
% 2.35/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_692,c_32]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_1836,plain,
% 2.35/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.35/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_694]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2088,plain,
% 2.35/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.35/0.99      | v1_relat_1(sK2) ),
% 2.35/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_2139,plain,
% 2.35/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_1836,c_32,c_30,c_692,c_2088]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_3027,plain,
% 2.35/0.99      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_3025,c_2139]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4057,plain,
% 2.35/0.99      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_3027,c_3096]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_4892,plain,
% 2.35/0.99      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 2.35/0.99      inference(light_normalisation,[status(thm)],[c_4890,c_4057]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_5231,plain,
% 2.35/0.99      ( k2_relat_1(sK2) = k1_xboole_0 ),
% 2.35/0.99      inference(global_propositional_subsumption,
% 2.35/0.99                [status(thm)],
% 2.35/0.99                [c_4061,c_32,c_3276,c_4080,c_4892]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_5247,plain,
% 2.35/0.99      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.35/0.99      inference(demodulation,[status(thm)],[c_5231,c_3251]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(c_117,plain,
% 2.35/0.99      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.35/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.35/0.99  
% 2.35/0.99  cnf(contradiction,plain,
% 2.35/0.99      ( $false ),
% 2.35/0.99      inference(minisat,[status(thm)],[c_5247,c_117]) ).
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.35/0.99  
% 2.35/0.99  ------                               Statistics
% 2.35/0.99  
% 2.35/0.99  ------ General
% 2.35/0.99  
% 2.35/0.99  abstr_ref_over_cycles:                  0
% 2.35/0.99  abstr_ref_under_cycles:                 0
% 2.35/0.99  gc_basic_clause_elim:                   0
% 2.35/0.99  forced_gc_time:                         0
% 2.35/0.99  parsing_time:                           0.011
% 2.35/0.99  unif_index_cands_time:                  0.
% 2.35/0.99  unif_index_add_time:                    0.
% 2.35/0.99  orderings_time:                         0.
% 2.35/0.99  out_proof_time:                         0.01
% 2.35/0.99  total_time:                             0.167
% 2.35/0.99  num_of_symbols:                         55
% 2.35/0.99  num_of_terms:                           4078
% 2.35/0.99  
% 2.35/0.99  ------ Preprocessing
% 2.35/0.99  
% 2.35/0.99  num_of_splits:                          0
% 2.35/0.99  num_of_split_atoms:                     0
% 2.35/0.99  num_of_reused_defs:                     0
% 2.35/0.99  num_eq_ax_congr_red:                    4
% 2.35/0.99  num_of_sem_filtered_clauses:            1
% 2.35/0.99  num_of_subtypes:                        0
% 2.35/0.99  monotx_restored_types:                  0
% 2.35/0.99  sat_num_of_epr_types:                   0
% 2.35/0.99  sat_num_of_non_cyclic_types:            0
% 2.35/0.99  sat_guarded_non_collapsed_types:        0
% 2.35/0.99  num_pure_diseq_elim:                    0
% 2.35/0.99  simp_replaced_by:                       0
% 2.35/0.99  res_preprocessed:                       157
% 2.35/0.99  prep_upred:                             0
% 2.35/0.99  prep_unflattend:                        35
% 2.35/0.99  smt_new_axioms:                         0
% 2.35/0.99  pred_elim_cands:                        5
% 2.35/0.99  pred_elim:                              5
% 2.35/0.99  pred_elim_cl:                           6
% 2.35/0.99  pred_elim_cycles:                       10
% 2.35/0.99  merged_defs:                            0
% 2.35/0.99  merged_defs_ncl:                        0
% 2.35/0.99  bin_hyper_res:                          0
% 2.35/0.99  prep_cycles:                            4
% 2.35/0.99  pred_elim_time:                         0.016
% 2.35/0.99  splitting_time:                         0.
% 2.35/0.99  sem_filter_time:                        0.
% 2.35/0.99  monotx_time:                            0.001
% 2.35/0.99  subtype_inf_time:                       0.
% 2.35/0.99  
% 2.35/0.99  ------ Problem properties
% 2.35/0.99  
% 2.35/0.99  clauses:                                29
% 2.35/0.99  conjectures:                            5
% 2.35/0.99  epr:                                    2
% 2.35/0.99  horn:                                   24
% 2.35/0.99  ground:                                 11
% 2.35/0.99  unary:                                  8
% 2.35/0.99  binary:                                 6
% 2.35/0.99  lits:                                   76
% 2.35/0.99  lits_eq:                                25
% 2.35/0.99  fd_pure:                                0
% 2.35/0.99  fd_pseudo:                              0
% 2.35/0.99  fd_cond:                                3
% 2.35/0.99  fd_pseudo_cond:                         1
% 2.35/0.99  ac_symbols:                             0
% 2.35/0.99  
% 2.35/0.99  ------ Propositional Solver
% 2.35/0.99  
% 2.35/0.99  prop_solver_calls:                      28
% 2.35/0.99  prop_fast_solver_calls:                 1193
% 2.35/0.99  smt_solver_calls:                       0
% 2.35/0.99  smt_fast_solver_calls:                  0
% 2.35/0.99  prop_num_of_clauses:                    1519
% 2.35/0.99  prop_preprocess_simplified:             5664
% 2.35/0.99  prop_fo_subsumed:                       34
% 2.35/0.99  prop_solver_time:                       0.
% 2.35/0.99  smt_solver_time:                        0.
% 2.35/0.99  smt_fast_solver_time:                   0.
% 2.35/0.99  prop_fast_solver_time:                  0.
% 2.35/0.99  prop_unsat_core_time:                   0.
% 2.35/0.99  
% 2.35/0.99  ------ QBF
% 2.35/0.99  
% 2.35/0.99  qbf_q_res:                              0
% 2.35/0.99  qbf_num_tautologies:                    0
% 2.35/0.99  qbf_prep_cycles:                        0
% 2.35/0.99  
% 2.35/0.99  ------ BMC1
% 2.35/0.99  
% 2.35/0.99  bmc1_current_bound:                     -1
% 2.35/0.99  bmc1_last_solved_bound:                 -1
% 2.35/0.99  bmc1_unsat_core_size:                   -1
% 2.35/0.99  bmc1_unsat_core_parents_size:           -1
% 2.35/0.99  bmc1_merge_next_fun:                    0
% 2.35/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.35/0.99  
% 2.35/0.99  ------ Instantiation
% 2.35/0.99  
% 2.35/0.99  inst_num_of_clauses:                    547
% 2.35/0.99  inst_num_in_passive:                    105
% 2.35/0.99  inst_num_in_active:                     280
% 2.35/0.99  inst_num_in_unprocessed:                162
% 2.35/0.99  inst_num_of_loops:                      300
% 2.35/0.99  inst_num_of_learning_restarts:          0
% 2.35/0.99  inst_num_moves_active_passive:          16
% 2.35/0.99  inst_lit_activity:                      0
% 2.35/0.99  inst_lit_activity_moves:                0
% 2.35/0.99  inst_num_tautologies:                   0
% 2.35/0.99  inst_num_prop_implied:                  0
% 2.35/0.99  inst_num_existing_simplified:           0
% 2.35/0.99  inst_num_eq_res_simplified:             0
% 2.35/0.99  inst_num_child_elim:                    0
% 2.35/0.99  inst_num_of_dismatching_blockings:      35
% 2.35/0.99  inst_num_of_non_proper_insts:           413
% 2.35/0.99  inst_num_of_duplicates:                 0
% 2.35/0.99  inst_inst_num_from_inst_to_res:         0
% 2.35/0.99  inst_dismatching_checking_time:         0.
% 2.35/0.99  
% 2.35/0.99  ------ Resolution
% 2.35/0.99  
% 2.35/0.99  res_num_of_clauses:                     0
% 2.35/0.99  res_num_in_passive:                     0
% 2.35/0.99  res_num_in_active:                      0
% 2.35/0.99  res_num_of_loops:                       161
% 2.35/0.99  res_forward_subset_subsumed:            57
% 2.35/0.99  res_backward_subset_subsumed:           2
% 2.35/0.99  res_forward_subsumed:                   0
% 2.35/0.99  res_backward_subsumed:                  0
% 2.35/0.99  res_forward_subsumption_resolution:     1
% 2.35/0.99  res_backward_subsumption_resolution:    0
% 2.35/0.99  res_clause_to_clause_subsumption:       127
% 2.35/0.99  res_orphan_elimination:                 0
% 2.35/0.99  res_tautology_del:                      47
% 2.35/0.99  res_num_eq_res_simplified:              0
% 2.35/0.99  res_num_sel_changes:                    0
% 2.35/0.99  res_moves_from_active_to_pass:          0
% 2.35/0.99  
% 2.35/0.99  ------ Superposition
% 2.35/0.99  
% 2.35/0.99  sup_time_total:                         0.
% 2.35/0.99  sup_time_generating:                    0.
% 2.35/0.99  sup_time_sim_full:                      0.
% 2.35/0.99  sup_time_sim_immed:                     0.
% 2.35/0.99  
% 2.35/0.99  sup_num_of_clauses:                     48
% 2.35/0.99  sup_num_in_active:                      30
% 2.35/0.99  sup_num_in_passive:                     18
% 2.35/0.99  sup_num_of_loops:                       58
% 2.35/0.99  sup_fw_superposition:                   17
% 2.35/0.99  sup_bw_superposition:                   31
% 2.35/0.99  sup_immediate_simplified:               22
% 2.35/0.99  sup_given_eliminated:                   0
% 2.35/0.99  comparisons_done:                       0
% 2.35/0.99  comparisons_avoided:                    3
% 2.35/0.99  
% 2.35/0.99  ------ Simplifications
% 2.35/0.99  
% 2.35/0.99  
% 2.35/0.99  sim_fw_subset_subsumed:                 14
% 2.35/0.99  sim_bw_subset_subsumed:                 0
% 2.35/0.99  sim_fw_subsumed:                        0
% 2.35/0.99  sim_bw_subsumed:                        0
% 2.35/0.99  sim_fw_subsumption_res:                 0
% 2.35/0.99  sim_bw_subsumption_res:                 0
% 2.35/0.99  sim_tautology_del:                      1
% 2.35/0.99  sim_eq_tautology_del:                   3
% 2.35/0.99  sim_eq_res_simp:                        0
% 2.35/0.99  sim_fw_demodulated:                     0
% 2.35/0.99  sim_bw_demodulated:                     28
% 2.35/0.99  sim_light_normalised:                   15
% 2.35/0.99  sim_joinable_taut:                      0
% 2.35/0.99  sim_joinable_simp:                      0
% 2.35/0.99  sim_ac_normalised:                      0
% 2.35/0.99  sim_smt_subsumption:                    0
% 2.35/0.99  
%------------------------------------------------------------------------------
