%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:00 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :  193 (3092 expanded)
%              Number of clauses        :  116 ( 860 expanded)
%              Number of leaves         :   21 ( 894 expanded)
%              Depth                    :   21
%              Number of atoms          :  621 (21595 expanded)
%              Number of equality atoms :  257 (7139 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    6 (   2 average)

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
               => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
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
                 => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f52,plain,(
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

fof(f51,plain,(
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

fof(f50,plain,
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

fof(f53,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f52,f51,f50])).

fof(f87,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f76,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f84,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f82,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f53])).

fof(f13,axiom,(
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

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f34])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f49])).

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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f85,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f83,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f86,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f53])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f88,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f89,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f2])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f57,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

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

fof(f61,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f60,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
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

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f33])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f90,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f53])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f56,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1409,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_22,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_34,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_426,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_34])).

cnf(c_427,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_426])).

cnf(c_36,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_431,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_36])).

cnf(c_432,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_431])).

cnf(c_1443,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1409,c_427,c_432])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_19,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_438,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_9,c_19])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_442,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_438,c_19,c_9,c_8])).

cnf(c_443,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_442])).

cnf(c_620,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_21,c_443])).

cnf(c_624,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_620,c_21,c_8,c_438])).

cnf(c_625,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_624])).

cnf(c_1401,plain,
    ( k1_relat_1(X0) = X1
    | k1_xboole_0 = X2
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_2234,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_struct_0(sK1) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1443,c_1401])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_23,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_413,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_35])).

cnf(c_414,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_416,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_414,c_34])).

cnf(c_1405,plain,
    ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_416])).

cnf(c_1434,plain,
    ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1405,c_427])).

cnf(c_1592,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1434])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1408,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1437,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1408,c_427,c_432])).

cnf(c_927,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1918,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_struct_0(sK1))
    | k2_struct_0(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_927])).

cnf(c_1920,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1918])).

cnf(c_3670,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2234,c_40,c_0,c_1592,c_1437,c_1920])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1419,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2341,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1443,c_1419])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1440,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_30,c_427,c_432])).

cnf(c_2495,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2341,c_1440])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_482,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_483,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_487,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_483,c_33])).

cnf(c_488,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_487])).

cnf(c_1404,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_488])).

cnf(c_1972,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1440,c_1404])).

cnf(c_2088,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1972,c_1443,c_1437])).

cnf(c_2500,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2495,c_2088])).

cnf(c_3676,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3670,c_2500])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1412,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4275,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3676,c_1412])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_1650,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1651,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1650])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_3,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_398,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X2)
    | X2 != X0
    | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_3])).

cnf(c_399,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_398])).

cnf(c_1714,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_399])).

cnf(c_1721,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1714])).

cnf(c_2502,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2495,c_1437])).

cnf(c_3678,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3670,c_2502])).

cnf(c_5036,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4275,c_40,c_42,c_1651,c_1721,c_3678])).

cnf(c_1421,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_5046,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_5036,c_1421])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_520,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_29])).

cnf(c_521,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_520])).

cnf(c_523,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_521,c_33])).

cnf(c_1402,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_523])).

cnf(c_1895,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1402,c_33,c_31,c_521,c_1650])).

cnf(c_1406,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_2955,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_1406])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_506,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_29])).

cnf(c_507,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_506])).

cnf(c_509,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_33])).

cnf(c_1403,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_509])).

cnf(c_1961,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1403,c_33,c_31,c_507,c_1650])).

cnf(c_2972,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2955,c_1961])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1413,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3498,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2972,c_1413])).

cnf(c_3499,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2972,c_1419])).

cnf(c_3505,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3499,c_1895])).

cnf(c_28,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1530,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_28,c_427,c_432])).

cnf(c_2091,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2088,c_1530])).

cnf(c_2499,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2495,c_2091])).

cnf(c_3673,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3670,c_2499])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1411,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4276,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3676,c_1411])).

cnf(c_4900,plain,
    ( k1_relat_1(sK2) = k1_xboole_0
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3498,c_40,c_42,c_1651,c_1721,c_3505,c_3673,c_3678,c_4276])).

cnf(c_5250,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5046,c_4900])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1420,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_2394,plain,
    ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1443,c_1420])).

cnf(c_2,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1424,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2503,plain,
    ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2495,c_1434])).

cnf(c_2663,plain,
    ( v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1424,c_2503])).

cnf(c_3345,plain,
    ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2394,c_2663])).

cnf(c_3674,plain,
    ( v1_xboole_0(k1_relat_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3670,c_3345])).

cnf(c_5636,plain,
    ( v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5250,c_3674])).

cnf(c_123,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5636,c_123])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.41/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.00  
% 2.41/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.41/1.00  
% 2.41/1.00  ------  iProver source info
% 2.41/1.00  
% 2.41/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.41/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.41/1.00  git: non_committed_changes: false
% 2.41/1.00  git: last_make_outside_of_git: false
% 2.41/1.00  
% 2.41/1.00  ------ 
% 2.41/1.00  
% 2.41/1.00  ------ Input Options
% 2.41/1.00  
% 2.41/1.00  --out_options                           all
% 2.41/1.00  --tptp_safe_out                         true
% 2.41/1.00  --problem_path                          ""
% 2.41/1.00  --include_path                          ""
% 2.41/1.00  --clausifier                            res/vclausify_rel
% 2.41/1.00  --clausifier_options                    --mode clausify
% 2.41/1.00  --stdin                                 false
% 2.41/1.00  --stats_out                             all
% 2.41/1.00  
% 2.41/1.00  ------ General Options
% 2.41/1.00  
% 2.41/1.00  --fof                                   false
% 2.41/1.00  --time_out_real                         305.
% 2.41/1.00  --time_out_virtual                      -1.
% 2.41/1.00  --symbol_type_check                     false
% 2.41/1.00  --clausify_out                          false
% 2.41/1.00  --sig_cnt_out                           false
% 2.41/1.00  --trig_cnt_out                          false
% 2.41/1.00  --trig_cnt_out_tolerance                1.
% 2.41/1.00  --trig_cnt_out_sk_spl                   false
% 2.41/1.00  --abstr_cl_out                          false
% 2.41/1.00  
% 2.41/1.00  ------ Global Options
% 2.41/1.00  
% 2.41/1.00  --schedule                              default
% 2.41/1.00  --add_important_lit                     false
% 2.41/1.00  --prop_solver_per_cl                    1000
% 2.41/1.00  --min_unsat_core                        false
% 2.41/1.00  --soft_assumptions                      false
% 2.41/1.00  --soft_lemma_size                       3
% 2.41/1.00  --prop_impl_unit_size                   0
% 2.41/1.00  --prop_impl_unit                        []
% 2.41/1.00  --share_sel_clauses                     true
% 2.41/1.00  --reset_solvers                         false
% 2.41/1.00  --bc_imp_inh                            [conj_cone]
% 2.41/1.00  --conj_cone_tolerance                   3.
% 2.41/1.00  --extra_neg_conj                        none
% 2.41/1.00  --large_theory_mode                     true
% 2.41/1.00  --prolific_symb_bound                   200
% 2.41/1.00  --lt_threshold                          2000
% 2.41/1.00  --clause_weak_htbl                      true
% 2.41/1.00  --gc_record_bc_elim                     false
% 2.41/1.00  
% 2.41/1.00  ------ Preprocessing Options
% 2.41/1.00  
% 2.41/1.00  --preprocessing_flag                    true
% 2.41/1.00  --time_out_prep_mult                    0.1
% 2.41/1.00  --splitting_mode                        input
% 2.41/1.00  --splitting_grd                         true
% 2.41/1.00  --splitting_cvd                         false
% 2.41/1.00  --splitting_cvd_svl                     false
% 2.41/1.00  --splitting_nvd                         32
% 2.41/1.00  --sub_typing                            true
% 2.41/1.00  --prep_gs_sim                           true
% 2.41/1.00  --prep_unflatten                        true
% 2.41/1.00  --prep_res_sim                          true
% 2.41/1.00  --prep_upred                            true
% 2.41/1.00  --prep_sem_filter                       exhaustive
% 2.41/1.00  --prep_sem_filter_out                   false
% 2.41/1.00  --pred_elim                             true
% 2.41/1.00  --res_sim_input                         true
% 2.41/1.00  --eq_ax_congr_red                       true
% 2.41/1.00  --pure_diseq_elim                       true
% 2.41/1.00  --brand_transform                       false
% 2.41/1.00  --non_eq_to_eq                          false
% 2.41/1.00  --prep_def_merge                        true
% 2.41/1.00  --prep_def_merge_prop_impl              false
% 2.41/1.00  --prep_def_merge_mbd                    true
% 2.41/1.00  --prep_def_merge_tr_red                 false
% 2.41/1.00  --prep_def_merge_tr_cl                  false
% 2.41/1.00  --smt_preprocessing                     true
% 2.41/1.00  --smt_ac_axioms                         fast
% 2.41/1.00  --preprocessed_out                      false
% 2.41/1.00  --preprocessed_stats                    false
% 2.41/1.00  
% 2.41/1.00  ------ Abstraction refinement Options
% 2.41/1.00  
% 2.41/1.00  --abstr_ref                             []
% 2.41/1.00  --abstr_ref_prep                        false
% 2.41/1.00  --abstr_ref_until_sat                   false
% 2.41/1.00  --abstr_ref_sig_restrict                funpre
% 2.41/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.00  --abstr_ref_under                       []
% 2.41/1.00  
% 2.41/1.00  ------ SAT Options
% 2.41/1.00  
% 2.41/1.00  --sat_mode                              false
% 2.41/1.00  --sat_fm_restart_options                ""
% 2.41/1.00  --sat_gr_def                            false
% 2.41/1.00  --sat_epr_types                         true
% 2.41/1.00  --sat_non_cyclic_types                  false
% 2.41/1.00  --sat_finite_models                     false
% 2.41/1.00  --sat_fm_lemmas                         false
% 2.41/1.00  --sat_fm_prep                           false
% 2.41/1.00  --sat_fm_uc_incr                        true
% 2.41/1.00  --sat_out_model                         small
% 2.41/1.00  --sat_out_clauses                       false
% 2.41/1.00  
% 2.41/1.00  ------ QBF Options
% 2.41/1.00  
% 2.41/1.00  --qbf_mode                              false
% 2.41/1.00  --qbf_elim_univ                         false
% 2.41/1.00  --qbf_dom_inst                          none
% 2.41/1.00  --qbf_dom_pre_inst                      false
% 2.41/1.00  --qbf_sk_in                             false
% 2.41/1.00  --qbf_pred_elim                         true
% 2.41/1.00  --qbf_split                             512
% 2.41/1.00  
% 2.41/1.00  ------ BMC1 Options
% 2.41/1.00  
% 2.41/1.00  --bmc1_incremental                      false
% 2.41/1.00  --bmc1_axioms                           reachable_all
% 2.41/1.00  --bmc1_min_bound                        0
% 2.41/1.00  --bmc1_max_bound                        -1
% 2.41/1.00  --bmc1_max_bound_default                -1
% 2.41/1.00  --bmc1_symbol_reachability              true
% 2.41/1.00  --bmc1_property_lemmas                  false
% 2.41/1.00  --bmc1_k_induction                      false
% 2.41/1.00  --bmc1_non_equiv_states                 false
% 2.41/1.00  --bmc1_deadlock                         false
% 2.41/1.00  --bmc1_ucm                              false
% 2.41/1.00  --bmc1_add_unsat_core                   none
% 2.41/1.00  --bmc1_unsat_core_children              false
% 2.41/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.00  --bmc1_out_stat                         full
% 2.41/1.00  --bmc1_ground_init                      false
% 2.41/1.00  --bmc1_pre_inst_next_state              false
% 2.41/1.00  --bmc1_pre_inst_state                   false
% 2.41/1.00  --bmc1_pre_inst_reach_state             false
% 2.41/1.00  --bmc1_out_unsat_core                   false
% 2.41/1.00  --bmc1_aig_witness_out                  false
% 2.41/1.00  --bmc1_verbose                          false
% 2.41/1.00  --bmc1_dump_clauses_tptp                false
% 2.41/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.00  --bmc1_dump_file                        -
% 2.41/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.00  --bmc1_ucm_extend_mode                  1
% 2.41/1.00  --bmc1_ucm_init_mode                    2
% 2.41/1.00  --bmc1_ucm_cone_mode                    none
% 2.41/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.00  --bmc1_ucm_relax_model                  4
% 2.41/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.00  --bmc1_ucm_layered_model                none
% 2.41/1.00  --bmc1_ucm_max_lemma_size               10
% 2.41/1.00  
% 2.41/1.00  ------ AIG Options
% 2.41/1.00  
% 2.41/1.00  --aig_mode                              false
% 2.41/1.00  
% 2.41/1.00  ------ Instantiation Options
% 2.41/1.00  
% 2.41/1.00  --instantiation_flag                    true
% 2.41/1.00  --inst_sos_flag                         false
% 2.41/1.00  --inst_sos_phase                        true
% 2.41/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.00  --inst_lit_sel_side                     num_symb
% 2.41/1.00  --inst_solver_per_active                1400
% 2.41/1.00  --inst_solver_calls_frac                1.
% 2.41/1.00  --inst_passive_queue_type               priority_queues
% 2.41/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.00  --inst_passive_queues_freq              [25;2]
% 2.41/1.00  --inst_dismatching                      true
% 2.41/1.00  --inst_eager_unprocessed_to_passive     true
% 2.41/1.00  --inst_prop_sim_given                   true
% 2.41/1.00  --inst_prop_sim_new                     false
% 2.41/1.00  --inst_subs_new                         false
% 2.41/1.00  --inst_eq_res_simp                      false
% 2.41/1.00  --inst_subs_given                       false
% 2.41/1.00  --inst_orphan_elimination               true
% 2.41/1.00  --inst_learning_loop_flag               true
% 2.41/1.00  --inst_learning_start                   3000
% 2.41/1.00  --inst_learning_factor                  2
% 2.41/1.00  --inst_start_prop_sim_after_learn       3
% 2.41/1.00  --inst_sel_renew                        solver
% 2.41/1.00  --inst_lit_activity_flag                true
% 2.41/1.00  --inst_restr_to_given                   false
% 2.41/1.00  --inst_activity_threshold               500
% 2.41/1.00  --inst_out_proof                        true
% 2.41/1.00  
% 2.41/1.00  ------ Resolution Options
% 2.41/1.00  
% 2.41/1.00  --resolution_flag                       true
% 2.41/1.00  --res_lit_sel                           adaptive
% 2.41/1.00  --res_lit_sel_side                      none
% 2.41/1.00  --res_ordering                          kbo
% 2.41/1.00  --res_to_prop_solver                    active
% 2.41/1.00  --res_prop_simpl_new                    false
% 2.41/1.00  --res_prop_simpl_given                  true
% 2.41/1.00  --res_passive_queue_type                priority_queues
% 2.41/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.00  --res_passive_queues_freq               [15;5]
% 2.41/1.00  --res_forward_subs                      full
% 2.41/1.00  --res_backward_subs                     full
% 2.41/1.00  --res_forward_subs_resolution           true
% 2.41/1.00  --res_backward_subs_resolution          true
% 2.41/1.00  --res_orphan_elimination                true
% 2.41/1.00  --res_time_limit                        2.
% 2.41/1.00  --res_out_proof                         true
% 2.41/1.00  
% 2.41/1.00  ------ Superposition Options
% 2.41/1.00  
% 2.41/1.00  --superposition_flag                    true
% 2.41/1.00  --sup_passive_queue_type                priority_queues
% 2.41/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.00  --demod_completeness_check              fast
% 2.41/1.00  --demod_use_ground                      true
% 2.41/1.00  --sup_to_prop_solver                    passive
% 2.41/1.00  --sup_prop_simpl_new                    true
% 2.41/1.00  --sup_prop_simpl_given                  true
% 2.41/1.00  --sup_fun_splitting                     false
% 2.41/1.00  --sup_smt_interval                      50000
% 2.41/1.00  
% 2.41/1.00  ------ Superposition Simplification Setup
% 2.41/1.00  
% 2.41/1.00  --sup_indices_passive                   []
% 2.41/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.00  --sup_full_bw                           [BwDemod]
% 2.41/1.00  --sup_immed_triv                        [TrivRules]
% 2.41/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.00  --sup_immed_bw_main                     []
% 2.41/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.00  
% 2.41/1.00  ------ Combination Options
% 2.41/1.00  
% 2.41/1.00  --comb_res_mult                         3
% 2.41/1.00  --comb_sup_mult                         2
% 2.41/1.00  --comb_inst_mult                        10
% 2.41/1.00  
% 2.41/1.00  ------ Debug Options
% 2.41/1.00  
% 2.41/1.00  --dbg_backtrace                         false
% 2.41/1.00  --dbg_dump_prop_clauses                 false
% 2.41/1.00  --dbg_dump_prop_clauses_file            -
% 2.41/1.00  --dbg_out_stat                          false
% 2.41/1.00  ------ Parsing...
% 2.41/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.41/1.00  
% 2.41/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.41/1.00  
% 2.41/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.41/1.00  
% 2.41/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.41/1.00  ------ Proving...
% 2.41/1.00  ------ Problem Properties 
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  clauses                                 30
% 2.41/1.00  conjectures                             5
% 2.41/1.00  EPR                                     2
% 2.41/1.00  Horn                                    25
% 2.41/1.00  unary                                   8
% 2.41/1.00  binary                                  7
% 2.41/1.00  lits                                    78
% 2.41/1.00  lits eq                                 26
% 2.41/1.00  fd_pure                                 0
% 2.41/1.00  fd_pseudo                               0
% 2.41/1.00  fd_cond                                 3
% 2.41/1.00  fd_pseudo_cond                          1
% 2.41/1.00  AC symbols                              0
% 2.41/1.00  
% 2.41/1.00  ------ Schedule dynamic 5 is on 
% 2.41/1.00  
% 2.41/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  ------ 
% 2.41/1.00  Current options:
% 2.41/1.00  ------ 
% 2.41/1.00  
% 2.41/1.00  ------ Input Options
% 2.41/1.00  
% 2.41/1.00  --out_options                           all
% 2.41/1.00  --tptp_safe_out                         true
% 2.41/1.00  --problem_path                          ""
% 2.41/1.00  --include_path                          ""
% 2.41/1.00  --clausifier                            res/vclausify_rel
% 2.41/1.00  --clausifier_options                    --mode clausify
% 2.41/1.00  --stdin                                 false
% 2.41/1.00  --stats_out                             all
% 2.41/1.00  
% 2.41/1.00  ------ General Options
% 2.41/1.00  
% 2.41/1.00  --fof                                   false
% 2.41/1.00  --time_out_real                         305.
% 2.41/1.00  --time_out_virtual                      -1.
% 2.41/1.00  --symbol_type_check                     false
% 2.41/1.00  --clausify_out                          false
% 2.41/1.00  --sig_cnt_out                           false
% 2.41/1.00  --trig_cnt_out                          false
% 2.41/1.00  --trig_cnt_out_tolerance                1.
% 2.41/1.00  --trig_cnt_out_sk_spl                   false
% 2.41/1.00  --abstr_cl_out                          false
% 2.41/1.00  
% 2.41/1.00  ------ Global Options
% 2.41/1.00  
% 2.41/1.00  --schedule                              default
% 2.41/1.00  --add_important_lit                     false
% 2.41/1.00  --prop_solver_per_cl                    1000
% 2.41/1.00  --min_unsat_core                        false
% 2.41/1.00  --soft_assumptions                      false
% 2.41/1.00  --soft_lemma_size                       3
% 2.41/1.00  --prop_impl_unit_size                   0
% 2.41/1.00  --prop_impl_unit                        []
% 2.41/1.00  --share_sel_clauses                     true
% 2.41/1.00  --reset_solvers                         false
% 2.41/1.00  --bc_imp_inh                            [conj_cone]
% 2.41/1.00  --conj_cone_tolerance                   3.
% 2.41/1.00  --extra_neg_conj                        none
% 2.41/1.00  --large_theory_mode                     true
% 2.41/1.00  --prolific_symb_bound                   200
% 2.41/1.00  --lt_threshold                          2000
% 2.41/1.00  --clause_weak_htbl                      true
% 2.41/1.00  --gc_record_bc_elim                     false
% 2.41/1.00  
% 2.41/1.00  ------ Preprocessing Options
% 2.41/1.00  
% 2.41/1.00  --preprocessing_flag                    true
% 2.41/1.00  --time_out_prep_mult                    0.1
% 2.41/1.00  --splitting_mode                        input
% 2.41/1.00  --splitting_grd                         true
% 2.41/1.00  --splitting_cvd                         false
% 2.41/1.00  --splitting_cvd_svl                     false
% 2.41/1.00  --splitting_nvd                         32
% 2.41/1.00  --sub_typing                            true
% 2.41/1.00  --prep_gs_sim                           true
% 2.41/1.00  --prep_unflatten                        true
% 2.41/1.00  --prep_res_sim                          true
% 2.41/1.00  --prep_upred                            true
% 2.41/1.00  --prep_sem_filter                       exhaustive
% 2.41/1.00  --prep_sem_filter_out                   false
% 2.41/1.00  --pred_elim                             true
% 2.41/1.00  --res_sim_input                         true
% 2.41/1.00  --eq_ax_congr_red                       true
% 2.41/1.00  --pure_diseq_elim                       true
% 2.41/1.00  --brand_transform                       false
% 2.41/1.00  --non_eq_to_eq                          false
% 2.41/1.00  --prep_def_merge                        true
% 2.41/1.00  --prep_def_merge_prop_impl              false
% 2.41/1.00  --prep_def_merge_mbd                    true
% 2.41/1.00  --prep_def_merge_tr_red                 false
% 2.41/1.00  --prep_def_merge_tr_cl                  false
% 2.41/1.00  --smt_preprocessing                     true
% 2.41/1.00  --smt_ac_axioms                         fast
% 2.41/1.00  --preprocessed_out                      false
% 2.41/1.00  --preprocessed_stats                    false
% 2.41/1.00  
% 2.41/1.00  ------ Abstraction refinement Options
% 2.41/1.00  
% 2.41/1.00  --abstr_ref                             []
% 2.41/1.00  --abstr_ref_prep                        false
% 2.41/1.00  --abstr_ref_until_sat                   false
% 2.41/1.00  --abstr_ref_sig_restrict                funpre
% 2.41/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.41/1.00  --abstr_ref_under                       []
% 2.41/1.00  
% 2.41/1.00  ------ SAT Options
% 2.41/1.00  
% 2.41/1.00  --sat_mode                              false
% 2.41/1.00  --sat_fm_restart_options                ""
% 2.41/1.00  --sat_gr_def                            false
% 2.41/1.00  --sat_epr_types                         true
% 2.41/1.00  --sat_non_cyclic_types                  false
% 2.41/1.00  --sat_finite_models                     false
% 2.41/1.00  --sat_fm_lemmas                         false
% 2.41/1.00  --sat_fm_prep                           false
% 2.41/1.00  --sat_fm_uc_incr                        true
% 2.41/1.00  --sat_out_model                         small
% 2.41/1.00  --sat_out_clauses                       false
% 2.41/1.00  
% 2.41/1.00  ------ QBF Options
% 2.41/1.00  
% 2.41/1.00  --qbf_mode                              false
% 2.41/1.00  --qbf_elim_univ                         false
% 2.41/1.00  --qbf_dom_inst                          none
% 2.41/1.00  --qbf_dom_pre_inst                      false
% 2.41/1.00  --qbf_sk_in                             false
% 2.41/1.00  --qbf_pred_elim                         true
% 2.41/1.00  --qbf_split                             512
% 2.41/1.00  
% 2.41/1.00  ------ BMC1 Options
% 2.41/1.00  
% 2.41/1.00  --bmc1_incremental                      false
% 2.41/1.00  --bmc1_axioms                           reachable_all
% 2.41/1.00  --bmc1_min_bound                        0
% 2.41/1.00  --bmc1_max_bound                        -1
% 2.41/1.00  --bmc1_max_bound_default                -1
% 2.41/1.00  --bmc1_symbol_reachability              true
% 2.41/1.00  --bmc1_property_lemmas                  false
% 2.41/1.00  --bmc1_k_induction                      false
% 2.41/1.00  --bmc1_non_equiv_states                 false
% 2.41/1.00  --bmc1_deadlock                         false
% 2.41/1.00  --bmc1_ucm                              false
% 2.41/1.00  --bmc1_add_unsat_core                   none
% 2.41/1.00  --bmc1_unsat_core_children              false
% 2.41/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.41/1.00  --bmc1_out_stat                         full
% 2.41/1.00  --bmc1_ground_init                      false
% 2.41/1.00  --bmc1_pre_inst_next_state              false
% 2.41/1.00  --bmc1_pre_inst_state                   false
% 2.41/1.00  --bmc1_pre_inst_reach_state             false
% 2.41/1.00  --bmc1_out_unsat_core                   false
% 2.41/1.00  --bmc1_aig_witness_out                  false
% 2.41/1.00  --bmc1_verbose                          false
% 2.41/1.00  --bmc1_dump_clauses_tptp                false
% 2.41/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.41/1.00  --bmc1_dump_file                        -
% 2.41/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.41/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.41/1.00  --bmc1_ucm_extend_mode                  1
% 2.41/1.00  --bmc1_ucm_init_mode                    2
% 2.41/1.00  --bmc1_ucm_cone_mode                    none
% 2.41/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.41/1.00  --bmc1_ucm_relax_model                  4
% 2.41/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.41/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.41/1.00  --bmc1_ucm_layered_model                none
% 2.41/1.00  --bmc1_ucm_max_lemma_size               10
% 2.41/1.00  
% 2.41/1.00  ------ AIG Options
% 2.41/1.00  
% 2.41/1.00  --aig_mode                              false
% 2.41/1.00  
% 2.41/1.00  ------ Instantiation Options
% 2.41/1.00  
% 2.41/1.00  --instantiation_flag                    true
% 2.41/1.00  --inst_sos_flag                         false
% 2.41/1.00  --inst_sos_phase                        true
% 2.41/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.41/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.41/1.00  --inst_lit_sel_side                     none
% 2.41/1.00  --inst_solver_per_active                1400
% 2.41/1.00  --inst_solver_calls_frac                1.
% 2.41/1.00  --inst_passive_queue_type               priority_queues
% 2.41/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.41/1.00  --inst_passive_queues_freq              [25;2]
% 2.41/1.00  --inst_dismatching                      true
% 2.41/1.00  --inst_eager_unprocessed_to_passive     true
% 2.41/1.00  --inst_prop_sim_given                   true
% 2.41/1.00  --inst_prop_sim_new                     false
% 2.41/1.00  --inst_subs_new                         false
% 2.41/1.00  --inst_eq_res_simp                      false
% 2.41/1.00  --inst_subs_given                       false
% 2.41/1.00  --inst_orphan_elimination               true
% 2.41/1.00  --inst_learning_loop_flag               true
% 2.41/1.00  --inst_learning_start                   3000
% 2.41/1.00  --inst_learning_factor                  2
% 2.41/1.00  --inst_start_prop_sim_after_learn       3
% 2.41/1.00  --inst_sel_renew                        solver
% 2.41/1.00  --inst_lit_activity_flag                true
% 2.41/1.00  --inst_restr_to_given                   false
% 2.41/1.00  --inst_activity_threshold               500
% 2.41/1.00  --inst_out_proof                        true
% 2.41/1.00  
% 2.41/1.00  ------ Resolution Options
% 2.41/1.00  
% 2.41/1.00  --resolution_flag                       false
% 2.41/1.00  --res_lit_sel                           adaptive
% 2.41/1.00  --res_lit_sel_side                      none
% 2.41/1.00  --res_ordering                          kbo
% 2.41/1.00  --res_to_prop_solver                    active
% 2.41/1.00  --res_prop_simpl_new                    false
% 2.41/1.00  --res_prop_simpl_given                  true
% 2.41/1.00  --res_passive_queue_type                priority_queues
% 2.41/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.41/1.00  --res_passive_queues_freq               [15;5]
% 2.41/1.00  --res_forward_subs                      full
% 2.41/1.00  --res_backward_subs                     full
% 2.41/1.00  --res_forward_subs_resolution           true
% 2.41/1.00  --res_backward_subs_resolution          true
% 2.41/1.00  --res_orphan_elimination                true
% 2.41/1.00  --res_time_limit                        2.
% 2.41/1.00  --res_out_proof                         true
% 2.41/1.00  
% 2.41/1.00  ------ Superposition Options
% 2.41/1.00  
% 2.41/1.00  --superposition_flag                    true
% 2.41/1.00  --sup_passive_queue_type                priority_queues
% 2.41/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.41/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.41/1.00  --demod_completeness_check              fast
% 2.41/1.00  --demod_use_ground                      true
% 2.41/1.00  --sup_to_prop_solver                    passive
% 2.41/1.00  --sup_prop_simpl_new                    true
% 2.41/1.00  --sup_prop_simpl_given                  true
% 2.41/1.00  --sup_fun_splitting                     false
% 2.41/1.00  --sup_smt_interval                      50000
% 2.41/1.00  
% 2.41/1.00  ------ Superposition Simplification Setup
% 2.41/1.00  
% 2.41/1.00  --sup_indices_passive                   []
% 2.41/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.41/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.41/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.00  --sup_full_bw                           [BwDemod]
% 2.41/1.00  --sup_immed_triv                        [TrivRules]
% 2.41/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.41/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.00  --sup_immed_bw_main                     []
% 2.41/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.41/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.41/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.41/1.00  
% 2.41/1.00  ------ Combination Options
% 2.41/1.00  
% 2.41/1.00  --comb_res_mult                         3
% 2.41/1.00  --comb_sup_mult                         2
% 2.41/1.00  --comb_inst_mult                        10
% 2.41/1.00  
% 2.41/1.00  ------ Debug Options
% 2.41/1.00  
% 2.41/1.00  --dbg_backtrace                         false
% 2.41/1.00  --dbg_dump_prop_clauses                 false
% 2.41/1.00  --dbg_dump_prop_clauses_file            -
% 2.41/1.00  --dbg_out_stat                          false
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  ------ Proving...
% 2.41/1.00  
% 2.41/1.00  
% 2.41/1.00  % SZS status Theorem for theBenchmark.p
% 2.41/1.00  
% 2.41/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.41/1.00  
% 2.41/1.00  fof(f18,conjecture,(
% 2.41/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f19,negated_conjecture,(
% 2.41/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.41/1.00    inference(negated_conjecture,[],[f18])).
% 2.41/1.00  
% 2.41/1.00  fof(f45,plain,(
% 2.41/1.00    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.41/1.00    inference(ennf_transformation,[],[f19])).
% 2.41/1.00  
% 2.41/1.00  fof(f46,plain,(
% 2.41/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.41/1.00    inference(flattening,[],[f45])).
% 2.41/1.00  
% 2.41/1.00  fof(f52,plain,(
% 2.41/1.00    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.41/1.00    introduced(choice_axiom,[])).
% 2.41/1.00  
% 2.41/1.00  fof(f51,plain,(
% 2.41/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.41/1.00    introduced(choice_axiom,[])).
% 2.41/1.00  
% 2.41/1.00  fof(f50,plain,(
% 2.41/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.41/1.00    introduced(choice_axiom,[])).
% 2.41/1.00  
% 2.41/1.00  fof(f53,plain,(
% 2.41/1.00    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.41/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f46,f52,f51,f50])).
% 2.41/1.00  
% 2.41/1.00  fof(f87,plain,(
% 2.41/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.41/1.00    inference(cnf_transformation,[],[f53])).
% 2.41/1.00  
% 2.41/1.00  fof(f14,axiom,(
% 2.41/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f38,plain,(
% 2.41/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.41/1.00    inference(ennf_transformation,[],[f14])).
% 2.41/1.00  
% 2.41/1.00  fof(f76,plain,(
% 2.41/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.41/1.00    inference(cnf_transformation,[],[f38])).
% 2.41/1.00  
% 2.41/1.00  fof(f84,plain,(
% 2.41/1.00    l1_struct_0(sK1)),
% 2.41/1.00    inference(cnf_transformation,[],[f53])).
% 2.41/1.00  
% 2.41/1.00  fof(f82,plain,(
% 2.41/1.00    l1_struct_0(sK0)),
% 2.41/1.00    inference(cnf_transformation,[],[f53])).
% 2.41/1.00  
% 2.41/1.00  fof(f13,axiom,(
% 2.41/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f36,plain,(
% 2.41/1.00    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.41/1.00    inference(ennf_transformation,[],[f13])).
% 2.41/1.00  
% 2.41/1.00  fof(f37,plain,(
% 2.41/1.00    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.41/1.00    inference(flattening,[],[f36])).
% 2.41/1.00  
% 2.41/1.00  fof(f74,plain,(
% 2.41/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.41/1.00    inference(cnf_transformation,[],[f37])).
% 2.41/1.00  
% 2.41/1.00  fof(f8,axiom,(
% 2.41/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f21,plain,(
% 2.41/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.41/1.00    inference(pure_predicate_removal,[],[f8])).
% 2.41/1.00  
% 2.41/1.00  fof(f29,plain,(
% 2.41/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.00    inference(ennf_transformation,[],[f21])).
% 2.41/1.00  
% 2.41/1.00  fof(f63,plain,(
% 2.41/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/1.00    inference(cnf_transformation,[],[f29])).
% 2.41/1.00  
% 2.41/1.00  fof(f12,axiom,(
% 2.41/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f34,plain,(
% 2.41/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.41/1.00    inference(ennf_transformation,[],[f12])).
% 2.41/1.00  
% 2.41/1.00  fof(f35,plain,(
% 2.41/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.41/1.00    inference(flattening,[],[f34])).
% 2.41/1.00  
% 2.41/1.00  fof(f49,plain,(
% 2.41/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.41/1.00    inference(nnf_transformation,[],[f35])).
% 2.41/1.00  
% 2.41/1.00  fof(f72,plain,(
% 2.41/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.41/1.00    inference(cnf_transformation,[],[f49])).
% 2.41/1.00  
% 2.41/1.00  fof(f7,axiom,(
% 2.41/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f28,plain,(
% 2.41/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.00    inference(ennf_transformation,[],[f7])).
% 2.41/1.00  
% 2.41/1.00  fof(f62,plain,(
% 2.41/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/1.00    inference(cnf_transformation,[],[f28])).
% 2.41/1.00  
% 2.41/1.00  fof(f85,plain,(
% 2.41/1.00    v1_funct_1(sK2)),
% 2.41/1.00    inference(cnf_transformation,[],[f53])).
% 2.41/1.00  
% 2.41/1.00  fof(f1,axiom,(
% 2.41/1.00    v1_xboole_0(k1_xboole_0)),
% 2.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f54,plain,(
% 2.41/1.00    v1_xboole_0(k1_xboole_0)),
% 2.41/1.00    inference(cnf_transformation,[],[f1])).
% 2.41/1.00  
% 2.41/1.00  fof(f15,axiom,(
% 2.41/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f39,plain,(
% 2.41/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.41/1.00    inference(ennf_transformation,[],[f15])).
% 2.41/1.00  
% 2.41/1.00  fof(f40,plain,(
% 2.41/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.41/1.00    inference(flattening,[],[f39])).
% 2.41/1.00  
% 2.41/1.00  fof(f77,plain,(
% 2.41/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.41/1.00    inference(cnf_transformation,[],[f40])).
% 2.41/1.00  
% 2.41/1.00  fof(f83,plain,(
% 2.41/1.00    ~v2_struct_0(sK1)),
% 2.41/1.00    inference(cnf_transformation,[],[f53])).
% 2.41/1.00  
% 2.41/1.00  fof(f86,plain,(
% 2.41/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.41/1.00    inference(cnf_transformation,[],[f53])).
% 2.41/1.00  
% 2.41/1.00  fof(f10,axiom,(
% 2.41/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f31,plain,(
% 2.41/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.00    inference(ennf_transformation,[],[f10])).
% 2.41/1.00  
% 2.41/1.00  fof(f65,plain,(
% 2.41/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/1.00    inference(cnf_transformation,[],[f31])).
% 2.41/1.00  
% 2.41/1.00  fof(f88,plain,(
% 2.41/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.41/1.00    inference(cnf_transformation,[],[f53])).
% 2.41/1.00  
% 2.41/1.00  fof(f16,axiom,(
% 2.41/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.41/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.00  
% 2.41/1.00  fof(f41,plain,(
% 2.41/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.41/1.00    inference(ennf_transformation,[],[f16])).
% 2.41/1.00  
% 2.41/1.00  fof(f42,plain,(
% 2.41/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.41/1.00    inference(flattening,[],[f41])).
% 2.41/1.00  
% 2.41/1.00  fof(f78,plain,(
% 2.41/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/1.00    inference(cnf_transformation,[],[f42])).
% 2.41/1.00  
% 2.41/1.00  fof(f89,plain,(
% 2.41/1.00    v2_funct_1(sK2)),
% 2.41/1.00    inference(cnf_transformation,[],[f53])).
% 2.41/1.00  
% 2.41/1.00  fof(f17,axiom,(
% 2.41/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f43,plain,(
% 2.41/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.41/1.01    inference(ennf_transformation,[],[f17])).
% 2.41/1.01  
% 2.41/1.01  fof(f44,plain,(
% 2.41/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.41/1.01    inference(flattening,[],[f43])).
% 2.41/1.01  
% 2.41/1.01  fof(f81,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f44])).
% 2.41/1.01  
% 2.41/1.01  fof(f2,axiom,(
% 2.41/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f20,plain,(
% 2.41/1.01    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 2.41/1.01    inference(unused_predicate_definition_removal,[],[f2])).
% 2.41/1.01  
% 2.41/1.01  fof(f22,plain,(
% 2.41/1.01    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 2.41/1.01    inference(ennf_transformation,[],[f20])).
% 2.41/1.01  
% 2.41/1.01  fof(f55,plain,(
% 2.41/1.01    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f22])).
% 2.41/1.01  
% 2.41/1.01  fof(f4,axiom,(
% 2.41/1.01    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f24,plain,(
% 2.41/1.01    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.41/1.01    inference(ennf_transformation,[],[f4])).
% 2.41/1.01  
% 2.41/1.01  fof(f57,plain,(
% 2.41/1.01    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f24])).
% 2.41/1.01  
% 2.41/1.01  fof(f6,axiom,(
% 2.41/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f26,plain,(
% 2.41/1.01    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.41/1.01    inference(ennf_transformation,[],[f6])).
% 2.41/1.01  
% 2.41/1.01  fof(f27,plain,(
% 2.41/1.01    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.41/1.01    inference(flattening,[],[f26])).
% 2.41/1.01  
% 2.41/1.01  fof(f61,plain,(
% 2.41/1.01    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f27])).
% 2.41/1.01  
% 2.41/1.01  fof(f60,plain,(
% 2.41/1.01    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f27])).
% 2.41/1.01  
% 2.41/1.01  fof(f11,axiom,(
% 2.41/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f32,plain,(
% 2.41/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.01    inference(ennf_transformation,[],[f11])).
% 2.41/1.01  
% 2.41/1.01  fof(f33,plain,(
% 2.41/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.01    inference(flattening,[],[f32])).
% 2.41/1.01  
% 2.41/1.01  fof(f48,plain,(
% 2.41/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.41/1.01    inference(nnf_transformation,[],[f33])).
% 2.41/1.01  
% 2.41/1.01  fof(f66,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.41/1.01    inference(cnf_transformation,[],[f48])).
% 2.41/1.01  
% 2.41/1.01  fof(f90,plain,(
% 2.41/1.01    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.41/1.01    inference(cnf_transformation,[],[f53])).
% 2.41/1.01  
% 2.41/1.01  fof(f80,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f44])).
% 2.41/1.01  
% 2.41/1.01  fof(f9,axiom,(
% 2.41/1.01    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f30,plain,(
% 2.41/1.01    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.41/1.01    inference(ennf_transformation,[],[f9])).
% 2.41/1.01  
% 2.41/1.01  fof(f64,plain,(
% 2.41/1.01    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f30])).
% 2.41/1.01  
% 2.41/1.01  fof(f3,axiom,(
% 2.41/1.01    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 2.41/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.41/1.01  
% 2.41/1.01  fof(f23,plain,(
% 2.41/1.01    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 2.41/1.01    inference(ennf_transformation,[],[f3])).
% 2.41/1.01  
% 2.41/1.01  fof(f56,plain,(
% 2.41/1.01    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 2.41/1.01    inference(cnf_transformation,[],[f23])).
% 2.41/1.01  
% 2.41/1.01  cnf(c_31,negated_conjecture,
% 2.41/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.41/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1409,plain,
% 2.41/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_22,plain,
% 2.41/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_34,negated_conjecture,
% 2.41/1.01      ( l1_struct_0(sK1) ),
% 2.41/1.01      inference(cnf_transformation,[],[f84]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_426,plain,
% 2.41/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.41/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_34]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_427,plain,
% 2.41/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.41/1.01      inference(unflattening,[status(thm)],[c_426]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_36,negated_conjecture,
% 2.41/1.01      ( l1_struct_0(sK0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_431,plain,
% 2.41/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.41/1.01      inference(resolution_lifted,[status(thm)],[c_22,c_36]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_432,plain,
% 2.41/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.41/1.01      inference(unflattening,[status(thm)],[c_431]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1443,plain,
% 2.41/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.41/1.01      inference(light_normalisation,[status(thm)],[c_1409,c_427,c_432]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_21,plain,
% 2.41/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.01      | v1_partfun1(X0,X1)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | ~ v1_funct_1(X0)
% 2.41/1.01      | k1_xboole_0 = X2 ),
% 2.41/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_9,plain,
% 2.41/1.01      ( v4_relat_1(X0,X1)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.41/1.01      inference(cnf_transformation,[],[f63]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_19,plain,
% 2.41/1.01      ( ~ v1_partfun1(X0,X1)
% 2.41/1.01      | ~ v4_relat_1(X0,X1)
% 2.41/1.01      | ~ v1_relat_1(X0)
% 2.41/1.01      | k1_relat_1(X0) = X1 ),
% 2.41/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_438,plain,
% 2.41/1.01      ( ~ v1_partfun1(X0,X1)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | ~ v1_relat_1(X0)
% 2.41/1.01      | k1_relat_1(X0) = X1 ),
% 2.41/1.01      inference(resolution,[status(thm)],[c_9,c_19]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_8,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | v1_relat_1(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_442,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | ~ v1_partfun1(X0,X1)
% 2.41/1.01      | k1_relat_1(X0) = X1 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_438,c_19,c_9,c_8]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_443,plain,
% 2.41/1.01      ( ~ v1_partfun1(X0,X1)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | k1_relat_1(X0) = X1 ),
% 2.41/1.01      inference(renaming,[status(thm)],[c_442]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_620,plain,
% 2.41/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 2.41/1.01      | ~ v1_funct_1(X0)
% 2.41/1.01      | k1_relat_1(X0) = X1
% 2.41/1.01      | k1_xboole_0 = X2 ),
% 2.41/1.01      inference(resolution,[status(thm)],[c_21,c_443]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_624,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | ~ v1_funct_2(X0,X1,X2)
% 2.41/1.01      | ~ v1_funct_1(X0)
% 2.41/1.01      | k1_relat_1(X0) = X1
% 2.41/1.01      | k1_xboole_0 = X2 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_620,c_21,c_8,c_438]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_625,plain,
% 2.41/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | ~ v1_funct_1(X0)
% 2.41/1.01      | k1_relat_1(X0) = X1
% 2.41/1.01      | k1_xboole_0 = X2 ),
% 2.41/1.01      inference(renaming,[status(thm)],[c_624]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1401,plain,
% 2.41/1.01      ( k1_relat_1(X0) = X1
% 2.41/1.01      | k1_xboole_0 = X2
% 2.41/1.01      | v1_funct_2(X0,X1,X2) != iProver_top
% 2.41/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.41/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2234,plain,
% 2.41/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.41/1.01      | k2_struct_0(sK1) = k1_xboole_0
% 2.41/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_1443,c_1401]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_33,negated_conjecture,
% 2.41/1.01      ( v1_funct_1(sK2) ),
% 2.41/1.01      inference(cnf_transformation,[],[f85]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_40,plain,
% 2.41/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_0,plain,
% 2.41/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f54]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_23,plain,
% 2.41/1.01      ( v2_struct_0(X0)
% 2.41/1.01      | ~ l1_struct_0(X0)
% 2.41/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.41/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_35,negated_conjecture,
% 2.41/1.01      ( ~ v2_struct_0(sK1) ),
% 2.41/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_413,plain,
% 2.41/1.01      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.41/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_35]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_414,plain,
% 2.41/1.01      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.41/1.01      inference(unflattening,[status(thm)],[c_413]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_416,plain,
% 2.41/1.01      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_414,c_34]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1405,plain,
% 2.41/1.01      ( v1_xboole_0(u1_struct_0(sK1)) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_416]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1434,plain,
% 2.41/1.01      ( v1_xboole_0(k2_struct_0(sK1)) != iProver_top ),
% 2.41/1.01      inference(light_normalisation,[status(thm)],[c_1405,c_427]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1592,plain,
% 2.41/1.01      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.41/1.01      inference(predicate_to_equality_rev,[status(thm)],[c_1434]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_32,negated_conjecture,
% 2.41/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.41/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1408,plain,
% 2.41/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1437,plain,
% 2.41/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.41/1.01      inference(light_normalisation,[status(thm)],[c_1408,c_427,c_432]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_927,plain,
% 2.41/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.41/1.01      theory(equality) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1918,plain,
% 2.41/1.01      ( ~ v1_xboole_0(X0)
% 2.41/1.01      | v1_xboole_0(k2_struct_0(sK1))
% 2.41/1.01      | k2_struct_0(sK1) != X0 ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_927]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1920,plain,
% 2.41/1.01      ( v1_xboole_0(k2_struct_0(sK1))
% 2.41/1.01      | ~ v1_xboole_0(k1_xboole_0)
% 2.41/1.01      | k2_struct_0(sK1) != k1_xboole_0 ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_1918]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3670,plain,
% 2.41/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_2234,c_40,c_0,c_1592,c_1437,c_1920]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_11,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1419,plain,
% 2.41/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.41/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2341,plain,
% 2.41/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_1443,c_1419]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_30,negated_conjecture,
% 2.41/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.41/1.01      inference(cnf_transformation,[],[f88]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1440,plain,
% 2.41/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.41/1.01      inference(light_normalisation,[status(thm)],[c_30,c_427,c_432]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2495,plain,
% 2.41/1.01      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_2341,c_1440]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_24,plain,
% 2.41/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | ~ v1_funct_1(X0)
% 2.41/1.01      | ~ v2_funct_1(X0)
% 2.41/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.41/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.41/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_29,negated_conjecture,
% 2.41/1.01      ( v2_funct_1(sK2) ),
% 2.41/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_482,plain,
% 2.41/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | ~ v1_funct_1(X0)
% 2.41/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.41/1.01      | k2_relset_1(X1,X2,X0) != X2
% 2.41/1.01      | sK2 != X0 ),
% 2.41/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_483,plain,
% 2.41/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 2.41/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.41/1.01      | ~ v1_funct_1(sK2)
% 2.41/1.01      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.41/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.41/1.01      inference(unflattening,[status(thm)],[c_482]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_487,plain,
% 2.41/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.41/1.01      | ~ v1_funct_2(sK2,X0,X1)
% 2.41/1.01      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.41/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_483,c_33]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_488,plain,
% 2.41/1.01      ( ~ v1_funct_2(sK2,X0,X1)
% 2.41/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.41/1.01      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.41/1.01      | k2_relset_1(X0,X1,sK2) != X1 ),
% 2.41/1.01      inference(renaming,[status(thm)],[c_487]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1404,plain,
% 2.41/1.01      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 2.41/1.01      | k2_relset_1(X0,X1,sK2) != X1
% 2.41/1.01      | v1_funct_2(sK2,X0,X1) != iProver_top
% 2.41/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_488]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1972,plain,
% 2.41/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.41/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.41/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_1440,c_1404]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2088,plain,
% 2.41/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_1972,c_1443,c_1437]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2500,plain,
% 2.41/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_2495,c_2088]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3676,plain,
% 2.41/1.01      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_3670,c_2500]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_25,plain,
% 2.41/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.41/1.01      | ~ v1_funct_1(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f81]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1412,plain,
% 2.41/1.01      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.41/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.41/1.01      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 2.41/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4275,plain,
% 2.41/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.41/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.41/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.41/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3676,c_1412]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_42,plain,
% 2.41/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1650,plain,
% 2.41/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.41/1.01      | v1_relat_1(sK2) ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1651,plain,
% 2.41/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.41/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_1650]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1,plain,
% 2.41/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.41/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3,plain,
% 2.41/1.01      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 2.41/1.01      | ~ v1_relat_1(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_398,plain,
% 2.41/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.41/1.01      | ~ v1_relat_1(X2)
% 2.41/1.01      | X2 != X0
% 2.41/1.01      | k2_zfmisc_1(k1_relat_1(X2),k2_relat_1(X2)) != X1 ),
% 2.41/1.01      inference(resolution_lifted,[status(thm)],[c_1,c_3]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_399,plain,
% 2.41/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 2.41/1.01      | ~ v1_relat_1(X0) ),
% 2.41/1.01      inference(unflattening,[status(thm)],[c_398]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1714,plain,
% 2.41/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 2.41/1.01      | ~ v1_relat_1(sK2) ),
% 2.41/1.01      inference(instantiation,[status(thm)],[c_399]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1721,plain,
% 2.41/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 2.41/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_1714]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2502,plain,
% 2.41/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_2495,c_1437]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3678,plain,
% 2.41/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_3670,c_2502]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_5036,plain,
% 2.41/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_4275,c_40,c_42,c_1651,c_1721,c_3678]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1421,plain,
% 2.41/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.41/1.01      | v1_relat_1(X0) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_5046,plain,
% 2.41/1.01      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_5036,c_1421]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_6,plain,
% 2.41/1.01      ( ~ v1_funct_1(X0)
% 2.41/1.01      | ~ v2_funct_1(X0)
% 2.41/1.01      | ~ v1_relat_1(X0)
% 2.41/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_520,plain,
% 2.41/1.01      ( ~ v1_funct_1(X0)
% 2.41/1.01      | ~ v1_relat_1(X0)
% 2.41/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.41/1.01      | sK2 != X0 ),
% 2.41/1.01      inference(resolution_lifted,[status(thm)],[c_6,c_29]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_521,plain,
% 2.41/1.01      ( ~ v1_funct_1(sK2)
% 2.41/1.01      | ~ v1_relat_1(sK2)
% 2.41/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.41/1.01      inference(unflattening,[status(thm)],[c_520]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_523,plain,
% 2.41/1.01      ( ~ v1_relat_1(sK2)
% 2.41/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_521,c_33]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1402,plain,
% 2.41/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.41/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_523]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1895,plain,
% 2.41/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_1402,c_33,c_31,c_521,c_1650]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1406,plain,
% 2.41/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 2.41/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2955,plain,
% 2.41/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)))) = iProver_top
% 2.41/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_1895,c_1406]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_7,plain,
% 2.41/1.01      ( ~ v1_funct_1(X0)
% 2.41/1.01      | ~ v2_funct_1(X0)
% 2.41/1.01      | ~ v1_relat_1(X0)
% 2.41/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_506,plain,
% 2.41/1.01      ( ~ v1_funct_1(X0)
% 2.41/1.01      | ~ v1_relat_1(X0)
% 2.41/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.41/1.01      | sK2 != X0 ),
% 2.41/1.01      inference(resolution_lifted,[status(thm)],[c_7,c_29]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_507,plain,
% 2.41/1.01      ( ~ v1_funct_1(sK2)
% 2.41/1.01      | ~ v1_relat_1(sK2)
% 2.41/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.41/1.01      inference(unflattening,[status(thm)],[c_506]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_509,plain,
% 2.41/1.01      ( ~ v1_relat_1(sK2)
% 2.41/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_507,c_33]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1403,plain,
% 2.41/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.41/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_509]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1961,plain,
% 2.41/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_1403,c_33,c_31,c_507,c_1650]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2972,plain,
% 2.41/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.41/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.41/1.01      inference(light_normalisation,[status(thm)],[c_2955,c_1961]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_17,plain,
% 2.41/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.41/1.01      | k1_xboole_0 = X2 ),
% 2.41/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1413,plain,
% 2.41/1.01      ( k1_relset_1(X0,X1,X2) = X0
% 2.41/1.01      | k1_xboole_0 = X1
% 2.41/1.01      | v1_funct_2(X2,X0,X1) != iProver_top
% 2.41/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3498,plain,
% 2.41/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.41/1.01      | k1_relat_1(sK2) = k1_xboole_0
% 2.41/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.41/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2972,c_1413]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3499,plain,
% 2.41/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
% 2.41/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_2972,c_1419]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3505,plain,
% 2.41/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.41/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.41/1.01      inference(light_normalisation,[status(thm)],[c_3499,c_1895]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_28,negated_conjecture,
% 2.41/1.01      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.41/1.01      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f90]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1530,plain,
% 2.41/1.01      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 2.41/1.01      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 2.41/1.01      inference(light_normalisation,[status(thm)],[c_28,c_427,c_432]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2091,plain,
% 2.41/1.01      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 2.41/1.01      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_2088,c_1530]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2499,plain,
% 2.41/1.01      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.41/1.01      | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_2495,c_2091]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3673,plain,
% 2.41/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 2.41/1.01      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_3670,c_2499]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_26,plain,
% 2.41/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.41/1.01      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 2.41/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | ~ v1_funct_1(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f80]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1411,plain,
% 2.41/1.01      ( v1_funct_2(X0,X1,X2) != iProver_top
% 2.41/1.01      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 2.41/1.01      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.41/1.01      | v1_funct_1(X0) != iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4276,plain,
% 2.41/1.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.41/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.41/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.41/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_3676,c_1411]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_4900,plain,
% 2.41/1.01      ( k1_relat_1(sK2) = k1_xboole_0
% 2.41/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_3498,c_40,c_42,c_1651,c_1721,c_3505,c_3673,c_3678,
% 2.41/1.01                 c_4276]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_5250,plain,
% 2.41/1.01      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_5046,c_4900]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_10,plain,
% 2.41/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.41/1.01      | ~ v1_xboole_0(X1)
% 2.41/1.01      | v1_xboole_0(X0) ),
% 2.41/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1420,plain,
% 2.41/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.41/1.01      | v1_xboole_0(X1) != iProver_top
% 2.41/1.01      | v1_xboole_0(X0) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2394,plain,
% 2.41/1.01      ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top
% 2.41/1.01      | v1_xboole_0(sK2) = iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_1443,c_1420]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2,plain,
% 2.41/1.01      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0)) ),
% 2.41/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_1424,plain,
% 2.41/1.01      ( v1_xboole_0(X0) != iProver_top
% 2.41/1.01      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2503,plain,
% 2.41/1.01      ( v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_2495,c_1434]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_2663,plain,
% 2.41/1.01      ( v1_xboole_0(sK2) != iProver_top ),
% 2.41/1.01      inference(superposition,[status(thm)],[c_1424,c_2503]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3345,plain,
% 2.41/1.01      ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top ),
% 2.41/1.01      inference(global_propositional_subsumption,
% 2.41/1.01                [status(thm)],
% 2.41/1.01                [c_2394,c_2663]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_3674,plain,
% 2.41/1.01      ( v1_xboole_0(k1_relat_1(sK2)) != iProver_top ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_3670,c_3345]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_5636,plain,
% 2.41/1.01      ( v1_xboole_0(k1_xboole_0) != iProver_top ),
% 2.41/1.01      inference(demodulation,[status(thm)],[c_5250,c_3674]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(c_123,plain,
% 2.41/1.01      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 2.41/1.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 2.41/1.01  
% 2.41/1.01  cnf(contradiction,plain,
% 2.41/1.01      ( $false ),
% 2.41/1.01      inference(minisat,[status(thm)],[c_5636,c_123]) ).
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.41/1.01  
% 2.41/1.01  ------                               Statistics
% 2.41/1.01  
% 2.41/1.01  ------ General
% 2.41/1.01  
% 2.41/1.01  abstr_ref_over_cycles:                  0
% 2.41/1.01  abstr_ref_under_cycles:                 0
% 2.41/1.01  gc_basic_clause_elim:                   0
% 2.41/1.01  forced_gc_time:                         0
% 2.41/1.01  parsing_time:                           0.014
% 2.41/1.01  unif_index_cands_time:                  0.
% 2.41/1.01  unif_index_add_time:                    0.
% 2.41/1.01  orderings_time:                         0.
% 2.41/1.01  out_proof_time:                         0.013
% 2.41/1.01  total_time:                             0.176
% 2.41/1.01  num_of_symbols:                         56
% 2.41/1.01  num_of_terms:                           5118
% 2.41/1.01  
% 2.41/1.01  ------ Preprocessing
% 2.41/1.01  
% 2.41/1.01  num_of_splits:                          0
% 2.41/1.01  num_of_split_atoms:                     0
% 2.41/1.01  num_of_reused_defs:                     0
% 2.41/1.01  num_eq_ax_congr_red:                    5
% 2.41/1.01  num_of_sem_filtered_clauses:            1
% 2.41/1.01  num_of_subtypes:                        0
% 2.41/1.01  monotx_restored_types:                  0
% 2.41/1.01  sat_num_of_epr_types:                   0
% 2.41/1.01  sat_num_of_non_cyclic_types:            0
% 2.41/1.01  sat_guarded_non_collapsed_types:        0
% 2.41/1.01  num_pure_diseq_elim:                    0
% 2.41/1.01  simp_replaced_by:                       0
% 2.41/1.01  res_preprocessed:                       162
% 2.41/1.01  prep_upred:                             0
% 2.41/1.01  prep_unflattend:                        18
% 2.41/1.01  smt_new_axioms:                         0
% 2.41/1.01  pred_elim_cands:                        5
% 2.41/1.01  pred_elim:                              6
% 2.41/1.01  pred_elim_cl:                           7
% 2.41/1.01  pred_elim_cycles:                       9
% 2.41/1.01  merged_defs:                            0
% 2.41/1.01  merged_defs_ncl:                        0
% 2.41/1.01  bin_hyper_res:                          0
% 2.41/1.01  prep_cycles:                            4
% 2.41/1.01  pred_elim_time:                         0.006
% 2.41/1.01  splitting_time:                         0.
% 2.41/1.01  sem_filter_time:                        0.
% 2.41/1.01  monotx_time:                            0.
% 2.41/1.01  subtype_inf_time:                       0.
% 2.41/1.01  
% 2.41/1.01  ------ Problem properties
% 2.41/1.01  
% 2.41/1.01  clauses:                                30
% 2.41/1.01  conjectures:                            5
% 2.41/1.01  epr:                                    2
% 2.41/1.01  horn:                                   25
% 2.41/1.01  ground:                                 11
% 2.41/1.01  unary:                                  8
% 2.41/1.01  binary:                                 7
% 2.41/1.01  lits:                                   78
% 2.41/1.01  lits_eq:                                26
% 2.41/1.01  fd_pure:                                0
% 2.41/1.01  fd_pseudo:                              0
% 2.41/1.01  fd_cond:                                3
% 2.41/1.01  fd_pseudo_cond:                         1
% 2.41/1.01  ac_symbols:                             0
% 2.41/1.01  
% 2.41/1.01  ------ Propositional Solver
% 2.41/1.01  
% 2.41/1.01  prop_solver_calls:                      28
% 2.41/1.01  prop_fast_solver_calls:                 1122
% 2.41/1.01  smt_solver_calls:                       0
% 2.41/1.01  smt_fast_solver_calls:                  0
% 2.41/1.01  prop_num_of_clauses:                    1876
% 2.41/1.01  prop_preprocess_simplified:             6146
% 2.41/1.01  prop_fo_subsumed:                       29
% 2.41/1.01  prop_solver_time:                       0.
% 2.41/1.01  smt_solver_time:                        0.
% 2.41/1.01  smt_fast_solver_time:                   0.
% 2.41/1.01  prop_fast_solver_time:                  0.
% 2.41/1.01  prop_unsat_core_time:                   0.
% 2.41/1.01  
% 2.41/1.01  ------ QBF
% 2.41/1.01  
% 2.41/1.01  qbf_q_res:                              0
% 2.41/1.01  qbf_num_tautologies:                    0
% 2.41/1.01  qbf_prep_cycles:                        0
% 2.41/1.01  
% 2.41/1.01  ------ BMC1
% 2.41/1.01  
% 2.41/1.01  bmc1_current_bound:                     -1
% 2.41/1.01  bmc1_last_solved_bound:                 -1
% 2.41/1.01  bmc1_unsat_core_size:                   -1
% 2.41/1.01  bmc1_unsat_core_parents_size:           -1
% 2.41/1.01  bmc1_merge_next_fun:                    0
% 2.41/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.41/1.01  
% 2.41/1.01  ------ Instantiation
% 2.41/1.01  
% 2.41/1.01  inst_num_of_clauses:                    710
% 2.41/1.01  inst_num_in_passive:                    69
% 2.41/1.01  inst_num_in_active:                     339
% 2.41/1.01  inst_num_in_unprocessed:                302
% 2.41/1.01  inst_num_of_loops:                      360
% 2.41/1.01  inst_num_of_learning_restarts:          0
% 2.41/1.01  inst_num_moves_active_passive:          17
% 2.41/1.01  inst_lit_activity:                      0
% 2.41/1.01  inst_lit_activity_moves:                0
% 2.41/1.01  inst_num_tautologies:                   0
% 2.41/1.01  inst_num_prop_implied:                  0
% 2.41/1.01  inst_num_existing_simplified:           0
% 2.41/1.01  inst_num_eq_res_simplified:             0
% 2.41/1.01  inst_num_child_elim:                    0
% 2.41/1.01  inst_num_of_dismatching_blockings:      64
% 2.41/1.01  inst_num_of_non_proper_insts:           458
% 2.41/1.01  inst_num_of_duplicates:                 0
% 2.41/1.01  inst_inst_num_from_inst_to_res:         0
% 2.41/1.01  inst_dismatching_checking_time:         0.
% 2.41/1.01  
% 2.41/1.01  ------ Resolution
% 2.41/1.01  
% 2.41/1.01  res_num_of_clauses:                     0
% 2.41/1.01  res_num_in_passive:                     0
% 2.41/1.01  res_num_in_active:                      0
% 2.41/1.01  res_num_of_loops:                       166
% 2.41/1.01  res_forward_subset_subsumed:            52
% 2.41/1.01  res_backward_subset_subsumed:           2
% 2.41/1.01  res_forward_subsumed:                   0
% 2.41/1.01  res_backward_subsumed:                  0
% 2.41/1.01  res_forward_subsumption_resolution:     1
% 2.41/1.01  res_backward_subsumption_resolution:    0
% 2.41/1.01  res_clause_to_clause_subsumption:       119
% 2.41/1.01  res_orphan_elimination:                 0
% 2.41/1.01  res_tautology_del:                      50
% 2.41/1.01  res_num_eq_res_simplified:              0
% 2.41/1.01  res_num_sel_changes:                    0
% 2.41/1.01  res_moves_from_active_to_pass:          0
% 2.41/1.01  
% 2.41/1.01  ------ Superposition
% 2.41/1.01  
% 2.41/1.01  sup_time_total:                         0.
% 2.41/1.01  sup_time_generating:                    0.
% 2.41/1.01  sup_time_sim_full:                      0.
% 2.41/1.01  sup_time_sim_immed:                     0.
% 2.41/1.01  
% 2.41/1.01  sup_num_of_clauses:                     46
% 2.41/1.01  sup_num_in_active:                      33
% 2.41/1.01  sup_num_in_passive:                     13
% 2.41/1.01  sup_num_of_loops:                       70
% 2.41/1.01  sup_fw_superposition:                   21
% 2.41/1.01  sup_bw_superposition:                   44
% 2.41/1.01  sup_immediate_simplified:               33
% 2.41/1.01  sup_given_eliminated:                   0
% 2.41/1.01  comparisons_done:                       0
% 2.41/1.01  comparisons_avoided:                    6
% 2.41/1.01  
% 2.41/1.01  ------ Simplifications
% 2.41/1.01  
% 2.41/1.01  
% 2.41/1.01  sim_fw_subset_subsumed:                 13
% 2.41/1.01  sim_bw_subset_subsumed:                 6
% 2.41/1.01  sim_fw_subsumed:                        0
% 2.41/1.01  sim_bw_subsumed:                        0
% 2.41/1.01  sim_fw_subsumption_res:                 0
% 2.41/1.01  sim_bw_subsumption_res:                 0
% 2.41/1.01  sim_tautology_del:                      2
% 2.41/1.01  sim_eq_tautology_del:                   3
% 2.41/1.01  sim_eq_res_simp:                        2
% 2.41/1.01  sim_fw_demodulated:                     4
% 2.41/1.01  sim_bw_demodulated:                     33
% 2.41/1.01  sim_light_normalised:                   25
% 2.41/1.01  sim_joinable_taut:                      0
% 2.41/1.01  sim_joinable_simp:                      0
% 2.41/1.01  sim_ac_normalised:                      0
% 2.41/1.01  sim_smt_subsumption:                    0
% 2.41/1.01  
%------------------------------------------------------------------------------
