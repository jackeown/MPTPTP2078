%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:16:59 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :  233 (13423 expanded)
%              Number of clauses        :  145 (3697 expanded)
%              Number of leaves         :   23 (3884 expanded)
%              Depth                    :   30
%              Number of atoms          :  720 (94690 expanded)
%              Number of equality atoms :  321 (31120 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23,conjecture,(
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

fof(f24,negated_conjecture,(
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
    inference(negated_conjecture,[],[f23])).

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
    inference(ennf_transformation,[],[f24])).

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

fof(f60,plain,(
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

fof(f59,plain,(
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

fof(f58,plain,
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

fof(f61,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f60,f59,f58])).

fof(f103,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f61])).

fof(f20,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f95,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f100,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f98,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f36])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f21,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f96,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f99,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f40])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f90,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f101,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f102,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f61])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f104,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f19,axiom,(
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
    inference(ennf_transformation,[],[f19])).

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

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f105,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f61])).

fof(f17,axiom,(
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

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f56,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f22,axiom,(
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
    inference(ennf_transformation,[],[f22])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f106,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f61])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f75,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f74,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f51])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f52])).

fof(f108,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f63])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f65,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f53])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f54])).

fof(f110,plain,(
    ! [X1] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1828,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_33,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_42,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_518,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_42])).

cnf(c_519,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_44,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_523,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_44])).

cnf(c_524,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_1872,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1828,c_519,c_524])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_34,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_505,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_43])).

cnf(c_506,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_505])).

cnf(c_508,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_506,c_42])).

cnf(c_534,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_508])).

cnf(c_535,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_534])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_29,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_558,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_18,c_29])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_560,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_558,c_29,c_18,c_17])).

cnf(c_561,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_560])).

cnf(c_618,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_535,c_561])).

cnf(c_1823,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_2730,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1872,c_1823])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_48,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1827,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_1866,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1827,c_519,c_524])).

cnf(c_3109,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2730,c_48,c_1866])).

cnf(c_3110,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3109])).

cnf(c_3117,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1872,c_3110])).

cnf(c_3130,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3117,c_1872])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1835,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4488,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3130,c_1835])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1869,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_38,c_519,c_524])).

cnf(c_3132,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_3117,c_1869])).

cnf(c_4606,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4488,c_3132])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_37,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_716,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_37])).

cnf(c_717,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_716])).

cnf(c_721,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_717,c_41])).

cnf(c_722,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_721])).

cnf(c_1819,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_722])).

cnf(c_2722,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_1819])).

cnf(c_3039,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2722,c_1872,c_1866])).

cnf(c_3126,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3117,c_3039])).

cnf(c_4716,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4606,c_3126])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1829,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7106,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k1_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4716,c_1829])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_692,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_37])).

cnf(c_693,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(unflattening,[status(thm)],[c_692])).

cnf(c_697,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK2,X1,X0)
    | v1_funct_2(k2_funct_1(sK2),X0,X1)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_693,c_41])).

cnf(c_698,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(renaming,[status(thm)],[c_697])).

cnf(c_1820,plain,
    ( k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_698])).

cnf(c_2438,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_1820])).

cnf(c_2480,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2438,c_1872,c_1866])).

cnf(c_3129,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3117,c_2480])).

cnf(c_4718,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4606,c_3129])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_644,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_37])).

cnf(c_645,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(unflattening,[status(thm)],[c_644])).

cnf(c_649,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK2,X0,X1)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_645,c_41])).

cnf(c_650,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(renaming,[status(thm)],[c_649])).

cnf(c_1822,plain,
    ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1
    | v1_funct_2(sK2,X0,X1) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_650])).

cnf(c_2490,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_1869,c_1822])).

cnf(c_2563,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2490,c_1872,c_1866])).

cnf(c_36,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1977,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(light_normalisation,[status(thm)],[c_36,c_519,c_524])).

cnf(c_2566,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2563,c_1977])).

cnf(c_3127,plain,
    ( k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3117,c_2566])).

cnf(c_4715,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4606,c_3127])).

cnf(c_4487,plain,
    ( k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3126,c_1835])).

cnf(c_5903,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(light_normalisation,[status(thm)],[c_4487,c_4606])).

cnf(c_6273,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4715,c_5903])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_574,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(resolution,[status(thm)],[c_18,c_13])).

cnf(c_578,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relat_1(X0,X1) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_574,c_18,c_17,c_13])).

cnf(c_1824,plain,
    ( k7_relat_1(X0,X1) = X0
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_578])).

cnf(c_3806,plain,
    ( k7_relat_1(k2_funct_1(sK2),k2_struct_0(sK1)) = k2_funct_1(sK2) ),
    inference(superposition,[status(thm)],[c_3126,c_1824])).

cnf(c_4714,plain,
    ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4606,c_3806])).

cnf(c_1836,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4111,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3126,c_1836])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1837,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4603,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
    inference(superposition,[status(thm)],[c_4111,c_1837])).

cnf(c_6682,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4714,c_4603])).

cnf(c_3689,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_3130,c_1824])).

cnf(c_4112,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3130,c_1836])).

cnf(c_4520,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_4112,c_1837])).

cnf(c_6348,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_3689,c_4520])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1842,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_16,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_740,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0
    | sK2 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_37])).

cnf(c_741,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_740])).

cnf(c_745,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_741,c_41])).

cnf(c_1818,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_747,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_2105,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_2106,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2105])).

cnf(c_2163,plain,
    ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
    | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1818,c_50,c_747,c_2106])).

cnf(c_2164,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
    | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2163])).

cnf(c_2867,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1842,c_2164])).

cnf(c_6493,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_6348,c_2867])).

cnf(c_6683,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_6682,c_6493])).

cnf(c_7752,plain,
    ( k1_relat_1(sK2) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7106,c_4718,c_6273,c_6683])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1839,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_3688,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3130,c_1839])).

cnf(c_4713,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4606,c_3688])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1843,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5497,plain,
    ( k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)) = sK2
    | r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4713,c_1843])).

cnf(c_7757,plain,
    ( k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)) = sK2
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)),sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7752,c_5497])).

cnf(c_5,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f110])).

cnf(c_7814,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7757,c_5])).

cnf(c_2519,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2))
    | r1_tarski(X0,sK2) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2520,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(X0,sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2519])).

cnf(c_2522,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2520])).

cnf(c_2554,plain,
    ( ~ r1_tarski(X0,sK2)
    | ~ r1_tarski(sK2,X0)
    | sK2 = X0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2555,plain,
    ( sK2 = X0
    | r1_tarski(X0,sK2) != iProver_top
    | r1_tarski(sK2,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2554])).

cnf(c_2557,plain,
    ( sK2 = k1_xboole_0
    | r1_tarski(sK2,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2555])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3447,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_3450,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3447])).

cnf(c_7767,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7752,c_4713])).

cnf(c_7789,plain,
    ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7767,c_5])).

cnf(c_9415,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7814,c_2522,c_2557,c_3450,c_7789])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_530,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_508])).

cnf(c_4722,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4606,c_530])).

cnf(c_9438,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_9415,c_4722])).

cnf(c_14,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_9498,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_9438,c_14])).

cnf(c_9499,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_9498])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.11/0.33  % Computer   : n001.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % WCLimit    : 600
% 0.11/0.33  % DateTime   : Tue Dec  1 13:38:00 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  % Running in FOF mode
% 3.34/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/0.97  
% 3.34/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.34/0.97  
% 3.34/0.97  ------  iProver source info
% 3.34/0.97  
% 3.34/0.97  git: date: 2020-06-30 10:37:57 +0100
% 3.34/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.34/0.97  git: non_committed_changes: false
% 3.34/0.97  git: last_make_outside_of_git: false
% 3.34/0.97  
% 3.34/0.97  ------ 
% 3.34/0.97  
% 3.34/0.97  ------ Input Options
% 3.34/0.97  
% 3.34/0.97  --out_options                           all
% 3.34/0.97  --tptp_safe_out                         true
% 3.34/0.97  --problem_path                          ""
% 3.34/0.97  --include_path                          ""
% 3.34/0.97  --clausifier                            res/vclausify_rel
% 3.34/0.97  --clausifier_options                    --mode clausify
% 3.34/0.97  --stdin                                 false
% 3.34/0.97  --stats_out                             all
% 3.34/0.97  
% 3.34/0.97  ------ General Options
% 3.34/0.97  
% 3.34/0.97  --fof                                   false
% 3.34/0.97  --time_out_real                         305.
% 3.34/0.97  --time_out_virtual                      -1.
% 3.34/0.97  --symbol_type_check                     false
% 3.34/0.97  --clausify_out                          false
% 3.34/0.97  --sig_cnt_out                           false
% 3.34/0.97  --trig_cnt_out                          false
% 3.34/0.97  --trig_cnt_out_tolerance                1.
% 3.34/0.97  --trig_cnt_out_sk_spl                   false
% 3.34/0.97  --abstr_cl_out                          false
% 3.34/0.97  
% 3.34/0.97  ------ Global Options
% 3.34/0.97  
% 3.34/0.97  --schedule                              default
% 3.34/0.97  --add_important_lit                     false
% 3.34/0.97  --prop_solver_per_cl                    1000
% 3.34/0.97  --min_unsat_core                        false
% 3.34/0.97  --soft_assumptions                      false
% 3.34/0.97  --soft_lemma_size                       3
% 3.34/0.97  --prop_impl_unit_size                   0
% 3.34/0.97  --prop_impl_unit                        []
% 3.34/0.97  --share_sel_clauses                     true
% 3.34/0.97  --reset_solvers                         false
% 3.34/0.97  --bc_imp_inh                            [conj_cone]
% 3.34/0.97  --conj_cone_tolerance                   3.
% 3.34/0.97  --extra_neg_conj                        none
% 3.34/0.97  --large_theory_mode                     true
% 3.34/0.97  --prolific_symb_bound                   200
% 3.34/0.97  --lt_threshold                          2000
% 3.34/0.97  --clause_weak_htbl                      true
% 3.34/0.97  --gc_record_bc_elim                     false
% 3.34/0.97  
% 3.34/0.97  ------ Preprocessing Options
% 3.34/0.97  
% 3.34/0.97  --preprocessing_flag                    true
% 3.34/0.97  --time_out_prep_mult                    0.1
% 3.34/0.97  --splitting_mode                        input
% 3.34/0.97  --splitting_grd                         true
% 3.34/0.97  --splitting_cvd                         false
% 3.34/0.97  --splitting_cvd_svl                     false
% 3.34/0.97  --splitting_nvd                         32
% 3.34/0.97  --sub_typing                            true
% 3.34/0.97  --prep_gs_sim                           true
% 3.34/0.97  --prep_unflatten                        true
% 3.34/0.97  --prep_res_sim                          true
% 3.34/0.97  --prep_upred                            true
% 3.34/0.97  --prep_sem_filter                       exhaustive
% 3.34/0.97  --prep_sem_filter_out                   false
% 3.34/0.97  --pred_elim                             true
% 3.34/0.97  --res_sim_input                         true
% 3.34/0.97  --eq_ax_congr_red                       true
% 3.34/0.97  --pure_diseq_elim                       true
% 3.34/0.97  --brand_transform                       false
% 3.34/0.97  --non_eq_to_eq                          false
% 3.34/0.97  --prep_def_merge                        true
% 3.34/0.97  --prep_def_merge_prop_impl              false
% 3.34/0.97  --prep_def_merge_mbd                    true
% 3.34/0.97  --prep_def_merge_tr_red                 false
% 3.34/0.97  --prep_def_merge_tr_cl                  false
% 3.34/0.97  --smt_preprocessing                     true
% 3.34/0.97  --smt_ac_axioms                         fast
% 3.34/0.97  --preprocessed_out                      false
% 3.34/0.97  --preprocessed_stats                    false
% 3.34/0.97  
% 3.34/0.97  ------ Abstraction refinement Options
% 3.34/0.97  
% 3.34/0.97  --abstr_ref                             []
% 3.34/0.97  --abstr_ref_prep                        false
% 3.34/0.97  --abstr_ref_until_sat                   false
% 3.34/0.97  --abstr_ref_sig_restrict                funpre
% 3.34/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.97  --abstr_ref_under                       []
% 3.34/0.97  
% 3.34/0.97  ------ SAT Options
% 3.34/0.97  
% 3.34/0.97  --sat_mode                              false
% 3.34/0.97  --sat_fm_restart_options                ""
% 3.34/0.97  --sat_gr_def                            false
% 3.34/0.97  --sat_epr_types                         true
% 3.34/0.97  --sat_non_cyclic_types                  false
% 3.34/0.97  --sat_finite_models                     false
% 3.34/0.97  --sat_fm_lemmas                         false
% 3.34/0.97  --sat_fm_prep                           false
% 3.34/0.97  --sat_fm_uc_incr                        true
% 3.34/0.97  --sat_out_model                         small
% 3.34/0.97  --sat_out_clauses                       false
% 3.34/0.97  
% 3.34/0.97  ------ QBF Options
% 3.34/0.97  
% 3.34/0.97  --qbf_mode                              false
% 3.34/0.97  --qbf_elim_univ                         false
% 3.34/0.97  --qbf_dom_inst                          none
% 3.34/0.97  --qbf_dom_pre_inst                      false
% 3.34/0.97  --qbf_sk_in                             false
% 3.34/0.97  --qbf_pred_elim                         true
% 3.34/0.97  --qbf_split                             512
% 3.34/0.97  
% 3.34/0.97  ------ BMC1 Options
% 3.34/0.97  
% 3.34/0.97  --bmc1_incremental                      false
% 3.34/0.97  --bmc1_axioms                           reachable_all
% 3.34/0.97  --bmc1_min_bound                        0
% 3.34/0.97  --bmc1_max_bound                        -1
% 3.34/0.97  --bmc1_max_bound_default                -1
% 3.34/0.97  --bmc1_symbol_reachability              true
% 3.34/0.97  --bmc1_property_lemmas                  false
% 3.34/0.97  --bmc1_k_induction                      false
% 3.34/0.97  --bmc1_non_equiv_states                 false
% 3.34/0.97  --bmc1_deadlock                         false
% 3.34/0.97  --bmc1_ucm                              false
% 3.34/0.97  --bmc1_add_unsat_core                   none
% 3.34/0.97  --bmc1_unsat_core_children              false
% 3.34/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.97  --bmc1_out_stat                         full
% 3.34/0.97  --bmc1_ground_init                      false
% 3.34/0.97  --bmc1_pre_inst_next_state              false
% 3.34/0.97  --bmc1_pre_inst_state                   false
% 3.34/0.97  --bmc1_pre_inst_reach_state             false
% 3.34/0.97  --bmc1_out_unsat_core                   false
% 3.34/0.97  --bmc1_aig_witness_out                  false
% 3.34/0.97  --bmc1_verbose                          false
% 3.34/0.97  --bmc1_dump_clauses_tptp                false
% 3.34/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.97  --bmc1_dump_file                        -
% 3.34/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.97  --bmc1_ucm_extend_mode                  1
% 3.34/0.97  --bmc1_ucm_init_mode                    2
% 3.34/0.97  --bmc1_ucm_cone_mode                    none
% 3.34/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.97  --bmc1_ucm_relax_model                  4
% 3.34/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.97  --bmc1_ucm_layered_model                none
% 3.34/0.97  --bmc1_ucm_max_lemma_size               10
% 3.34/0.97  
% 3.34/0.97  ------ AIG Options
% 3.34/0.97  
% 3.34/0.97  --aig_mode                              false
% 3.34/0.97  
% 3.34/0.97  ------ Instantiation Options
% 3.34/0.97  
% 3.34/0.97  --instantiation_flag                    true
% 3.34/0.97  --inst_sos_flag                         false
% 3.34/0.97  --inst_sos_phase                        true
% 3.34/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.97  --inst_lit_sel_side                     num_symb
% 3.34/0.97  --inst_solver_per_active                1400
% 3.34/0.97  --inst_solver_calls_frac                1.
% 3.34/0.97  --inst_passive_queue_type               priority_queues
% 3.34/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.97  --inst_passive_queues_freq              [25;2]
% 3.34/0.97  --inst_dismatching                      true
% 3.34/0.97  --inst_eager_unprocessed_to_passive     true
% 3.34/0.97  --inst_prop_sim_given                   true
% 3.34/0.97  --inst_prop_sim_new                     false
% 3.34/0.97  --inst_subs_new                         false
% 3.34/0.97  --inst_eq_res_simp                      false
% 3.34/0.97  --inst_subs_given                       false
% 3.34/0.97  --inst_orphan_elimination               true
% 3.34/0.97  --inst_learning_loop_flag               true
% 3.34/0.97  --inst_learning_start                   3000
% 3.34/0.97  --inst_learning_factor                  2
% 3.34/0.97  --inst_start_prop_sim_after_learn       3
% 3.34/0.97  --inst_sel_renew                        solver
% 3.34/0.97  --inst_lit_activity_flag                true
% 3.34/0.97  --inst_restr_to_given                   false
% 3.34/0.97  --inst_activity_threshold               500
% 3.34/0.97  --inst_out_proof                        true
% 3.34/0.97  
% 3.34/0.97  ------ Resolution Options
% 3.34/0.97  
% 3.34/0.97  --resolution_flag                       true
% 3.34/0.97  --res_lit_sel                           adaptive
% 3.34/0.97  --res_lit_sel_side                      none
% 3.34/0.97  --res_ordering                          kbo
% 3.34/0.97  --res_to_prop_solver                    active
% 3.34/0.97  --res_prop_simpl_new                    false
% 3.34/0.97  --res_prop_simpl_given                  true
% 3.34/0.97  --res_passive_queue_type                priority_queues
% 3.34/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.97  --res_passive_queues_freq               [15;5]
% 3.34/0.97  --res_forward_subs                      full
% 3.34/0.97  --res_backward_subs                     full
% 3.34/0.97  --res_forward_subs_resolution           true
% 3.34/0.97  --res_backward_subs_resolution          true
% 3.34/0.97  --res_orphan_elimination                true
% 3.34/0.97  --res_time_limit                        2.
% 3.34/0.97  --res_out_proof                         true
% 3.34/0.97  
% 3.34/0.97  ------ Superposition Options
% 3.34/0.97  
% 3.34/0.97  --superposition_flag                    true
% 3.34/0.97  --sup_passive_queue_type                priority_queues
% 3.34/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.97  --demod_completeness_check              fast
% 3.34/0.97  --demod_use_ground                      true
% 3.34/0.97  --sup_to_prop_solver                    passive
% 3.34/0.97  --sup_prop_simpl_new                    true
% 3.34/0.97  --sup_prop_simpl_given                  true
% 3.34/0.97  --sup_fun_splitting                     false
% 3.34/0.97  --sup_smt_interval                      50000
% 3.34/0.97  
% 3.34/0.97  ------ Superposition Simplification Setup
% 3.34/0.97  
% 3.34/0.97  --sup_indices_passive                   []
% 3.34/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.97  --sup_full_bw                           [BwDemod]
% 3.34/0.97  --sup_immed_triv                        [TrivRules]
% 3.34/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.97  --sup_immed_bw_main                     []
% 3.34/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.97  
% 3.34/0.97  ------ Combination Options
% 3.34/0.97  
% 3.34/0.97  --comb_res_mult                         3
% 3.34/0.97  --comb_sup_mult                         2
% 3.34/0.97  --comb_inst_mult                        10
% 3.34/0.97  
% 3.34/0.97  ------ Debug Options
% 3.34/0.97  
% 3.34/0.97  --dbg_backtrace                         false
% 3.34/0.97  --dbg_dump_prop_clauses                 false
% 3.34/0.97  --dbg_dump_prop_clauses_file            -
% 3.34/0.97  --dbg_out_stat                          false
% 3.34/0.97  ------ Parsing...
% 3.34/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.34/0.97  
% 3.34/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.34/0.97  
% 3.34/0.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.34/0.97  
% 3.34/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.34/0.97  ------ Proving...
% 3.34/0.97  ------ Problem Properties 
% 3.34/0.97  
% 3.34/0.97  
% 3.34/0.97  clauses                                 36
% 3.34/0.97  conjectures                             5
% 3.34/0.97  EPR                                     4
% 3.34/0.97  Horn                                    31
% 3.34/0.97  unary                                   14
% 3.34/0.97  binary                                  7
% 3.34/0.97  lits                                    82
% 3.34/0.97  lits eq                                 33
% 3.34/0.97  fd_pure                                 0
% 3.34/0.97  fd_pseudo                               0
% 3.34/0.97  fd_cond                                 4
% 3.34/0.97  fd_pseudo_cond                          2
% 3.34/0.97  AC symbols                              0
% 3.34/0.97  
% 3.34/0.97  ------ Schedule dynamic 5 is on 
% 3.34/0.97  
% 3.34/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.34/0.97  
% 3.34/0.97  
% 3.34/0.97  ------ 
% 3.34/0.97  Current options:
% 3.34/0.97  ------ 
% 3.34/0.97  
% 3.34/0.97  ------ Input Options
% 3.34/0.97  
% 3.34/0.97  --out_options                           all
% 3.34/0.97  --tptp_safe_out                         true
% 3.34/0.97  --problem_path                          ""
% 3.34/0.97  --include_path                          ""
% 3.34/0.97  --clausifier                            res/vclausify_rel
% 3.34/0.97  --clausifier_options                    --mode clausify
% 3.34/0.97  --stdin                                 false
% 3.34/0.97  --stats_out                             all
% 3.34/0.97  
% 3.34/0.97  ------ General Options
% 3.34/0.97  
% 3.34/0.97  --fof                                   false
% 3.34/0.97  --time_out_real                         305.
% 3.34/0.97  --time_out_virtual                      -1.
% 3.34/0.97  --symbol_type_check                     false
% 3.34/0.97  --clausify_out                          false
% 3.34/0.97  --sig_cnt_out                           false
% 3.34/0.97  --trig_cnt_out                          false
% 3.34/0.97  --trig_cnt_out_tolerance                1.
% 3.34/0.97  --trig_cnt_out_sk_spl                   false
% 3.34/0.97  --abstr_cl_out                          false
% 3.34/0.97  
% 3.34/0.97  ------ Global Options
% 3.34/0.97  
% 3.34/0.97  --schedule                              default
% 3.34/0.97  --add_important_lit                     false
% 3.34/0.97  --prop_solver_per_cl                    1000
% 3.34/0.97  --min_unsat_core                        false
% 3.34/0.97  --soft_assumptions                      false
% 3.34/0.97  --soft_lemma_size                       3
% 3.34/0.97  --prop_impl_unit_size                   0
% 3.34/0.97  --prop_impl_unit                        []
% 3.34/0.97  --share_sel_clauses                     true
% 3.34/0.97  --reset_solvers                         false
% 3.34/0.97  --bc_imp_inh                            [conj_cone]
% 3.34/0.97  --conj_cone_tolerance                   3.
% 3.34/0.97  --extra_neg_conj                        none
% 3.34/0.97  --large_theory_mode                     true
% 3.34/0.97  --prolific_symb_bound                   200
% 3.34/0.97  --lt_threshold                          2000
% 3.34/0.97  --clause_weak_htbl                      true
% 3.34/0.97  --gc_record_bc_elim                     false
% 3.34/0.97  
% 3.34/0.97  ------ Preprocessing Options
% 3.34/0.97  
% 3.34/0.97  --preprocessing_flag                    true
% 3.34/0.97  --time_out_prep_mult                    0.1
% 3.34/0.97  --splitting_mode                        input
% 3.34/0.97  --splitting_grd                         true
% 3.34/0.97  --splitting_cvd                         false
% 3.34/0.97  --splitting_cvd_svl                     false
% 3.34/0.97  --splitting_nvd                         32
% 3.34/0.97  --sub_typing                            true
% 3.34/0.97  --prep_gs_sim                           true
% 3.34/0.97  --prep_unflatten                        true
% 3.34/0.97  --prep_res_sim                          true
% 3.34/0.97  --prep_upred                            true
% 3.34/0.97  --prep_sem_filter                       exhaustive
% 3.34/0.97  --prep_sem_filter_out                   false
% 3.34/0.97  --pred_elim                             true
% 3.34/0.97  --res_sim_input                         true
% 3.34/0.97  --eq_ax_congr_red                       true
% 3.34/0.97  --pure_diseq_elim                       true
% 3.34/0.97  --brand_transform                       false
% 3.34/0.97  --non_eq_to_eq                          false
% 3.34/0.97  --prep_def_merge                        true
% 3.34/0.97  --prep_def_merge_prop_impl              false
% 3.34/0.97  --prep_def_merge_mbd                    true
% 3.34/0.97  --prep_def_merge_tr_red                 false
% 3.34/0.97  --prep_def_merge_tr_cl                  false
% 3.34/0.97  --smt_preprocessing                     true
% 3.34/0.97  --smt_ac_axioms                         fast
% 3.34/0.97  --preprocessed_out                      false
% 3.34/0.97  --preprocessed_stats                    false
% 3.34/0.97  
% 3.34/0.97  ------ Abstraction refinement Options
% 3.34/0.97  
% 3.34/0.97  --abstr_ref                             []
% 3.34/0.97  --abstr_ref_prep                        false
% 3.34/0.97  --abstr_ref_until_sat                   false
% 3.34/0.97  --abstr_ref_sig_restrict                funpre
% 3.34/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 3.34/0.97  --abstr_ref_under                       []
% 3.34/0.97  
% 3.34/0.97  ------ SAT Options
% 3.34/0.97  
% 3.34/0.97  --sat_mode                              false
% 3.34/0.97  --sat_fm_restart_options                ""
% 3.34/0.97  --sat_gr_def                            false
% 3.34/0.97  --sat_epr_types                         true
% 3.34/0.97  --sat_non_cyclic_types                  false
% 3.34/0.97  --sat_finite_models                     false
% 3.34/0.97  --sat_fm_lemmas                         false
% 3.34/0.97  --sat_fm_prep                           false
% 3.34/0.97  --sat_fm_uc_incr                        true
% 3.34/0.97  --sat_out_model                         small
% 3.34/0.97  --sat_out_clauses                       false
% 3.34/0.97  
% 3.34/0.97  ------ QBF Options
% 3.34/0.97  
% 3.34/0.97  --qbf_mode                              false
% 3.34/0.97  --qbf_elim_univ                         false
% 3.34/0.97  --qbf_dom_inst                          none
% 3.34/0.97  --qbf_dom_pre_inst                      false
% 3.34/0.97  --qbf_sk_in                             false
% 3.34/0.97  --qbf_pred_elim                         true
% 3.34/0.97  --qbf_split                             512
% 3.34/0.97  
% 3.34/0.97  ------ BMC1 Options
% 3.34/0.97  
% 3.34/0.97  --bmc1_incremental                      false
% 3.34/0.97  --bmc1_axioms                           reachable_all
% 3.34/0.97  --bmc1_min_bound                        0
% 3.34/0.97  --bmc1_max_bound                        -1
% 3.34/0.97  --bmc1_max_bound_default                -1
% 3.34/0.97  --bmc1_symbol_reachability              true
% 3.34/0.97  --bmc1_property_lemmas                  false
% 3.34/0.97  --bmc1_k_induction                      false
% 3.34/0.97  --bmc1_non_equiv_states                 false
% 3.34/0.97  --bmc1_deadlock                         false
% 3.34/0.97  --bmc1_ucm                              false
% 3.34/0.97  --bmc1_add_unsat_core                   none
% 3.34/0.97  --bmc1_unsat_core_children              false
% 3.34/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 3.34/0.97  --bmc1_out_stat                         full
% 3.34/0.97  --bmc1_ground_init                      false
% 3.34/0.97  --bmc1_pre_inst_next_state              false
% 3.34/0.97  --bmc1_pre_inst_state                   false
% 3.34/0.97  --bmc1_pre_inst_reach_state             false
% 3.34/0.97  --bmc1_out_unsat_core                   false
% 3.34/0.97  --bmc1_aig_witness_out                  false
% 3.34/0.97  --bmc1_verbose                          false
% 3.34/0.97  --bmc1_dump_clauses_tptp                false
% 3.34/0.97  --bmc1_dump_unsat_core_tptp             false
% 3.34/0.97  --bmc1_dump_file                        -
% 3.34/0.97  --bmc1_ucm_expand_uc_limit              128
% 3.34/0.97  --bmc1_ucm_n_expand_iterations          6
% 3.34/0.97  --bmc1_ucm_extend_mode                  1
% 3.34/0.97  --bmc1_ucm_init_mode                    2
% 3.34/0.97  --bmc1_ucm_cone_mode                    none
% 3.34/0.97  --bmc1_ucm_reduced_relation_type        0
% 3.34/0.97  --bmc1_ucm_relax_model                  4
% 3.34/0.97  --bmc1_ucm_full_tr_after_sat            true
% 3.34/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 3.34/0.97  --bmc1_ucm_layered_model                none
% 3.34/0.97  --bmc1_ucm_max_lemma_size               10
% 3.34/0.97  
% 3.34/0.97  ------ AIG Options
% 3.34/0.97  
% 3.34/0.97  --aig_mode                              false
% 3.34/0.97  
% 3.34/0.97  ------ Instantiation Options
% 3.34/0.97  
% 3.34/0.97  --instantiation_flag                    true
% 3.34/0.97  --inst_sos_flag                         false
% 3.34/0.97  --inst_sos_phase                        true
% 3.34/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.34/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.34/0.97  --inst_lit_sel_side                     none
% 3.34/0.97  --inst_solver_per_active                1400
% 3.34/0.97  --inst_solver_calls_frac                1.
% 3.34/0.97  --inst_passive_queue_type               priority_queues
% 3.34/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.34/0.97  --inst_passive_queues_freq              [25;2]
% 3.34/0.97  --inst_dismatching                      true
% 3.34/0.97  --inst_eager_unprocessed_to_passive     true
% 3.34/0.97  --inst_prop_sim_given                   true
% 3.34/0.97  --inst_prop_sim_new                     false
% 3.34/0.97  --inst_subs_new                         false
% 3.34/0.97  --inst_eq_res_simp                      false
% 3.34/0.97  --inst_subs_given                       false
% 3.34/0.97  --inst_orphan_elimination               true
% 3.34/0.97  --inst_learning_loop_flag               true
% 3.34/0.97  --inst_learning_start                   3000
% 3.34/0.97  --inst_learning_factor                  2
% 3.34/0.97  --inst_start_prop_sim_after_learn       3
% 3.34/0.97  --inst_sel_renew                        solver
% 3.34/0.97  --inst_lit_activity_flag                true
% 3.34/0.97  --inst_restr_to_given                   false
% 3.34/0.97  --inst_activity_threshold               500
% 3.34/0.97  --inst_out_proof                        true
% 3.34/0.97  
% 3.34/0.97  ------ Resolution Options
% 3.34/0.97  
% 3.34/0.97  --resolution_flag                       false
% 3.34/0.97  --res_lit_sel                           adaptive
% 3.34/0.97  --res_lit_sel_side                      none
% 3.34/0.97  --res_ordering                          kbo
% 3.34/0.97  --res_to_prop_solver                    active
% 3.34/0.97  --res_prop_simpl_new                    false
% 3.34/0.97  --res_prop_simpl_given                  true
% 3.34/0.97  --res_passive_queue_type                priority_queues
% 3.34/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.34/0.97  --res_passive_queues_freq               [15;5]
% 3.34/0.97  --res_forward_subs                      full
% 3.34/0.97  --res_backward_subs                     full
% 3.34/0.97  --res_forward_subs_resolution           true
% 3.34/0.97  --res_backward_subs_resolution          true
% 3.34/0.97  --res_orphan_elimination                true
% 3.34/0.97  --res_time_limit                        2.
% 3.34/0.97  --res_out_proof                         true
% 3.34/0.97  
% 3.34/0.97  ------ Superposition Options
% 3.34/0.97  
% 3.34/0.97  --superposition_flag                    true
% 3.34/0.97  --sup_passive_queue_type                priority_queues
% 3.34/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.34/0.97  --sup_passive_queues_freq               [8;1;4]
% 3.34/0.97  --demod_completeness_check              fast
% 3.34/0.97  --demod_use_ground                      true
% 3.34/0.97  --sup_to_prop_solver                    passive
% 3.34/0.97  --sup_prop_simpl_new                    true
% 3.34/0.97  --sup_prop_simpl_given                  true
% 3.34/0.97  --sup_fun_splitting                     false
% 3.34/0.97  --sup_smt_interval                      50000
% 3.34/0.97  
% 3.34/0.97  ------ Superposition Simplification Setup
% 3.34/0.97  
% 3.34/0.97  --sup_indices_passive                   []
% 3.34/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.34/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 3.34/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.97  --sup_full_bw                           [BwDemod]
% 3.34/0.97  --sup_immed_triv                        [TrivRules]
% 3.34/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.34/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.97  --sup_immed_bw_main                     []
% 3.34/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 3.34/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.34/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.34/0.97  
% 3.34/0.97  ------ Combination Options
% 3.34/0.97  
% 3.34/0.97  --comb_res_mult                         3
% 3.34/0.97  --comb_sup_mult                         2
% 3.34/0.97  --comb_inst_mult                        10
% 3.34/0.97  
% 3.34/0.97  ------ Debug Options
% 3.34/0.97  
% 3.34/0.97  --dbg_backtrace                         false
% 3.34/0.97  --dbg_dump_prop_clauses                 false
% 3.34/0.97  --dbg_dump_prop_clauses_file            -
% 3.34/0.97  --dbg_out_stat                          false
% 3.34/0.97  
% 3.34/0.97  
% 3.34/0.97  
% 3.34/0.97  
% 3.34/0.97  ------ Proving...
% 3.34/0.97  
% 3.34/0.97  
% 3.34/0.97  % SZS status Theorem for theBenchmark.p
% 3.34/0.97  
% 3.34/0.97   Resolution empty clause
% 3.34/0.97  
% 3.34/0.97  % SZS output start CNFRefutation for theBenchmark.p
% 3.34/0.97  
% 3.34/0.97  fof(f23,conjecture,(
% 3.34/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f24,negated_conjecture,(
% 3.34/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.34/0.98    inference(negated_conjecture,[],[f23])).
% 3.34/0.98  
% 3.34/0.98  fof(f49,plain,(
% 3.34/0.98    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f24])).
% 3.34/0.98  
% 3.34/0.98  fof(f50,plain,(
% 3.34/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.34/0.98    inference(flattening,[],[f49])).
% 3.34/0.98  
% 3.34/0.98  fof(f60,plain,(
% 3.34/0.98    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f59,plain,(
% 3.34/0.98    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f58,plain,(
% 3.34/0.98    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.34/0.98    introduced(choice_axiom,[])).
% 3.34/0.98  
% 3.34/0.98  fof(f61,plain,(
% 3.34/0.98    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.34/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f60,f59,f58])).
% 3.34/0.98  
% 3.34/0.98  fof(f103,plain,(
% 3.34/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.34/0.98    inference(cnf_transformation,[],[f61])).
% 3.34/0.98  
% 3.34/0.98  fof(f20,axiom,(
% 3.34/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f44,plain,(
% 3.34/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.34/0.98    inference(ennf_transformation,[],[f20])).
% 3.34/0.98  
% 3.34/0.98  fof(f95,plain,(
% 3.34/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f44])).
% 3.34/0.98  
% 3.34/0.98  fof(f100,plain,(
% 3.34/0.98    l1_struct_0(sK1)),
% 3.34/0.98    inference(cnf_transformation,[],[f61])).
% 3.34/0.98  
% 3.34/0.98  fof(f98,plain,(
% 3.34/0.98    l1_struct_0(sK0)),
% 3.34/0.98    inference(cnf_transformation,[],[f61])).
% 3.34/0.98  
% 3.34/0.98  fof(f16,axiom,(
% 3.34/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f36,plain,(
% 3.34/0.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.34/0.98    inference(ennf_transformation,[],[f16])).
% 3.34/0.98  
% 3.34/0.98  fof(f37,plain,(
% 3.34/0.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.34/0.98    inference(flattening,[],[f36])).
% 3.34/0.98  
% 3.34/0.98  fof(f83,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f37])).
% 3.34/0.98  
% 3.34/0.98  fof(f21,axiom,(
% 3.34/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f45,plain,(
% 3.34/0.98    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.34/0.98    inference(ennf_transformation,[],[f21])).
% 3.34/0.98  
% 3.34/0.98  fof(f46,plain,(
% 3.34/0.98    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.34/0.98    inference(flattening,[],[f45])).
% 3.34/0.98  
% 3.34/0.98  fof(f96,plain,(
% 3.34/0.98    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f46])).
% 3.34/0.98  
% 3.34/0.98  fof(f99,plain,(
% 3.34/0.98    ~v2_struct_0(sK1)),
% 3.34/0.98    inference(cnf_transformation,[],[f61])).
% 3.34/0.98  
% 3.34/0.98  fof(f14,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f25,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.34/0.98    inference(pure_predicate_removal,[],[f14])).
% 3.34/0.98  
% 3.34/0.98  fof(f34,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f25])).
% 3.34/0.98  
% 3.34/0.98  fof(f80,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f34])).
% 3.34/0.98  
% 3.34/0.98  fof(f18,axiom,(
% 3.34/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f40,plain,(
% 3.34/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.34/0.98    inference(ennf_transformation,[],[f18])).
% 3.34/0.98  
% 3.34/0.98  fof(f41,plain,(
% 3.34/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(flattening,[],[f40])).
% 3.34/0.98  
% 3.34/0.98  fof(f57,plain,(
% 3.34/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(nnf_transformation,[],[f41])).
% 3.34/0.98  
% 3.34/0.98  fof(f90,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f57])).
% 3.34/0.98  
% 3.34/0.98  fof(f13,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f33,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f13])).
% 3.34/0.98  
% 3.34/0.98  fof(f79,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f33])).
% 3.34/0.98  
% 3.34/0.98  fof(f101,plain,(
% 3.34/0.98    v1_funct_1(sK2)),
% 3.34/0.98    inference(cnf_transformation,[],[f61])).
% 3.34/0.98  
% 3.34/0.98  fof(f102,plain,(
% 3.34/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.34/0.98    inference(cnf_transformation,[],[f61])).
% 3.34/0.98  
% 3.34/0.98  fof(f15,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f35,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f15])).
% 3.34/0.98  
% 3.34/0.98  fof(f81,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f35])).
% 3.34/0.98  
% 3.34/0.98  fof(f104,plain,(
% 3.34/0.98    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.34/0.98    inference(cnf_transformation,[],[f61])).
% 3.34/0.98  
% 3.34/0.98  fof(f19,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f42,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.34/0.98    inference(ennf_transformation,[],[f19])).
% 3.34/0.98  
% 3.34/0.98  fof(f43,plain,(
% 3.34/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.34/0.98    inference(flattening,[],[f42])).
% 3.34/0.98  
% 3.34/0.98  fof(f94,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f43])).
% 3.34/0.98  
% 3.34/0.98  fof(f105,plain,(
% 3.34/0.98    v2_funct_1(sK2)),
% 3.34/0.98    inference(cnf_transformation,[],[f61])).
% 3.34/0.98  
% 3.34/0.98  fof(f17,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f38,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(ennf_transformation,[],[f17])).
% 3.34/0.98  
% 3.34/0.98  fof(f39,plain,(
% 3.34/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(flattening,[],[f38])).
% 3.34/0.98  
% 3.34/0.98  fof(f56,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.34/0.98    inference(nnf_transformation,[],[f39])).
% 3.34/0.98  
% 3.34/0.98  fof(f84,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f56])).
% 3.34/0.98  
% 3.34/0.98  fof(f93,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f43])).
% 3.34/0.98  
% 3.34/0.98  fof(f22,axiom,(
% 3.34/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f47,plain,(
% 3.34/0.98    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.34/0.98    inference(ennf_transformation,[],[f22])).
% 3.34/0.98  
% 3.34/0.98  fof(f48,plain,(
% 3.34/0.98    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.34/0.98    inference(flattening,[],[f47])).
% 3.34/0.98  
% 3.34/0.98  fof(f97,plain,(
% 3.34/0.98    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f48])).
% 3.34/0.98  
% 3.34/0.98  fof(f106,plain,(
% 3.34/0.98    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 3.34/0.98    inference(cnf_transformation,[],[f61])).
% 3.34/0.98  
% 3.34/0.98  fof(f10,axiom,(
% 3.34/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f29,plain,(
% 3.34/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.34/0.98    inference(ennf_transformation,[],[f10])).
% 3.34/0.98  
% 3.34/0.98  fof(f30,plain,(
% 3.34/0.98    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(flattening,[],[f29])).
% 3.34/0.98  
% 3.34/0.98  fof(f75,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f30])).
% 3.34/0.98  
% 3.34/0.98  fof(f9,axiom,(
% 3.34/0.98    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f28,plain,(
% 3.34/0.98    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.34/0.98    inference(ennf_transformation,[],[f9])).
% 3.34/0.98  
% 3.34/0.98  fof(f74,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f28])).
% 3.34/0.98  
% 3.34/0.98  fof(f2,axiom,(
% 3.34/0.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f51,plain,(
% 3.34/0.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/0.98    inference(nnf_transformation,[],[f2])).
% 3.34/0.98  
% 3.34/0.98  fof(f52,plain,(
% 3.34/0.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.34/0.98    inference(flattening,[],[f51])).
% 3.34/0.98  
% 3.34/0.98  fof(f63,plain,(
% 3.34/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.34/0.98    inference(cnf_transformation,[],[f52])).
% 3.34/0.98  
% 3.34/0.98  fof(f108,plain,(
% 3.34/0.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.34/0.98    inference(equality_resolution,[],[f63])).
% 3.34/0.98  
% 3.34/0.98  fof(f12,axiom,(
% 3.34/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f31,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.34/0.98    inference(ennf_transformation,[],[f12])).
% 3.34/0.98  
% 3.34/0.98  fof(f32,plain,(
% 3.34/0.98    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.34/0.98    inference(flattening,[],[f31])).
% 3.34/0.98  
% 3.34/0.98  fof(f78,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f32])).
% 3.34/0.98  
% 3.34/0.98  fof(f5,axiom,(
% 3.34/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f55,plain,(
% 3.34/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.34/0.98    inference(nnf_transformation,[],[f5])).
% 3.34/0.98  
% 3.34/0.98  fof(f70,plain,(
% 3.34/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f55])).
% 3.34/0.98  
% 3.34/0.98  fof(f65,plain,(
% 3.34/0.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.34/0.98    inference(cnf_transformation,[],[f52])).
% 3.34/0.98  
% 3.34/0.98  fof(f3,axiom,(
% 3.34/0.98    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f53,plain,(
% 3.34/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.34/0.98    inference(nnf_transformation,[],[f3])).
% 3.34/0.98  
% 3.34/0.98  fof(f54,plain,(
% 3.34/0.98    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.34/0.98    inference(flattening,[],[f53])).
% 3.34/0.98  
% 3.34/0.98  fof(f67,plain,(
% 3.34/0.98    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X0) )),
% 3.34/0.98    inference(cnf_transformation,[],[f54])).
% 3.34/0.98  
% 3.34/0.98  fof(f110,plain,(
% 3.34/0.98    ( ! [X1] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X1)) )),
% 3.34/0.98    inference(equality_resolution,[],[f67])).
% 3.34/0.98  
% 3.34/0.98  fof(f4,axiom,(
% 3.34/0.98    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f69,plain,(
% 3.34/0.98    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.34/0.98    inference(cnf_transformation,[],[f4])).
% 3.34/0.98  
% 3.34/0.98  fof(f1,axiom,(
% 3.34/0.98    v1_xboole_0(k1_xboole_0)),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f62,plain,(
% 3.34/0.98    v1_xboole_0(k1_xboole_0)),
% 3.34/0.98    inference(cnf_transformation,[],[f1])).
% 3.34/0.98  
% 3.34/0.98  fof(f11,axiom,(
% 3.34/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 3.34/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.34/0.98  
% 3.34/0.98  fof(f77,plain,(
% 3.34/0.98    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 3.34/0.98    inference(cnf_transformation,[],[f11])).
% 3.34/0.98  
% 3.34/0.98  cnf(c_39,negated_conjecture,
% 3.34/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.34/0.98      inference(cnf_transformation,[],[f103]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1828,plain,
% 3.34/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_33,plain,
% 3.34/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f95]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_42,negated_conjecture,
% 3.34/0.98      ( l1_struct_0(sK1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f100]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_518,plain,
% 3.34/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_33,c_42]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_519,plain,
% 3.34/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.34/0.98      inference(unflattening,[status(thm)],[c_518]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_44,negated_conjecture,
% 3.34/0.98      ( l1_struct_0(sK0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f98]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_523,plain,
% 3.34/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_33,c_44]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_524,plain,
% 3.34/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.34/0.98      inference(unflattening,[status(thm)],[c_523]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1872,plain,
% 3.34/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_1828,c_519,c_524]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_20,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | v1_partfun1(X0,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | v1_xboole_0(X2) ),
% 3.34/0.98      inference(cnf_transformation,[],[f83]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_34,plain,
% 3.34/0.98      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f96]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_43,negated_conjecture,
% 3.34/0.98      ( ~ v2_struct_0(sK1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f99]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_505,plain,
% 3.34/0.98      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_34,c_43]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_506,plain,
% 3.34/0.98      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.34/0.98      inference(unflattening,[status(thm)],[c_505]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_508,plain,
% 3.34/0.98      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 3.34/0.98      inference(global_propositional_subsumption,[status(thm)],[c_506,c_42]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_534,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | v1_partfun1(X0,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k2_struct_0(sK1) != X2 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_20,c_508]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_535,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 3.34/0.98      | v1_partfun1(X0,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 3.34/0.98      | ~ v1_funct_1(X0) ),
% 3.34/0.98      inference(unflattening,[status(thm)],[c_534]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_18,plain,
% 3.34/0.98      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.34/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_29,plain,
% 3.34/0.98      ( ~ v1_partfun1(X0,X1)
% 3.34/0.98      | ~ v4_relat_1(X0,X1)
% 3.34/0.98      | ~ v1_relat_1(X0)
% 3.34/0.98      | k1_relat_1(X0) = X1 ),
% 3.34/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_558,plain,
% 3.34/0.98      ( ~ v1_partfun1(X0,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_relat_1(X0)
% 3.34/0.98      | k1_relat_1(X0) = X1 ),
% 3.34/0.98      inference(resolution,[status(thm)],[c_18,c_29]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_17,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_560,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_partfun1(X0,X1)
% 3.34/0.98      | k1_relat_1(X0) = X1 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_558,c_29,c_18,c_17]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_561,plain,
% 3.34/0.98      ( ~ v1_partfun1(X0,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | k1_relat_1(X0) = X1 ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_560]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_618,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k1_relat_1(X0) = X1 ),
% 3.34/0.98      inference(resolution,[status(thm)],[c_535,c_561]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1823,plain,
% 3.34/0.98      ( k1_relat_1(X0) = X1
% 3.34/0.98      | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
% 3.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
% 3.34/0.98      | v1_funct_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2730,plain,
% 3.34/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.34/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.34/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
% 3.34/0.98      | v1_funct_1(sK2) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1872,c_1823]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_41,negated_conjecture,
% 3.34/0.98      ( v1_funct_1(sK2) ),
% 3.34/0.98      inference(cnf_transformation,[],[f101]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_48,plain,
% 3.34/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_40,negated_conjecture,
% 3.34/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f102]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1827,plain,
% 3.34/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1866,plain,
% 3.34/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_1827,c_519,c_524]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3109,plain,
% 3.34/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top
% 3.34/0.98      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2730,c_48,c_1866]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3110,plain,
% 3.34/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.34/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) != iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_3109]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3117,plain,
% 3.34/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1872,c_3110]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3130,plain,
% 3.34/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) = iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_3117,c_1872]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_19,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f81]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1835,plain,
% 3.34/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4488,plain,
% 3.34/0.98      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_3130,c_1835]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_38,negated_conjecture,
% 3.34/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f104]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1869,plain,
% 3.34/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_38,c_519,c_524]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3132,plain,
% 3.34/0.98      ( k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_3117,c_1869]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4606,plain,
% 3.34/0.98      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_4488,c_3132]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_30,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v2_funct_1(X0)
% 3.34/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.34/0.98      inference(cnf_transformation,[],[f94]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_37,negated_conjecture,
% 3.34/0.98      ( v2_funct_1(sK2) ),
% 3.34/0.98      inference(cnf_transformation,[],[f105]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_716,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k2_relset_1(X1,X2,X0) != X2
% 3.34/0.98      | sK2 != X0 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_37]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_717,plain,
% 3.34/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 3.34/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.34/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | ~ v1_funct_1(sK2)
% 3.34/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.34/0.98      inference(unflattening,[status(thm)],[c_716]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_721,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.34/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 3.34/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.34/0.98      inference(global_propositional_subsumption,[status(thm)],[c_717,c_41]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_722,plain,
% 3.34/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 3.34/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.34/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_721]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1819,plain,
% 3.34/0.98      ( k2_relset_1(X0,X1,sK2) != X1
% 3.34/0.98      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.34/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.34/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_722]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2722,plain,
% 3.34/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.34/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 3.34/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1869,c_1819]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3039,plain,
% 3.34/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2722,c_1872,c_1866]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3126,plain,
% 3.34/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) = iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_3117,c_3039]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4716,plain,
% 3.34/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_4606,c_3126]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_27,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.34/0.98      | k1_xboole_0 = X2 ),
% 3.34/0.98      inference(cnf_transformation,[],[f84]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1829,plain,
% 3.34/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.34/0.98      | k1_xboole_0 = X1
% 3.34/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.34/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7106,plain,
% 3.34/0.98      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.34/0.98      | k1_relat_1(sK2) = k1_xboole_0
% 3.34/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_4716,c_1829]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_31,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v2_funct_1(X0)
% 3.34/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.34/0.98      inference(cnf_transformation,[],[f93]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_692,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k2_relset_1(X1,X2,X0) != X2
% 3.34/0.98      | sK2 != X0 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_31,c_37]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_693,plain,
% 3.34/0.98      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.34/0.98      | ~ v1_funct_2(sK2,X1,X0)
% 3.34/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.34/0.98      | ~ v1_funct_1(sK2)
% 3.34/0.98      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.34/0.98      inference(unflattening,[status(thm)],[c_692]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_697,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.34/0.98      | ~ v1_funct_2(sK2,X1,X0)
% 3.34/0.98      | v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.34/0.98      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.34/0.98      inference(global_propositional_subsumption,[status(thm)],[c_693,c_41]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_698,plain,
% 3.34/0.98      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.34/0.98      | ~ v1_funct_2(sK2,X1,X0)
% 3.34/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.34/0.98      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_697]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1820,plain,
% 3.34/0.98      ( k2_relset_1(X0,X1,sK2) != X1
% 3.34/0.98      | v1_funct_2(k2_funct_1(sK2),X1,X0) = iProver_top
% 3.34/0.98      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.34/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_698]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2438,plain,
% 3.34/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 3.34/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.34/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1869,c_1820]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2480,plain,
% 3.34/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2438,c_1872,c_1866]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3129,plain,
% 3.34/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k1_relat_1(sK2)) = iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_3117,c_2480]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4718,plain,
% 3.34/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_4606,c_3129]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_35,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | ~ v2_funct_1(X0)
% 3.34/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.34/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.34/0.98      inference(cnf_transformation,[],[f97]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_644,plain,
% 3.34/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.34/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_funct_1(X0)
% 3.34/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.34/0.98      | k2_relset_1(X1,X2,X0) != X2
% 3.34/0.98      | sK2 != X0 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_35,c_37]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_645,plain,
% 3.34/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 3.34/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | ~ v1_funct_1(sK2)
% 3.34/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.34/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.34/0.98      inference(unflattening,[status(thm)],[c_644]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_649,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | ~ v1_funct_2(sK2,X0,X1)
% 3.34/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.34/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.34/0.98      inference(global_propositional_subsumption,[status(thm)],[c_645,c_41]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_650,plain,
% 3.34/0.98      ( ~ v1_funct_2(sK2,X0,X1)
% 3.34/0.98      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.34/0.98      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.34/0.98      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_649]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1822,plain,
% 3.34/0.98      ( k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.34/0.98      | k2_relset_1(X0,X1,sK2) != X1
% 3.34/0.98      | v1_funct_2(sK2,X0,X1) != iProver_top
% 3.34/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_650]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2490,plain,
% 3.34/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.34/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.34/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1869,c_1822]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2563,plain,
% 3.34/0.98      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_2490,c_1872,c_1866]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_36,negated_conjecture,
% 3.34/0.98      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.34/0.98      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f106]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1977,plain,
% 3.34/0.98      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 3.34/0.98      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_36,c_519,c_524]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2566,plain,
% 3.34/0.98      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 3.34/0.98      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_2563,c_1977]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3127,plain,
% 3.34/0.98      ( k1_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_struct_0(sK1)
% 3.34/0.98      | k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_3117,c_2566]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4715,plain,
% 3.34/0.98      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.34/0.98      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_4606,c_3127]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4487,plain,
% 3.34/0.98      ( k2_relset_1(k2_struct_0(sK1),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_3126,c_1835]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5903,plain,
% 3.34/0.98      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_4487,c_4606]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6273,plain,
% 3.34/0.98      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.34/0.98      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_4715,c_5903]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_13,plain,
% 3.34/0.98      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f75]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_574,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | ~ v1_relat_1(X0)
% 3.34/0.98      | k7_relat_1(X0,X1) = X0 ),
% 3.34/0.98      inference(resolution,[status(thm)],[c_18,c_13]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_578,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.34/0.98      | k7_relat_1(X0,X1) = X0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_574,c_18,c_17,c_13]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1824,plain,
% 3.34/0.98      ( k7_relat_1(X0,X1) = X0
% 3.34/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_578]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3806,plain,
% 3.34/0.98      ( k7_relat_1(k2_funct_1(sK2),k2_struct_0(sK1)) = k2_funct_1(sK2) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_3126,c_1824]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4714,plain,
% 3.34/0.98      ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_4606,c_3806]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1836,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.34/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4111,plain,
% 3.34/0.98      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_3126,c_1836]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_12,plain,
% 3.34/0.98      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1837,plain,
% 3.34/0.98      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 3.34/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4603,plain,
% 3.34/0.98      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_4111,c_1837]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6682,plain,
% 3.34/0.98      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_4714,c_4603]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3689,plain,
% 3.34/0.98      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_3130,c_1824]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4112,plain,
% 3.34/0.98      ( v1_relat_1(sK2) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_3130,c_1836]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4520,plain,
% 3.34/0.98      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_4112,c_1837]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6348,plain,
% 3.34/0.98      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_3689,c_4520]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f108]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1842,plain,
% 3.34/0.98      ( r1_tarski(X0,X0) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_16,plain,
% 3.34/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.34/0.98      | ~ v1_funct_1(X1)
% 3.34/0.98      | ~ v2_funct_1(X1)
% 3.34/0.98      | ~ v1_relat_1(X1)
% 3.34/0.98      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_740,plain,
% 3.34/0.98      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 3.34/0.98      | ~ v1_funct_1(X1)
% 3.34/0.98      | ~ v1_relat_1(X1)
% 3.34/0.98      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0
% 3.34/0.98      | sK2 != X1 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_16,c_37]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_741,plain,
% 3.34/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.34/0.98      | ~ v1_funct_1(sK2)
% 3.34/0.98      | ~ v1_relat_1(sK2)
% 3.34/0.98      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ),
% 3.34/0.98      inference(unflattening,[status(thm)],[c_740]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_745,plain,
% 3.34/0.98      ( ~ r1_tarski(X0,k1_relat_1(sK2))
% 3.34/0.98      | ~ v1_relat_1(sK2)
% 3.34/0.98      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ),
% 3.34/0.98      inference(global_propositional_subsumption,[status(thm)],[c_741,c_41]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1818,plain,
% 3.34/0.98      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
% 3.34/0.98      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.34/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_50,plain,
% 3.34/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_747,plain,
% 3.34/0.98      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
% 3.34/0.98      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.34/0.98      | v1_relat_1(sK2) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2105,plain,
% 3.34/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.34/0.98      | v1_relat_1(sK2) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_17]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2106,plain,
% 3.34/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.34/0.98      | v1_relat_1(sK2) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2105]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2163,plain,
% 3.34/0.98      ( r1_tarski(X0,k1_relat_1(sK2)) != iProver_top
% 3.34/0.98      | k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_1818,c_50,c_747,c_2106]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2164,plain,
% 3.34/0.98      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,X0)) = X0
% 3.34/0.98      | r1_tarski(X0,k1_relat_1(sK2)) != iProver_top ),
% 3.34/0.98      inference(renaming,[status(thm)],[c_2163]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2867,plain,
% 3.34/0.98      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2) ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_1842,c_2164]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6493,plain,
% 3.34/0.98      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_6348,c_2867]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_6683,plain,
% 3.34/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_6682,c_6493]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7752,plain,
% 3.34/0.98      ( k1_relat_1(sK2) = k1_xboole_0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_7106,c_4718,c_6273,c_6683]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.34/0.98      inference(cnf_transformation,[],[f70]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1839,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.34/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3688,plain,
% 3.34/0.98      ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))) = iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_3130,c_1839]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4713,plain,
% 3.34/0.98      ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_4606,c_3688]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1,plain,
% 3.34/0.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.34/0.98      inference(cnf_transformation,[],[f65]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_1843,plain,
% 3.34/0.98      ( X0 = X1
% 3.34/0.98      | r1_tarski(X0,X1) != iProver_top
% 3.34/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5497,plain,
% 3.34/0.98      ( k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)) = sK2
% 3.34/0.98      | r1_tarski(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)),sK2) != iProver_top ),
% 3.34/0.98      inference(superposition,[status(thm)],[c_4713,c_1843]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7757,plain,
% 3.34/0.98      ( k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)) = sK2
% 3.34/0.98      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)),sK2) != iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_7752,c_5497]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_5,plain,
% 3.34/0.98      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f110]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7814,plain,
% 3.34/0.98      ( sK2 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_7757,c_5]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2519,plain,
% 3.34/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK2)) | r1_tarski(X0,sK2) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_9]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2520,plain,
% 3.34/0.98      ( m1_subset_1(X0,k1_zfmisc_1(sK2)) != iProver_top
% 3.34/0.98      | r1_tarski(X0,sK2) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2519]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2522,plain,
% 3.34/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) != iProver_top
% 3.34/0.98      | r1_tarski(k1_xboole_0,sK2) = iProver_top ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_2520]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2554,plain,
% 3.34/0.98      ( ~ r1_tarski(X0,sK2) | ~ r1_tarski(sK2,X0) | sK2 = X0 ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_1]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2555,plain,
% 3.34/0.98      ( sK2 = X0
% 3.34/0.98      | r1_tarski(X0,sK2) != iProver_top
% 3.34/0.98      | r1_tarski(sK2,X0) != iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_2554]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_2557,plain,
% 3.34/0.98      ( sK2 = k1_xboole_0
% 3.34/0.98      | r1_tarski(sK2,k1_xboole_0) != iProver_top
% 3.34/0.98      | r1_tarski(k1_xboole_0,sK2) != iProver_top ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_2555]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7,plain,
% 3.34/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.34/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3447,plain,
% 3.34/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) ),
% 3.34/0.98      inference(instantiation,[status(thm)],[c_7]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_3450,plain,
% 3.34/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(sK2)) = iProver_top ),
% 3.34/0.98      inference(predicate_to_equality,[status(thm)],[c_3447]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7767,plain,
% 3.34/0.98      ( r1_tarski(sK2,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))) = iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_7752,c_4713]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_7789,plain,
% 3.34/0.98      ( r1_tarski(sK2,k1_xboole_0) = iProver_top ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_7767,c_5]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9415,plain,
% 3.34/0.98      ( sK2 = k1_xboole_0 ),
% 3.34/0.98      inference(global_propositional_subsumption,
% 3.34/0.98                [status(thm)],
% 3.34/0.98                [c_7814,c_2522,c_2557,c_3450,c_7789]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_0,plain,
% 3.34/0.98      ( v1_xboole_0(k1_xboole_0) ),
% 3.34/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_530,plain,
% 3.34/0.98      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 3.34/0.98      inference(resolution_lifted,[status(thm)],[c_0,c_508]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_4722,plain,
% 3.34/0.98      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_4606,c_530]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9438,plain,
% 3.34/0.98      ( k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 3.34/0.98      inference(demodulation,[status(thm)],[c_9415,c_4722]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_14,plain,
% 3.34/0.98      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.34/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9498,plain,
% 3.34/0.98      ( k1_xboole_0 != k1_xboole_0 ),
% 3.34/0.98      inference(light_normalisation,[status(thm)],[c_9438,c_14]) ).
% 3.34/0.98  
% 3.34/0.98  cnf(c_9499,plain,
% 3.34/0.98      ( $false ),
% 3.34/0.98      inference(equality_resolution_simp,[status(thm)],[c_9498]) ).
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.34/0.98  
% 3.34/0.98  ------                               Statistics
% 3.34/0.98  
% 3.34/0.98  ------ General
% 3.34/0.98  
% 3.34/0.98  abstr_ref_over_cycles:                  0
% 3.34/0.98  abstr_ref_under_cycles:                 0
% 3.34/0.98  gc_basic_clause_elim:                   0
% 3.34/0.98  forced_gc_time:                         0
% 3.34/0.98  parsing_time:                           0.01
% 3.34/0.98  unif_index_cands_time:                  0.
% 3.34/0.98  unif_index_add_time:                    0.
% 3.34/0.98  orderings_time:                         0.
% 3.34/0.98  out_proof_time:                         0.016
% 3.34/0.98  total_time:                             0.3
% 3.34/0.98  num_of_symbols:                         58
% 3.34/0.98  num_of_terms:                           7995
% 3.34/0.98  
% 3.34/0.98  ------ Preprocessing
% 3.34/0.98  
% 3.34/0.98  num_of_splits:                          0
% 3.34/0.98  num_of_split_atoms:                     0
% 3.34/0.98  num_of_reused_defs:                     0
% 3.34/0.98  num_eq_ax_congr_red:                    12
% 3.34/0.98  num_of_sem_filtered_clauses:            1
% 3.34/0.98  num_of_subtypes:                        0
% 3.34/0.98  monotx_restored_types:                  0
% 3.34/0.98  sat_num_of_epr_types:                   0
% 3.34/0.98  sat_num_of_non_cyclic_types:            0
% 3.34/0.98  sat_guarded_non_collapsed_types:        0
% 3.34/0.98  num_pure_diseq_elim:                    0
% 3.34/0.98  simp_replaced_by:                       0
% 3.34/0.98  res_preprocessed:                       188
% 3.34/0.98  prep_upred:                             0
% 3.34/0.98  prep_unflattend:                        17
% 3.34/0.98  smt_new_axioms:                         0
% 3.34/0.98  pred_elim_cands:                        5
% 3.34/0.98  pred_elim:                              6
% 3.34/0.98  pred_elim_cl:                           7
% 3.34/0.98  pred_elim_cycles:                       8
% 3.34/0.98  merged_defs:                            8
% 3.34/0.98  merged_defs_ncl:                        0
% 3.34/0.98  bin_hyper_res:                          9
% 3.34/0.98  prep_cycles:                            4
% 3.34/0.98  pred_elim_time:                         0.009
% 3.34/0.98  splitting_time:                         0.
% 3.34/0.98  sem_filter_time:                        0.
% 3.34/0.98  monotx_time:                            0.
% 3.34/0.98  subtype_inf_time:                       0.
% 3.34/0.98  
% 3.34/0.98  ------ Problem properties
% 3.34/0.98  
% 3.34/0.98  clauses:                                36
% 3.34/0.98  conjectures:                            5
% 3.34/0.98  epr:                                    4
% 3.34/0.98  horn:                                   31
% 3.34/0.98  ground:                                 10
% 3.34/0.98  unary:                                  14
% 3.34/0.98  binary:                                 7
% 3.34/0.98  lits:                                   82
% 3.34/0.98  lits_eq:                                33
% 3.34/0.98  fd_pure:                                0
% 3.34/0.98  fd_pseudo:                              0
% 3.34/0.98  fd_cond:                                4
% 3.34/0.98  fd_pseudo_cond:                         2
% 3.34/0.98  ac_symbols:                             0
% 3.34/0.98  
% 3.34/0.98  ------ Propositional Solver
% 3.34/0.98  
% 3.34/0.98  prop_solver_calls:                      29
% 3.34/0.98  prop_fast_solver_calls:                 1245
% 3.34/0.98  smt_solver_calls:                       0
% 3.34/0.98  smt_fast_solver_calls:                  0
% 3.34/0.98  prop_num_of_clauses:                    3267
% 3.34/0.98  prop_preprocess_simplified:             9992
% 3.34/0.98  prop_fo_subsumed:                       25
% 3.34/0.98  prop_solver_time:                       0.
% 3.34/0.98  smt_solver_time:                        0.
% 3.34/0.98  smt_fast_solver_time:                   0.
% 3.34/0.98  prop_fast_solver_time:                  0.
% 3.34/0.98  prop_unsat_core_time:                   0.
% 3.34/0.98  
% 3.34/0.98  ------ QBF
% 3.34/0.98  
% 3.34/0.98  qbf_q_res:                              0
% 3.34/0.98  qbf_num_tautologies:                    0
% 3.34/0.98  qbf_prep_cycles:                        0
% 3.34/0.98  
% 3.34/0.98  ------ BMC1
% 3.34/0.98  
% 3.34/0.98  bmc1_current_bound:                     -1
% 3.34/0.98  bmc1_last_solved_bound:                 -1
% 3.34/0.98  bmc1_unsat_core_size:                   -1
% 3.34/0.98  bmc1_unsat_core_parents_size:           -1
% 3.34/0.98  bmc1_merge_next_fun:                    0
% 3.34/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.34/0.98  
% 3.34/0.98  ------ Instantiation
% 3.34/0.98  
% 3.34/0.98  inst_num_of_clauses:                    1191
% 3.34/0.98  inst_num_in_passive:                    516
% 3.34/0.98  inst_num_in_active:                     465
% 3.34/0.98  inst_num_in_unprocessed:                214
% 3.34/0.98  inst_num_of_loops:                      560
% 3.34/0.98  inst_num_of_learning_restarts:          0
% 3.34/0.98  inst_num_moves_active_passive:          92
% 3.34/0.98  inst_lit_activity:                      0
% 3.34/0.98  inst_lit_activity_moves:                0
% 3.34/0.98  inst_num_tautologies:                   0
% 3.34/0.98  inst_num_prop_implied:                  0
% 3.34/0.98  inst_num_existing_simplified:           0
% 3.34/0.98  inst_num_eq_res_simplified:             0
% 3.34/0.98  inst_num_child_elim:                    0
% 3.34/0.98  inst_num_of_dismatching_blockings:      298
% 3.34/0.98  inst_num_of_non_proper_insts:           1124
% 3.34/0.98  inst_num_of_duplicates:                 0
% 3.34/0.98  inst_inst_num_from_inst_to_res:         0
% 3.34/0.98  inst_dismatching_checking_time:         0.
% 3.34/0.98  
% 3.34/0.98  ------ Resolution
% 3.34/0.98  
% 3.34/0.98  res_num_of_clauses:                     0
% 3.34/0.98  res_num_in_passive:                     0
% 3.34/0.98  res_num_in_active:                      0
% 3.34/0.98  res_num_of_loops:                       192
% 3.34/0.98  res_forward_subset_subsumed:            121
% 3.34/0.98  res_backward_subset_subsumed:           16
% 3.34/0.98  res_forward_subsumed:                   0
% 3.34/0.98  res_backward_subsumed:                  0
% 3.34/0.98  res_forward_subsumption_resolution:     1
% 3.34/0.98  res_backward_subsumption_resolution:    0
% 3.34/0.98  res_clause_to_clause_subsumption:       278
% 3.34/0.98  res_orphan_elimination:                 0
% 3.34/0.98  res_tautology_del:                      75
% 3.34/0.98  res_num_eq_res_simplified:              0
% 3.34/0.98  res_num_sel_changes:                    0
% 3.34/0.98  res_moves_from_active_to_pass:          0
% 3.34/0.98  
% 3.34/0.98  ------ Superposition
% 3.34/0.98  
% 3.34/0.98  sup_time_total:                         0.
% 3.34/0.98  sup_time_generating:                    0.
% 3.34/0.98  sup_time_sim_full:                      0.
% 3.34/0.98  sup_time_sim_immed:                     0.
% 3.34/0.98  
% 3.34/0.98  sup_num_of_clauses:                     69
% 3.34/0.98  sup_num_in_active:                      34
% 3.34/0.98  sup_num_in_passive:                     35
% 3.34/0.98  sup_num_of_loops:                       111
% 3.34/0.98  sup_fw_superposition:                   72
% 3.34/0.98  sup_bw_superposition:                   53
% 3.34/0.98  sup_immediate_simplified:               39
% 3.34/0.98  sup_given_eliminated:                   0
% 3.34/0.98  comparisons_done:                       0
% 3.34/0.98  comparisons_avoided:                    0
% 3.34/0.98  
% 3.34/0.98  ------ Simplifications
% 3.34/0.98  
% 3.34/0.98  
% 3.34/0.98  sim_fw_subset_subsumed:                 16
% 3.34/0.98  sim_bw_subset_subsumed:                 3
% 3.34/0.98  sim_fw_subsumed:                        6
% 3.34/0.98  sim_bw_subsumed:                        2
% 3.34/0.98  sim_fw_subsumption_res:                 2
% 3.34/0.98  sim_bw_subsumption_res:                 0
% 3.34/0.98  sim_tautology_del:                      1
% 3.34/0.98  sim_eq_tautology_del:                   5
% 3.34/0.98  sim_eq_res_simp:                        1
% 3.34/0.98  sim_fw_demodulated:                     12
% 3.34/0.98  sim_bw_demodulated:                     76
% 3.34/0.98  sim_light_normalised:                   26
% 3.34/0.98  sim_joinable_taut:                      0
% 3.34/0.98  sim_joinable_simp:                      0
% 3.34/0.98  sim_ac_normalised:                      0
% 3.34/0.98  sim_smt_subsumption:                    0
% 3.34/0.98  
%------------------------------------------------------------------------------
