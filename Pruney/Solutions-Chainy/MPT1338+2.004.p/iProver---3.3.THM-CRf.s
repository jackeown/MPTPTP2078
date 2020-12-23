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
% DateTime   : Thu Dec  3 12:16:59 EST 2020

% Result     : Theorem 3.71s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :  251 (46481 expanded)
%              Number of clauses        :  157 (12612 expanded)
%              Number of leaves         :   27 (13078 expanded)
%              Depth                    :   32
%              Number of atoms          :  705 (316421 expanded)
%              Number of equality atoms :  309 (101152 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f106,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f100,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f36,conjecture,(
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

fof(f37,negated_conjecture,(
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
    inference(negated_conjecture,[],[f36])).

fof(f73,plain,(
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
    inference(ennf_transformation,[],[f37])).

fof(f74,plain,(
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
    inference(flattening,[],[f73])).

fof(f87,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
            | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) != k2_struct_0(X0)
          | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) != k2_struct_0(X1) )
        & v2_funct_1(sK4)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X1)
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f86,plain,(
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
            ( ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),X2)) != k2_struct_0(X0)
              | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),X2)) != k2_struct_0(sK3) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(sK3)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3))
            & v1_funct_1(X2) )
        & l1_struct_0(sK3)
        & ~ v2_struct_0(sK3) ) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,
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
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)) != k2_struct_0(sK2)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f88,plain,
    ( ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3) )
    & v2_funct_1(sK4)
    & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))
    & v1_funct_1(sK4)
    & l1_struct_0(sK3)
    & ~ v2_struct_0(sK3)
    & l1_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f74,f87,f86,f85])).

fof(f138,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f88])).

fof(f33,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f130,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f135,plain,(
    l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f88])).

fof(f133,plain,(
    l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f88])).

fof(f30,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f62])).

fof(f124,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f25,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f25])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f39])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f64])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f65])).

fof(f125,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f84])).

fof(f24,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f134,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f88])).

fof(f136,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

fof(f34,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f69])).

fof(f131,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f137,plain,(
    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f88])).

fof(f28,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f28])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f139,plain,(
    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f88])).

fof(f32,axiom,(
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

fof(f66,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f32])).

fof(f67,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f66])).

fof(f129,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f140,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

fof(f127,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f128,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f67])).

fof(f35,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f71,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f35])).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f71])).

fof(f132,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f72])).

fof(f141,plain,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f88])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f120,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f20,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f113,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f54])).

fof(f116,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f21,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f114,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f108,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f83])).

fof(f8,axiom,(
    ! [X0] :
      ( r1_tarski(X0,k1_xboole_0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f97,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ r1_tarski(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f9,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f98,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f144,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(definition_unfolding,[],[f96,f98])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f93,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f142,plain,(
    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) ),
    inference(definition_unfolding,[],[f93,f98])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f101,plain,(
    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f18,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f111,plain,(
    ! [X0] :
      ( v1_xboole_0(k2_relat_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_2501,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_16,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2492,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_10,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_2497,plain,
    ( X0 = X1
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_6078,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2501,c_2497])).

cnf(c_7204,plain,
    ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2492,c_6078])).

cnf(c_10848,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2501,c_7204])).

cnf(c_46,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_2479,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_40,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f130])).

cnf(c_49,negated_conjecture,
    ( l1_struct_0(sK3) ),
    inference(cnf_transformation,[],[f135])).

cnf(c_648,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_49])).

cnf(c_649,plain,
    ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
    inference(unflattening,[status(thm)],[c_648])).

cnf(c_51,negated_conjecture,
    ( l1_struct_0(sK2) ),
    inference(cnf_transformation,[],[f133])).

cnf(c_653,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_40,c_51])).

cnf(c_654,plain,
    ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
    inference(unflattening,[status(thm)],[c_653])).

cnf(c_2528,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2479,c_649,c_654])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f124])).

cnf(c_28,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_36,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f125])).

cnf(c_678,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_28,c_36])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_682,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_678,c_36,c_28,c_27])).

cnf(c_683,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_682])).

cnf(c_722,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_33,c_683])).

cnf(c_726,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_722,c_36,c_33,c_28,c_27])).

cnf(c_727,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_726])).

cnf(c_2473,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_727])).

cnf(c_4047,plain,
    ( k2_struct_0(sK2) = k1_relat_1(sK4)
    | v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2528,c_2473])).

cnf(c_50,negated_conjecture,
    ( ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f134])).

cnf(c_53,plain,
    ( v2_struct_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_54,plain,
    ( l1_struct_0(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_49])).

cnf(c_48,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_55,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_48])).

cnf(c_41,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f131])).

cnf(c_62,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_64,plain,
    ( v2_struct_0(sK3) = iProver_top
    | l1_struct_0(sK3) != iProver_top
    | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_62])).

cnf(c_47,negated_conjecture,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_2478,plain,
    ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_2522,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2478,c_649,c_654])).

cnf(c_4285,plain,
    ( k2_struct_0(sK2) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4047,c_53,c_54,c_55,c_64,c_2522])).

cnf(c_4294,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_struct_0(sK3)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4285,c_2528])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_2481,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6269,plain,
    ( k2_relset_1(k1_relat_1(sK4),k2_struct_0(sK3),sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4294,c_2481])).

cnf(c_45,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_2525,plain,
    ( k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_45,c_649,c_654])).

cnf(c_4296,plain,
    ( k2_relset_1(k1_relat_1(sK4),k2_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_4285,c_2525])).

cnf(c_6439,plain,
    ( k2_struct_0(sK3) = k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_6269,c_4296])).

cnf(c_37,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_44,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_925,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_37,c_44])).

cnf(c_926,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(unflattening,[status(thm)],[c_925])).

cnf(c_930,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK4,X0,X1)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_926,c_48])).

cnf(c_931,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(renaming,[status(thm)],[c_930])).

cnf(c_2469,plain,
    ( k2_relset_1(X0,X1,sK4) != X1
    | v1_funct_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_931])).

cnf(c_3293,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2525,c_2469])).

cnf(c_3653,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3293,c_2528,c_2522])).

cnf(c_4048,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_struct_0(sK3)
    | v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3653,c_2473])).

cnf(c_39,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f127])).

cnf(c_877,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_39,c_44])).

cnf(c_878,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(unflattening,[status(thm)],[c_877])).

cnf(c_882,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK4,X0,X1)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_878,c_48])).

cnf(c_883,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK4))
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(renaming,[status(thm)],[c_882])).

cnf(c_2471,plain,
    ( k2_relset_1(X0,X1,sK4) != X1
    | v1_funct_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_883])).

cnf(c_2996,plain,
    ( v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2525,c_2471])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f128])).

cnf(c_901,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_38,c_44])).

cnf(c_902,plain,
    ( v1_funct_2(k2_funct_1(sK4),X0,X1)
    | ~ v1_funct_2(sK4,X1,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(sK4)
    | k2_relset_1(X1,X0,sK4) != X0 ),
    inference(unflattening,[status(thm)],[c_901])).

cnf(c_906,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_2(sK4,X1,X0)
    | v1_funct_2(k2_funct_1(sK4),X0,X1)
    | k2_relset_1(X1,X0,sK4) != X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_902,c_48])).

cnf(c_907,plain,
    ( v1_funct_2(k2_funct_1(sK4),X0,X1)
    | ~ v1_funct_2(sK4,X1,X0)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | k2_relset_1(X1,X0,sK4) != X0 ),
    inference(renaming,[status(thm)],[c_906])).

cnf(c_2470,plain,
    ( k2_relset_1(X0,X1,sK4) != X1
    | v1_funct_2(k2_funct_1(sK4),X1,X0) = iProver_top
    | v1_funct_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_907])).

cnf(c_3075,plain,
    ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
    | v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2525,c_2470])).

cnf(c_5148,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_struct_0(sK3)
    | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4048,c_2528,c_2522,c_2996,c_3075])).

cnf(c_5152,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_struct_0(sK3)
    | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5148,c_4285])).

cnf(c_6550,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6439,c_5152])).

cnf(c_8349,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6550,c_6078])).

cnf(c_42,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f132])).

cnf(c_853,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_42,c_44])).

cnf(c_854,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK4)
    | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(unflattening,[status(thm)],[c_853])).

cnf(c_858,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_2(sK4,X0,X1)
    | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_854,c_48])).

cnf(c_859,plain,
    ( ~ v1_funct_2(sK4,X0,X1)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1 ),
    inference(renaming,[status(thm)],[c_858])).

cnf(c_2472,plain,
    ( k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
    | k2_relset_1(X0,X1,sK4) != X1
    | v1_funct_2(sK4,X0,X1) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_859])).

cnf(c_3169,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4)
    | v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2525,c_2472])).

cnf(c_3172,plain,
    ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3169,c_2528,c_2522])).

cnf(c_43,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_2651,plain,
    ( k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) != k2_struct_0(sK2)
    | k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
    inference(light_normalisation,[status(thm)],[c_43,c_649,c_654])).

cnf(c_3175,plain,
    ( k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK2)
    | k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_3172,c_2651])).

cnf(c_4291,plain,
    ( k2_relset_1(k2_struct_0(sK3),k1_relat_1(sK4),k2_funct_1(sK4)) != k1_relat_1(sK4)
    | k1_relset_1(k2_struct_0(sK3),k1_relat_1(sK4),k2_funct_1(sK4)) != k2_struct_0(sK3) ),
    inference(demodulation,[status(thm)],[c_4285,c_3175])).

cnf(c_6551,plain,
    ( k2_relset_1(k2_relat_1(sK4),k1_relat_1(sK4),k2_funct_1(sK4)) != k1_relat_1(sK4)
    | k1_relset_1(k2_relat_1(sK4),k1_relat_1(sK4),k2_funct_1(sK4)) != k2_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_6439,c_4291])).

cnf(c_4290,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k1_relat_1(sK4)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4285,c_3653])).

cnf(c_6268,plain,
    ( k2_relset_1(k2_struct_0(sK3),k1_relat_1(sK4),k2_funct_1(sK4)) = k2_relat_1(k2_funct_1(sK4)) ),
    inference(superposition,[status(thm)],[c_4290,c_2481])).

cnf(c_8051,plain,
    ( k2_relset_1(k2_relat_1(sK4),k1_relat_1(sK4),k2_funct_1(sK4)) = k2_relat_1(k2_funct_1(sK4)) ),
    inference(light_normalisation,[status(thm)],[c_6268,c_6439])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f120])).

cnf(c_2482,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6293,plain,
    ( k1_relset_1(k2_struct_0(sK3),k1_relat_1(sK4),k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
    inference(superposition,[status(thm)],[c_4290,c_2482])).

cnf(c_8176,plain,
    ( k1_relset_1(k2_relat_1(sK4),k1_relat_1(sK4),k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
    inference(light_normalisation,[status(thm)],[c_6293,c_6439])).

cnf(c_8342,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) != k1_relat_1(sK4) ),
    inference(light_normalisation,[status(thm)],[c_6551,c_8051,c_8176])).

cnf(c_8982,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | k2_relat_1(k2_funct_1(sK4)) != k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_8349,c_8342])).

cnf(c_2484,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4792,plain,
    ( v1_relat_1(k2_funct_1(sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4290,c_2484])).

cnf(c_23,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f113])).

cnf(c_2486,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5631,plain,
    ( k9_relat_1(k2_funct_1(sK4),k1_relat_1(k2_funct_1(sK4))) = k2_relat_1(k2_funct_1(sK4)) ),
    inference(superposition,[status(thm)],[c_4792,c_2486])).

cnf(c_8984,plain,
    ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = k2_relat_1(k2_funct_1(sK4))
    | k1_relat_1(sK4) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8349,c_5631])).

cnf(c_26,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_949,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_44])).

cnf(c_950,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
    inference(unflattening,[status(thm)],[c_949])).

cnf(c_954,plain,
    ( ~ v1_relat_1(sK4)
    | k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_950,c_48])).

cnf(c_2468,plain,
    ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_954])).

cnf(c_2816,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2909,plain,
    ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2468,c_48,c_46,c_950,c_2816])).

cnf(c_4793,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_4294,c_2484])).

cnf(c_24,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_2485,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_5624,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_4793,c_2485])).

cnf(c_8987,plain,
    ( k1_relat_1(sK4) = k1_xboole_0
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(demodulation,[status(thm)],[c_8984,c_2909,c_5624])).

cnf(c_8995,plain,
    ( k1_relat_1(sK4) = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8982,c_8987])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2489,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3872,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2528,c_2489])).

cnf(c_4289,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_struct_0(sK3))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4285,c_3872])).

cnf(c_6549,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6439,c_4289])).

cnf(c_9678,plain,
    ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8995,c_6549])).

cnf(c_10869,plain,
    ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10848,c_9678])).

cnf(c_8,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2498,plain,
    ( k1_xboole_0 = X0
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_12093,plain,
    ( sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_10869,c_2498])).

cnf(c_9669,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8995,c_8342])).

cnf(c_12412,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) != k2_relat_1(k1_xboole_0)
    | k2_relat_1(k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12093,c_9669])).

cnf(c_12428,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12093,c_8995])).

cnf(c_3873,plain,
    ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_3653,c_2489])).

cnf(c_4288,plain,
    ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(k2_struct_0(sK3),k1_relat_1(sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4285,c_3873])).

cnf(c_6548,plain,
    ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6439,c_4288])).

cnf(c_7,plain,
    ( ~ r1_tarski(X0,X1)
    | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
    inference(cnf_transformation,[],[f144])).

cnf(c_2499,plain,
    ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_7655,plain,
    ( k4_xboole_0(k2_funct_1(sK4),k4_xboole_0(k2_funct_1(sK4),k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4)))) = k2_funct_1(sK4) ),
    inference(superposition,[status(thm)],[c_6548,c_2499])).

cnf(c_0,plain,
    ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_8704,plain,
    ( k4_xboole_0(k2_funct_1(sK4),k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4))) = k5_xboole_0(k2_funct_1(sK4),k2_funct_1(sK4)) ),
    inference(superposition,[status(thm)],[c_7655,c_0])).

cnf(c_11,plain,
    ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_8706,plain,
    ( k4_xboole_0(k2_funct_1(sK4),k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4))) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_8704,c_11])).

cnf(c_8707,plain,
    ( k4_xboole_0(k2_funct_1(sK4),k1_xboole_0) = k2_funct_1(sK4) ),
    inference(demodulation,[status(thm)],[c_8706,c_7655])).

cnf(c_12424,plain,
    ( k4_xboole_0(k2_funct_1(k1_xboole_0),k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_12093,c_8707])).

cnf(c_10298,plain,
    ( k4_xboole_0(k2_funct_1(sK4),k2_zfmisc_1(k2_relat_1(sK4),k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_8706,c_8995])).

cnf(c_12425,plain,
    ( k4_xboole_0(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12093,c_10298])).

cnf(c_21,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_2488,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7205,plain,
    ( k2_relat_1(X0) = k1_xboole_0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2488,c_6078])).

cnf(c_7901,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2501,c_7205])).

cnf(c_12512,plain,
    ( k4_xboole_0(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12425,c_7901])).

cnf(c_12513,plain,
    ( k4_xboole_0(k2_funct_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_12512,c_10848])).

cnf(c_12515,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12424,c_12513])).

cnf(c_12595,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12412,c_12428,c_12515])).

cnf(c_12597,plain,
    ( k1_xboole_0 != k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_12595,c_7901])).

cnf(c_12598,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_12597])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:32:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
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
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.71/0.99  
% 3.71/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.71/0.99  ------ Proving...
% 3.71/0.99  ------ Problem Properties 
% 3.71/0.99  
% 3.71/0.99  
% 3.71/0.99  clauses                                 44
% 3.71/0.99  conjectures                             5
% 3.71/0.99  EPR                                     6
% 3.71/0.99  Horn                                    41
% 3.71/0.99  unary                                   13
% 3.71/0.99  binary                                  21
% 3.71/0.99  lits                                    91
% 3.71/0.99  lits eq                                 27
% 3.71/0.99  fd_pure                                 0
% 3.71/0.99  fd_pseudo                               0
% 3.71/0.99  fd_cond                                 1
% 3.71/0.99  fd_pseudo_cond                          4
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
% 3.71/0.99   Resolution empty clause
% 3.71/0.99  
% 3.71/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.71/0.99  
% 3.71/0.99  fof(f3,axiom,(
% 3.71/0.99    v1_xboole_0(k1_xboole_0)),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f92,plain,(
% 3.71/0.99    v1_xboole_0(k1_xboole_0)),
% 3.71/0.99    inference(cnf_transformation,[],[f3])).
% 3.71/0.99  
% 3.71/0.99  fof(f14,axiom,(
% 3.71/0.99    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f47,plain,(
% 3.71/0.99    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 3.71/0.99    inference(ennf_transformation,[],[f14])).
% 3.71/0.99  
% 3.71/0.99  fof(f106,plain,(
% 3.71/0.99    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f47])).
% 3.71/0.99  
% 3.71/0.99  fof(f11,axiom,(
% 3.71/0.99    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f46,plain,(
% 3.71/0.99    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 3.71/0.99    inference(ennf_transformation,[],[f11])).
% 3.71/0.99  
% 3.71/0.99  fof(f100,plain,(
% 3.71/0.99    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f46])).
% 3.71/0.99  
% 3.71/0.99  fof(f36,conjecture,(
% 3.71/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f37,negated_conjecture,(
% 3.71/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 3.71/0.99    inference(negated_conjecture,[],[f36])).
% 3.71/0.99  
% 3.71/0.99  fof(f73,plain,(
% 3.71/0.99    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.71/0.99    inference(ennf_transformation,[],[f37])).
% 3.71/0.99  
% 3.71/0.99  fof(f74,plain,(
% 3.71/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.71/0.99    inference(flattening,[],[f73])).
% 3.71/0.99  
% 3.71/0.99  fof(f87,plain,(
% 3.71/0.99    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK4)) != k2_struct_0(X1)) & v2_funct_1(sK4) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK4) = k2_struct_0(X1) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK4,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK4))) )),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f86,plain,(
% 3.71/0.99    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK3),X2)) != k2_struct_0(sK3)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK3),X2) = k2_struct_0(sK3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK3)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK3)) & v1_funct_1(X2)) & l1_struct_0(sK3) & ~v2_struct_0(sK3))) )),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f85,plain,(
% 3.71/0.99    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)) != k2_struct_0(sK2) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK2),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK2))),
% 3.71/0.99    introduced(choice_axiom,[])).
% 3.71/0.99  
% 3.71/0.99  fof(f88,plain,(
% 3.71/0.99    (((k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)) & v2_funct_1(sK4) & k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) & v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) & v1_funct_1(sK4)) & l1_struct_0(sK3) & ~v2_struct_0(sK3)) & l1_struct_0(sK2)),
% 3.71/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f74,f87,f86,f85])).
% 3.71/0.99  
% 3.71/0.99  fof(f138,plain,(
% 3.71/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))),
% 3.71/0.99    inference(cnf_transformation,[],[f88])).
% 3.71/0.99  
% 3.71/0.99  fof(f33,axiom,(
% 3.71/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.71/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/0.99  
% 3.71/0.99  fof(f68,plain,(
% 3.71/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.71/0.99    inference(ennf_transformation,[],[f33])).
% 3.71/0.99  
% 3.71/0.99  fof(f130,plain,(
% 3.71/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.71/0.99    inference(cnf_transformation,[],[f68])).
% 3.71/0.99  
% 3.71/0.99  fof(f135,plain,(
% 3.71/0.99    l1_struct_0(sK3)),
% 3.71/0.99    inference(cnf_transformation,[],[f88])).
% 3.71/0.99  
% 3.71/0.99  fof(f133,plain,(
% 3.71/0.99    l1_struct_0(sK2)),
% 3.71/0.99    inference(cnf_transformation,[],[f88])).
% 3.71/0.99  
% 3.71/0.99  fof(f30,axiom,(
% 3.71/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f62,plain,(
% 3.71/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.71/1.00    inference(ennf_transformation,[],[f30])).
% 3.71/1.00  
% 3.71/1.00  fof(f63,plain,(
% 3.71/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.71/1.00    inference(flattening,[],[f62])).
% 3.71/1.00  
% 3.71/1.00  fof(f124,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f63])).
% 3.71/1.00  
% 3.71/1.00  fof(f25,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f39,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.71/1.00    inference(pure_predicate_removal,[],[f25])).
% 3.71/1.00  
% 3.71/1.00  fof(f57,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.00    inference(ennf_transformation,[],[f39])).
% 3.71/1.00  
% 3.71/1.00  fof(f118,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f57])).
% 3.71/1.00  
% 3.71/1.00  fof(f31,axiom,(
% 3.71/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f64,plain,(
% 3.71/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.71/1.00    inference(ennf_transformation,[],[f31])).
% 3.71/1.00  
% 3.71/1.00  fof(f65,plain,(
% 3.71/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.71/1.00    inference(flattening,[],[f64])).
% 3.71/1.00  
% 3.71/1.00  fof(f84,plain,(
% 3.71/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.71/1.00    inference(nnf_transformation,[],[f65])).
% 3.71/1.00  
% 3.71/1.00  fof(f125,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f84])).
% 3.71/1.00  
% 3.71/1.00  fof(f24,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f56,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.00    inference(ennf_transformation,[],[f24])).
% 3.71/1.00  
% 3.71/1.00  fof(f117,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f56])).
% 3.71/1.00  
% 3.71/1.00  fof(f134,plain,(
% 3.71/1.00    ~v2_struct_0(sK3)),
% 3.71/1.00    inference(cnf_transformation,[],[f88])).
% 3.71/1.00  
% 3.71/1.00  fof(f136,plain,(
% 3.71/1.00    v1_funct_1(sK4)),
% 3.71/1.00    inference(cnf_transformation,[],[f88])).
% 3.71/1.00  
% 3.71/1.00  fof(f34,axiom,(
% 3.71/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f69,plain,(
% 3.71/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.71/1.00    inference(ennf_transformation,[],[f34])).
% 3.71/1.00  
% 3.71/1.00  fof(f70,plain,(
% 3.71/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.71/1.00    inference(flattening,[],[f69])).
% 3.71/1.00  
% 3.71/1.00  fof(f131,plain,(
% 3.71/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f70])).
% 3.71/1.00  
% 3.71/1.00  fof(f137,plain,(
% 3.71/1.00    v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3))),
% 3.71/1.00    inference(cnf_transformation,[],[f88])).
% 3.71/1.00  
% 3.71/1.00  fof(f28,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f60,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.00    inference(ennf_transformation,[],[f28])).
% 3.71/1.00  
% 3.71/1.00  fof(f121,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f60])).
% 3.71/1.00  
% 3.71/1.00  fof(f139,plain,(
% 3.71/1.00    k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3)),
% 3.71/1.00    inference(cnf_transformation,[],[f88])).
% 3.71/1.00  
% 3.71/1.00  fof(f32,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f66,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.71/1.00    inference(ennf_transformation,[],[f32])).
% 3.71/1.00  
% 3.71/1.00  fof(f67,plain,(
% 3.71/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.71/1.00    inference(flattening,[],[f66])).
% 3.71/1.00  
% 3.71/1.00  fof(f129,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f67])).
% 3.71/1.00  
% 3.71/1.00  fof(f140,plain,(
% 3.71/1.00    v2_funct_1(sK4)),
% 3.71/1.00    inference(cnf_transformation,[],[f88])).
% 3.71/1.00  
% 3.71/1.00  fof(f127,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f67])).
% 3.71/1.00  
% 3.71/1.00  fof(f128,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f67])).
% 3.71/1.00  
% 3.71/1.00  fof(f35,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f71,plain,(
% 3.71/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.71/1.00    inference(ennf_transformation,[],[f35])).
% 3.71/1.00  
% 3.71/1.00  fof(f72,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.71/1.00    inference(flattening,[],[f71])).
% 3.71/1.00  
% 3.71/1.00  fof(f132,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f72])).
% 3.71/1.00  
% 3.71/1.00  fof(f141,plain,(
% 3.71/1.00    k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2) | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3)),
% 3.71/1.00    inference(cnf_transformation,[],[f88])).
% 3.71/1.00  
% 3.71/1.00  fof(f27,axiom,(
% 3.71/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f59,plain,(
% 3.71/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.71/1.00    inference(ennf_transformation,[],[f27])).
% 3.71/1.00  
% 3.71/1.00  fof(f120,plain,(
% 3.71/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f59])).
% 3.71/1.00  
% 3.71/1.00  fof(f20,axiom,(
% 3.71/1.00    ! [X0] : (v1_relat_1(X0) => k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f50,plain,(
% 3.71/1.00    ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f20])).
% 3.71/1.00  
% 3.71/1.00  fof(f113,plain,(
% 3.71/1.00    ( ! [X0] : (k2_relat_1(X0) = k9_relat_1(X0,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f50])).
% 3.71/1.00  
% 3.71/1.00  fof(f23,axiom,(
% 3.71/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f54,plain,(
% 3.71/1.00    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.71/1.00    inference(ennf_transformation,[],[f23])).
% 3.71/1.00  
% 3.71/1.00  fof(f55,plain,(
% 3.71/1.00    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.71/1.00    inference(flattening,[],[f54])).
% 3.71/1.00  
% 3.71/1.00  fof(f116,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f55])).
% 3.71/1.00  
% 3.71/1.00  fof(f21,axiom,(
% 3.71/1.00    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f51,plain,(
% 3.71/1.00    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f21])).
% 3.71/1.00  
% 3.71/1.00  fof(f114,plain,(
% 3.71/1.00    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f51])).
% 3.71/1.00  
% 3.71/1.00  fof(f16,axiom,(
% 3.71/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f83,plain,(
% 3.71/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.71/1.00    inference(nnf_transformation,[],[f16])).
% 3.71/1.00  
% 3.71/1.00  fof(f108,plain,(
% 3.71/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f83])).
% 3.71/1.00  
% 3.71/1.00  fof(f8,axiom,(
% 3.71/1.00    ! [X0] : (r1_tarski(X0,k1_xboole_0) => k1_xboole_0 = X0)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f43,plain,(
% 3.71/1.00    ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0))),
% 3.71/1.00    inference(ennf_transformation,[],[f8])).
% 3.71/1.00  
% 3.71/1.00  fof(f97,plain,(
% 3.71/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~r1_tarski(X0,k1_xboole_0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f43])).
% 3.71/1.00  
% 3.71/1.00  fof(f7,axiom,(
% 3.71/1.00    ! [X0,X1] : (r1_tarski(X0,X1) => k3_xboole_0(X0,X1) = X0)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f42,plain,(
% 3.71/1.00    ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1))),
% 3.71/1.00    inference(ennf_transformation,[],[f7])).
% 3.71/1.00  
% 3.71/1.00  fof(f96,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = X0 | ~r1_tarski(X0,X1)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f42])).
% 3.71/1.00  
% 3.71/1.00  fof(f9,axiom,(
% 3.71/1.00    ! [X0,X1] : k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f98,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k4_xboole_0(X0,k4_xboole_0(X0,X1))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f9])).
% 3.71/1.00  
% 3.71/1.00  fof(f144,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 | ~r1_tarski(X0,X1)) )),
% 3.71/1.00    inference(definition_unfolding,[],[f96,f98])).
% 3.71/1.00  
% 3.71/1.00  fof(f4,axiom,(
% 3.71/1.00    ! [X0,X1] : k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f93,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k3_xboole_0(X0,X1))) )),
% 3.71/1.00    inference(cnf_transformation,[],[f4])).
% 3.71/1.00  
% 3.71/1.00  fof(f142,plain,(
% 3.71/1.00    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1)))) )),
% 3.71/1.00    inference(definition_unfolding,[],[f93,f98])).
% 3.71/1.00  
% 3.71/1.00  fof(f12,axiom,(
% 3.71/1.00    ! [X0] : k1_xboole_0 = k5_xboole_0(X0,X0)),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f101,plain,(
% 3.71/1.00    ( ! [X0] : (k1_xboole_0 = k5_xboole_0(X0,X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f12])).
% 3.71/1.00  
% 3.71/1.00  fof(f18,axiom,(
% 3.71/1.00    ! [X0] : (v1_xboole_0(X0) => v1_xboole_0(k2_relat_1(X0)))),
% 3.71/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.71/1.00  
% 3.71/1.00  fof(f49,plain,(
% 3.71/1.00    ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0))),
% 3.71/1.00    inference(ennf_transformation,[],[f18])).
% 3.71/1.00  
% 3.71/1.00  fof(f111,plain,(
% 3.71/1.00    ( ! [X0] : (v1_xboole_0(k2_relat_1(X0)) | ~v1_xboole_0(X0)) )),
% 3.71/1.00    inference(cnf_transformation,[],[f49])).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4,plain,
% 3.71/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f92]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2501,plain,
% 3.71/1.00      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_16,plain,
% 3.71/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f106]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2492,plain,
% 3.71/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.71/1.00      | v1_xboole_0(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10,plain,
% 3.71/1.00      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X1 = X0 ),
% 3.71/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2497,plain,
% 3.71/1.00      ( X0 = X1
% 3.71/1.00      | v1_xboole_0(X1) != iProver_top
% 3.71/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6078,plain,
% 3.71/1.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2501,c_2497]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7204,plain,
% 3.71/1.00      ( k2_zfmisc_1(X0,X1) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2492,c_6078]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10848,plain,
% 3.71/1.00      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2501,c_7204]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_46,negated_conjecture,
% 3.71/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) ),
% 3.71/1.00      inference(cnf_transformation,[],[f138]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2479,plain,
% 3.71/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3)))) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_40,plain,
% 3.71/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f130]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_49,negated_conjecture,
% 3.71/1.00      ( l1_struct_0(sK3) ),
% 3.71/1.00      inference(cnf_transformation,[],[f135]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_648,plain,
% 3.71/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK3 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_40,c_49]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_649,plain,
% 3.71/1.00      ( u1_struct_0(sK3) = k2_struct_0(sK3) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_648]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_51,negated_conjecture,
% 3.71/1.00      ( l1_struct_0(sK2) ),
% 3.71/1.00      inference(cnf_transformation,[],[f133]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_653,plain,
% 3.71/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK2 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_40,c_51]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_654,plain,
% 3.71/1.00      ( u1_struct_0(sK2) = k2_struct_0(sK2) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_653]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2528,plain,
% 3.71/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) = iProver_top ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_2479,c_649,c_654]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_33,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | v1_partfun1(X0,X1)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | v1_xboole_0(X2) ),
% 3.71/1.00      inference(cnf_transformation,[],[f124]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_28,plain,
% 3.71/1.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.71/1.00      inference(cnf_transformation,[],[f118]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_36,plain,
% 3.71/1.00      ( ~ v1_partfun1(X0,X1)
% 3.71/1.00      | ~ v4_relat_1(X0,X1)
% 3.71/1.00      | ~ v1_relat_1(X0)
% 3.71/1.00      | k1_relat_1(X0) = X1 ),
% 3.71/1.00      inference(cnf_transformation,[],[f125]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_678,plain,
% 3.71/1.00      ( ~ v1_partfun1(X0,X1)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ v1_relat_1(X0)
% 3.71/1.00      | k1_relat_1(X0) = X1 ),
% 3.71/1.00      inference(resolution,[status(thm)],[c_28,c_36]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_27,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f117]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_682,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ v1_partfun1(X0,X1)
% 3.71/1.00      | k1_relat_1(X0) = X1 ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_678,c_36,c_28,c_27]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_683,plain,
% 3.71/1.00      ( ~ v1_partfun1(X0,X1)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | k1_relat_1(X0) = X1 ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_682]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_722,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | v1_xboole_0(X2)
% 3.71/1.00      | k1_relat_1(X0) = X1 ),
% 3.71/1.00      inference(resolution,[status(thm)],[c_33,c_683]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_726,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | v1_xboole_0(X2)
% 3.71/1.00      | k1_relat_1(X0) = X1 ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_722,c_36,c_33,c_28,c_27]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_727,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | v1_xboole_0(X2)
% 3.71/1.00      | k1_relat_1(X0) = X1 ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_726]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2473,plain,
% 3.71/1.00      ( k1_relat_1(X0) = X1
% 3.71/1.00      | v1_funct_2(X0,X1,X2) != iProver_top
% 3.71/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/1.00      | v1_funct_1(X0) != iProver_top
% 3.71/1.00      | v1_xboole_0(X2) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_727]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4047,plain,
% 3.71/1.00      ( k2_struct_0(sK2) = k1_relat_1(sK4)
% 3.71/1.00      | v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
% 3.71/1.00      | v1_funct_1(sK4) != iProver_top
% 3.71/1.00      | v1_xboole_0(k2_struct_0(sK3)) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2528,c_2473]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_50,negated_conjecture,
% 3.71/1.00      ( ~ v2_struct_0(sK3) ),
% 3.71/1.00      inference(cnf_transformation,[],[f134]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_53,plain,
% 3.71/1.00      ( v2_struct_0(sK3) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_54,plain,
% 3.71/1.00      ( l1_struct_0(sK3) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_49]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_48,negated_conjecture,
% 3.71/1.00      ( v1_funct_1(sK4) ),
% 3.71/1.00      inference(cnf_transformation,[],[f136]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_55,plain,
% 3.71/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_48]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_41,plain,
% 3.71/1.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f131]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_62,plain,
% 3.71/1.00      ( v2_struct_0(X0) = iProver_top
% 3.71/1.00      | l1_struct_0(X0) != iProver_top
% 3.71/1.00      | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_64,plain,
% 3.71/1.00      ( v2_struct_0(sK3) = iProver_top
% 3.71/1.00      | l1_struct_0(sK3) != iProver_top
% 3.71/1.00      | v1_xboole_0(k2_struct_0(sK3)) != iProver_top ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_62]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_47,negated_conjecture,
% 3.71/1.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f137]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2478,plain,
% 3.71/1.00      ( v1_funct_2(sK4,u1_struct_0(sK2),u1_struct_0(sK3)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2522,plain,
% 3.71/1.00      ( v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) = iProver_top ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_2478,c_649,c_654]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4285,plain,
% 3.71/1.00      ( k2_struct_0(sK2) = k1_relat_1(sK4) ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_4047,c_53,c_54,c_55,c_64,c_2522]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4294,plain,
% 3.71/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK4),k2_struct_0(sK3)))) = iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_4285,c_2528]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_31,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f121]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2481,plain,
% 3.71/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.71/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6269,plain,
% 3.71/1.00      ( k2_relset_1(k1_relat_1(sK4),k2_struct_0(sK3),sK4) = k2_relat_1(sK4) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4294,c_2481]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_45,negated_conjecture,
% 3.71/1.00      ( k2_relset_1(u1_struct_0(sK2),u1_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 3.71/1.00      inference(cnf_transformation,[],[f139]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2525,plain,
% 3.71/1.00      ( k2_relset_1(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_45,c_649,c_654]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4296,plain,
% 3.71/1.00      ( k2_relset_1(k1_relat_1(sK4),k2_struct_0(sK3),sK4) = k2_struct_0(sK3) ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_4285,c_2525]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6439,plain,
% 3.71/1.00      ( k2_struct_0(sK3) = k2_relat_1(sK4) ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_6269,c_4296]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_37,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v2_funct_1(X0)
% 3.71/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.71/1.00      inference(cnf_transformation,[],[f129]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_44,negated_conjecture,
% 3.71/1.00      ( v2_funct_1(sK4) ),
% 3.71/1.00      inference(cnf_transformation,[],[f140]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_925,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.71/1.00      | sK4 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_37,c_44]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_926,plain,
% 3.71/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/1.00      | ~ v1_funct_1(sK4)
% 3.71/1.00      | k2_relset_1(X0,X1,sK4) != X1 ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_925]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_930,plain,
% 3.71/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.71/1.00      | ~ v1_funct_2(sK4,X0,X1)
% 3.71/1.00      | k2_relset_1(X0,X1,sK4) != X1 ),
% 3.71/1.00      inference(global_propositional_subsumption,[status(thm)],[c_926,c_48]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_931,plain,
% 3.71/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/1.00      | k2_relset_1(X0,X1,sK4) != X1 ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_930]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2469,plain,
% 3.71/1.00      ( k2_relset_1(X0,X1,sK4) != X1
% 3.71/1.00      | v1_funct_2(sK4,X0,X1) != iProver_top
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_931]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3293,plain,
% 3.71/1.00      ( v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
% 3.71/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) = iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2525,c_2469]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3653,plain,
% 3.71/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2)))) = iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_3293,c_2528,c_2522]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4048,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_struct_0(sK3)
% 3.71/1.00      | v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) != iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.71/1.00      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3653,c_2473]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_39,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.71/1.00      | ~ v2_funct_1(X0)
% 3.71/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.71/1.00      inference(cnf_transformation,[],[f127]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_877,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.71/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.71/1.00      | sK4 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_39,c_44]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_878,plain,
% 3.71/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK4))
% 3.71/1.00      | ~ v1_funct_1(sK4)
% 3.71/1.00      | k2_relset_1(X0,X1,sK4) != X1 ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_877]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_882,plain,
% 3.71/1.00      ( v1_funct_1(k2_funct_1(sK4))
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/1.00      | ~ v1_funct_2(sK4,X0,X1)
% 3.71/1.00      | k2_relset_1(X0,X1,sK4) != X1 ),
% 3.71/1.00      inference(global_propositional_subsumption,[status(thm)],[c_878,c_48]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_883,plain,
% 3.71/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK4))
% 3.71/1.00      | k2_relset_1(X0,X1,sK4) != X1 ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_882]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2471,plain,
% 3.71/1.00      ( k2_relset_1(X0,X1,sK4) != X1
% 3.71/1.00      | v1_funct_2(sK4,X0,X1) != iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK4)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_883]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2996,plain,
% 3.71/1.00      ( v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top
% 3.71/1.00      | v1_funct_1(k2_funct_1(sK4)) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2525,c_2471]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_38,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v2_funct_1(X0)
% 3.71/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.71/1.00      inference(cnf_transformation,[],[f128]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_901,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.71/1.00      | sK4 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_38,c_44]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_902,plain,
% 3.71/1.00      ( v1_funct_2(k2_funct_1(sK4),X0,X1)
% 3.71/1.00      | ~ v1_funct_2(sK4,X1,X0)
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.71/1.00      | ~ v1_funct_1(sK4)
% 3.71/1.00      | k2_relset_1(X1,X0,sK4) != X0 ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_901]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_906,plain,
% 3.71/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.71/1.00      | ~ v1_funct_2(sK4,X1,X0)
% 3.71/1.00      | v1_funct_2(k2_funct_1(sK4),X0,X1)
% 3.71/1.00      | k2_relset_1(X1,X0,sK4) != X0 ),
% 3.71/1.00      inference(global_propositional_subsumption,[status(thm)],[c_902,c_48]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_907,plain,
% 3.71/1.00      ( v1_funct_2(k2_funct_1(sK4),X0,X1)
% 3.71/1.00      | ~ v1_funct_2(sK4,X1,X0)
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.71/1.00      | k2_relset_1(X1,X0,sK4) != X0 ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_906]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2470,plain,
% 3.71/1.00      ( k2_relset_1(X0,X1,sK4) != X1
% 3.71/1.00      | v1_funct_2(k2_funct_1(sK4),X1,X0) = iProver_top
% 3.71/1.00      | v1_funct_2(sK4,X0,X1) != iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_907]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3075,plain,
% 3.71/1.00      ( v1_funct_2(k2_funct_1(sK4),k2_struct_0(sK3),k2_struct_0(sK2)) = iProver_top
% 3.71/1.00      | v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2525,c_2470]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5148,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_struct_0(sK3)
% 3.71/1.00      | v1_xboole_0(k2_struct_0(sK2)) = iProver_top ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_4048,c_2528,c_2522,c_2996,c_3075]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5152,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_struct_0(sK3)
% 3.71/1.00      | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_5148,c_4285]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6550,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 3.71/1.00      | v1_xboole_0(k1_relat_1(sK4)) = iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_6439,c_5152]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8349,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 3.71/1.00      | k1_relat_1(sK4) = k1_xboole_0 ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_6550,c_6078]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_42,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v2_funct_1(X0)
% 3.71/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.71/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.71/1.00      inference(cnf_transformation,[],[f132]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_853,plain,
% 3.71/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.71/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | ~ v1_funct_1(X0)
% 3.71/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.71/1.00      | k2_relset_1(X1,X2,X0) != X2
% 3.71/1.00      | sK4 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_42,c_44]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_854,plain,
% 3.71/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/1.00      | ~ v1_funct_1(sK4)
% 3.71/1.00      | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
% 3.71/1.00      | k2_relset_1(X0,X1,sK4) != X1 ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_853]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_858,plain,
% 3.71/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/1.00      | ~ v1_funct_2(sK4,X0,X1)
% 3.71/1.00      | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
% 3.71/1.00      | k2_relset_1(X0,X1,sK4) != X1 ),
% 3.71/1.00      inference(global_propositional_subsumption,[status(thm)],[c_854,c_48]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_859,plain,
% 3.71/1.00      ( ~ v1_funct_2(sK4,X0,X1)
% 3.71/1.00      | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.71/1.00      | k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
% 3.71/1.00      | k2_relset_1(X0,X1,sK4) != X1 ),
% 3.71/1.00      inference(renaming,[status(thm)],[c_858]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2472,plain,
% 3.71/1.00      ( k2_tops_2(X0,X1,sK4) = k2_funct_1(sK4)
% 3.71/1.00      | k2_relset_1(X0,X1,sK4) != X1
% 3.71/1.00      | v1_funct_2(sK4,X0,X1) != iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_859]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3169,plain,
% 3.71/1.00      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4)
% 3.71/1.00      | v1_funct_2(sK4,k2_struct_0(sK2),k2_struct_0(sK3)) != iProver_top
% 3.71/1.00      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3)))) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2525,c_2472]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3172,plain,
% 3.71/1.00      ( k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4) = k2_funct_1(sK4) ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_3169,c_2528,c_2522]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_43,negated_conjecture,
% 3.71/1.00      ( k2_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK2)
% 3.71/1.00      | k1_relset_1(u1_struct_0(sK3),u1_struct_0(sK2),k2_tops_2(u1_struct_0(sK2),u1_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
% 3.71/1.00      inference(cnf_transformation,[],[f141]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2651,plain,
% 3.71/1.00      ( k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) != k2_struct_0(sK2)
% 3.71/1.00      | k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_tops_2(k2_struct_0(sK2),k2_struct_0(sK3),sK4)) != k2_struct_0(sK3) ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_43,c_649,c_654]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3175,plain,
% 3.71/1.00      ( k2_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK2)
% 3.71/1.00      | k1_relset_1(k2_struct_0(sK3),k2_struct_0(sK2),k2_funct_1(sK4)) != k2_struct_0(sK3) ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_3172,c_2651]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4291,plain,
% 3.71/1.00      ( k2_relset_1(k2_struct_0(sK3),k1_relat_1(sK4),k2_funct_1(sK4)) != k1_relat_1(sK4)
% 3.71/1.00      | k1_relset_1(k2_struct_0(sK3),k1_relat_1(sK4),k2_funct_1(sK4)) != k2_struct_0(sK3) ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_4285,c_3175]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6551,plain,
% 3.71/1.00      ( k2_relset_1(k2_relat_1(sK4),k1_relat_1(sK4),k2_funct_1(sK4)) != k1_relat_1(sK4)
% 3.71/1.00      | k1_relset_1(k2_relat_1(sK4),k1_relat_1(sK4),k2_funct_1(sK4)) != k2_relat_1(sK4) ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_6439,c_4291]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4290,plain,
% 3.71/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK3),k1_relat_1(sK4)))) = iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_4285,c_3653]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6268,plain,
% 3.71/1.00      ( k2_relset_1(k2_struct_0(sK3),k1_relat_1(sK4),k2_funct_1(sK4)) = k2_relat_1(k2_funct_1(sK4)) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4290,c_2481]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8051,plain,
% 3.71/1.00      ( k2_relset_1(k2_relat_1(sK4),k1_relat_1(sK4),k2_funct_1(sK4)) = k2_relat_1(k2_funct_1(sK4)) ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_6268,c_6439]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_30,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.71/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f120]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2482,plain,
% 3.71/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.71/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6293,plain,
% 3.71/1.00      ( k1_relset_1(k2_struct_0(sK3),k1_relat_1(sK4),k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4290,c_2482]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8176,plain,
% 3.71/1.00      ( k1_relset_1(k2_relat_1(sK4),k1_relat_1(sK4),k2_funct_1(sK4)) = k1_relat_1(k2_funct_1(sK4)) ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_6293,c_6439]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8342,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
% 3.71/1.00      | k2_relat_1(k2_funct_1(sK4)) != k1_relat_1(sK4) ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_6551,c_8051,c_8176]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8982,plain,
% 3.71/1.00      ( k1_relat_1(sK4) = k1_xboole_0
% 3.71/1.00      | k2_relat_1(k2_funct_1(sK4)) != k1_relat_1(sK4) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_8349,c_8342]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2484,plain,
% 3.71/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.71/1.00      | v1_relat_1(X0) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4792,plain,
% 3.71/1.00      ( v1_relat_1(k2_funct_1(sK4)) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4290,c_2484]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_23,plain,
% 3.71/1.00      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f113]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2486,plain,
% 3.71/1.00      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.71/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5631,plain,
% 3.71/1.00      ( k9_relat_1(k2_funct_1(sK4),k1_relat_1(k2_funct_1(sK4))) = k2_relat_1(k2_funct_1(sK4)) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4792,c_2486]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8984,plain,
% 3.71/1.00      ( k9_relat_1(k2_funct_1(sK4),k2_relat_1(sK4)) = k2_relat_1(k2_funct_1(sK4))
% 3.71/1.00      | k1_relat_1(sK4) = k1_xboole_0 ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_8349,c_5631]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_26,plain,
% 3.71/1.00      ( ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v2_funct_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X0)
% 3.71/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f116]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_949,plain,
% 3.71/1.00      ( ~ v1_funct_1(X0)
% 3.71/1.00      | ~ v1_relat_1(X0)
% 3.71/1.00      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 3.71/1.00      | sK4 != X0 ),
% 3.71/1.00      inference(resolution_lifted,[status(thm)],[c_26,c_44]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_950,plain,
% 3.71/1.00      ( ~ v1_funct_1(sK4)
% 3.71/1.00      | ~ v1_relat_1(sK4)
% 3.71/1.00      | k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
% 3.71/1.00      inference(unflattening,[status(thm)],[c_949]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_954,plain,
% 3.71/1.00      ( ~ v1_relat_1(sK4)
% 3.71/1.00      | k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
% 3.71/1.00      inference(global_propositional_subsumption,[status(thm)],[c_950,c_48]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2468,plain,
% 3.71/1.00      ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0)
% 3.71/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_954]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2816,plain,
% 3.71/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK2),u1_struct_0(sK3))))
% 3.71/1.00      | v1_relat_1(sK4) ),
% 3.71/1.00      inference(instantiation,[status(thm)],[c_27]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2909,plain,
% 3.71/1.00      ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
% 3.71/1.00      inference(global_propositional_subsumption,
% 3.71/1.00                [status(thm)],
% 3.71/1.00                [c_2468,c_48,c_46,c_950,c_2816]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4793,plain,
% 3.71/1.00      ( v1_relat_1(sK4) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4294,c_2484]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_24,plain,
% 3.71/1.00      ( ~ v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 3.71/1.00      inference(cnf_transformation,[],[f114]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2485,plain,
% 3.71/1.00      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 3.71/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_5624,plain,
% 3.71/1.00      ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_4793,c_2485]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8987,plain,
% 3.71/1.00      ( k1_relat_1(sK4) = k1_xboole_0
% 3.71/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_8984,c_2909,c_5624]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8995,plain,
% 3.71/1.00      ( k1_relat_1(sK4) = k1_xboole_0 ),
% 3.71/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_8982,c_8987]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_19,plain,
% 3.71/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f108]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2489,plain,
% 3.71/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.71/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3872,plain,
% 3.71/1.00      ( r1_tarski(sK4,k2_zfmisc_1(k2_struct_0(sK2),k2_struct_0(sK3))) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2528,c_2489]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4289,plain,
% 3.71/1.00      ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_struct_0(sK3))) = iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_4285,c_3872]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6549,plain,
% 3.71/1.00      ( r1_tarski(sK4,k2_zfmisc_1(k1_relat_1(sK4),k2_relat_1(sK4))) = iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_6439,c_4289]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_9678,plain,
% 3.71/1.00      ( r1_tarski(sK4,k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK4))) = iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_8995,c_6549]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10869,plain,
% 3.71/1.00      ( r1_tarski(sK4,k1_xboole_0) = iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_10848,c_9678]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8,plain,
% 3.71/1.00      ( ~ r1_tarski(X0,k1_xboole_0) | k1_xboole_0 = X0 ),
% 3.71/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2498,plain,
% 3.71/1.00      ( k1_xboole_0 = X0 | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12093,plain,
% 3.71/1.00      ( sK4 = k1_xboole_0 ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_10869,c_2498]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_9669,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(sK4)) != k2_relat_1(sK4)
% 3.71/1.00      | k2_relat_1(k2_funct_1(sK4)) != k1_xboole_0 ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_8995,c_8342]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12412,plain,
% 3.71/1.00      ( k1_relat_1(k2_funct_1(k1_xboole_0)) != k2_relat_1(k1_xboole_0)
% 3.71/1.00      | k2_relat_1(k2_funct_1(k1_xboole_0)) != k1_xboole_0 ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_12093,c_9669]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12428,plain,
% 3.71/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_12093,c_8995]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_3873,plain,
% 3.71/1.00      ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(k2_struct_0(sK3),k2_struct_0(sK2))) = iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_3653,c_2489]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_4288,plain,
% 3.71/1.00      ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(k2_struct_0(sK3),k1_relat_1(sK4))) = iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_4285,c_3873]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_6548,plain,
% 3.71/1.00      ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4))) = iProver_top ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_6439,c_4288]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7,plain,
% 3.71/1.00      ( ~ r1_tarski(X0,X1) | k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0 ),
% 3.71/1.00      inference(cnf_transformation,[],[f144]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2499,plain,
% 3.71/1.00      ( k4_xboole_0(X0,k4_xboole_0(X0,X1)) = X0
% 3.71/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7655,plain,
% 3.71/1.00      ( k4_xboole_0(k2_funct_1(sK4),k4_xboole_0(k2_funct_1(sK4),k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4)))) = k2_funct_1(sK4) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_6548,c_2499]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_0,plain,
% 3.71/1.00      ( k5_xboole_0(X0,k4_xboole_0(X0,k4_xboole_0(X0,X1))) = k4_xboole_0(X0,X1) ),
% 3.71/1.00      inference(cnf_transformation,[],[f142]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8704,plain,
% 3.71/1.00      ( k4_xboole_0(k2_funct_1(sK4),k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4))) = k5_xboole_0(k2_funct_1(sK4),k2_funct_1(sK4)) ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_7655,c_0]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_11,plain,
% 3.71/1.00      ( k5_xboole_0(X0,X0) = k1_xboole_0 ),
% 3.71/1.00      inference(cnf_transformation,[],[f101]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8706,plain,
% 3.71/1.00      ( k4_xboole_0(k2_funct_1(sK4),k2_zfmisc_1(k2_relat_1(sK4),k1_relat_1(sK4))) = k1_xboole_0 ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_8704,c_11]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_8707,plain,
% 3.71/1.00      ( k4_xboole_0(k2_funct_1(sK4),k1_xboole_0) = k2_funct_1(sK4) ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_8706,c_7655]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12424,plain,
% 3.71/1.00      ( k4_xboole_0(k2_funct_1(k1_xboole_0),k1_xboole_0) = k2_funct_1(k1_xboole_0) ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_12093,c_8707]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_10298,plain,
% 3.71/1.00      ( k4_xboole_0(k2_funct_1(sK4),k2_zfmisc_1(k2_relat_1(sK4),k1_xboole_0)) = k1_xboole_0 ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_8706,c_8995]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12425,plain,
% 3.71/1.00      ( k4_xboole_0(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k2_relat_1(k1_xboole_0),k1_xboole_0)) = k1_xboole_0 ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_12093,c_10298]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_21,plain,
% 3.71/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(k2_relat_1(X0)) ),
% 3.71/1.00      inference(cnf_transformation,[],[f111]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_2488,plain,
% 3.71/1.00      ( v1_xboole_0(X0) != iProver_top
% 3.71/1.00      | v1_xboole_0(k2_relat_1(X0)) = iProver_top ),
% 3.71/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7205,plain,
% 3.71/1.00      ( k2_relat_1(X0) = k1_xboole_0 | v1_xboole_0(X0) != iProver_top ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2488,c_6078]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_7901,plain,
% 3.71/1.00      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 3.71/1.00      inference(superposition,[status(thm)],[c_2501,c_7205]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12512,plain,
% 3.71/1.00      ( k4_xboole_0(k2_funct_1(k1_xboole_0),k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_xboole_0 ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_12425,c_7901]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12513,plain,
% 3.71/1.00      ( k4_xboole_0(k2_funct_1(k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 3.71/1.00      inference(demodulation,[status(thm)],[c_12512,c_10848]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12515,plain,
% 3.71/1.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_12424,c_12513]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12595,plain,
% 3.71/1.00      ( k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_12412,c_12428,c_12515]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12597,plain,
% 3.71/1.00      ( k1_xboole_0 != k1_xboole_0 ),
% 3.71/1.00      inference(light_normalisation,[status(thm)],[c_12595,c_7901]) ).
% 3.71/1.00  
% 3.71/1.00  cnf(c_12598,plain,
% 3.71/1.00      ( $false ),
% 3.71/1.00      inference(equality_resolution_simp,[status(thm)],[c_12597]) ).
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
% 3.71/1.00  parsing_time:                           0.018
% 3.71/1.00  unif_index_cands_time:                  0.
% 3.71/1.00  unif_index_add_time:                    0.
% 3.71/1.00  orderings_time:                         0.
% 3.71/1.00  out_proof_time:                         0.016
% 3.71/1.00  total_time:                             0.33
% 3.71/1.00  num_of_symbols:                         67
% 3.71/1.00  num_of_terms:                           10653
% 3.71/1.00  
% 3.71/1.00  ------ Preprocessing
% 3.71/1.00  
% 3.71/1.00  num_of_splits:                          0
% 3.71/1.00  num_of_split_atoms:                     0
% 3.71/1.00  num_of_reused_defs:                     0
% 3.71/1.00  num_eq_ax_congr_red:                    40
% 3.71/1.00  num_of_sem_filtered_clauses:            1
% 3.71/1.00  num_of_subtypes:                        0
% 3.71/1.00  monotx_restored_types:                  0
% 3.71/1.00  sat_num_of_epr_types:                   0
% 3.71/1.00  sat_num_of_non_cyclic_types:            0
% 3.71/1.00  sat_guarded_non_collapsed_types:        0
% 3.71/1.00  num_pure_diseq_elim:                    0
% 3.71/1.00  simp_replaced_by:                       0
% 3.71/1.00  res_preprocessed:                       230
% 3.71/1.00  prep_upred:                             0
% 3.71/1.00  prep_unflattend:                        43
% 3.71/1.00  smt_new_axioms:                         0
% 3.71/1.00  pred_elim_cands:                        7
% 3.71/1.00  pred_elim:                              6
% 3.71/1.00  pred_elim_cl:                           7
% 3.71/1.00  pred_elim_cycles:                       10
% 3.71/1.00  merged_defs:                            16
% 3.71/1.00  merged_defs_ncl:                        0
% 3.71/1.00  bin_hyper_res:                          17
% 3.71/1.00  prep_cycles:                            4
% 3.71/1.00  pred_elim_time:                         0.019
% 3.71/1.00  splitting_time:                         0.
% 3.71/1.00  sem_filter_time:                        0.
% 3.71/1.00  monotx_time:                            0.001
% 3.71/1.00  subtype_inf_time:                       0.
% 3.71/1.00  
% 3.71/1.00  ------ Problem properties
% 3.71/1.00  
% 3.71/1.00  clauses:                                44
% 3.71/1.00  conjectures:                            5
% 3.71/1.00  epr:                                    6
% 3.71/1.00  horn:                                   41
% 3.71/1.00  ground:                                 10
% 3.71/1.00  unary:                                  13
% 3.71/1.00  binary:                                 21
% 3.71/1.00  lits:                                   91
% 3.71/1.00  lits_eq:                                27
% 3.71/1.00  fd_pure:                                0
% 3.71/1.00  fd_pseudo:                              0
% 3.71/1.00  fd_cond:                                1
% 3.71/1.00  fd_pseudo_cond:                         4
% 3.71/1.00  ac_symbols:                             0
% 3.71/1.00  
% 3.71/1.00  ------ Propositional Solver
% 3.71/1.00  
% 3.71/1.00  prop_solver_calls:                      27
% 3.71/1.00  prop_fast_solver_calls:                 1459
% 3.71/1.00  smt_solver_calls:                       0
% 3.71/1.00  smt_fast_solver_calls:                  0
% 3.71/1.00  prop_num_of_clauses:                    4803
% 3.71/1.00  prop_preprocess_simplified:             13122
% 3.71/1.00  prop_fo_subsumed:                       32
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
% 3.71/1.00  inst_num_of_clauses:                    1529
% 3.71/1.00  inst_num_in_passive:                    481
% 3.71/1.00  inst_num_in_active:                     660
% 3.71/1.00  inst_num_in_unprocessed:                389
% 3.71/1.00  inst_num_of_loops:                      710
% 3.71/1.00  inst_num_of_learning_restarts:          0
% 3.71/1.00  inst_num_moves_active_passive:          48
% 3.71/1.00  inst_lit_activity:                      0
% 3.71/1.00  inst_lit_activity_moves:                0
% 3.71/1.00  inst_num_tautologies:                   0
% 3.71/1.00  inst_num_prop_implied:                  0
% 3.71/1.00  inst_num_existing_simplified:           0
% 3.71/1.00  inst_num_eq_res_simplified:             0
% 3.71/1.00  inst_num_child_elim:                    0
% 3.71/1.00  inst_num_of_dismatching_blockings:      402
% 3.71/1.00  inst_num_of_non_proper_insts:           1435
% 3.71/1.00  inst_num_of_duplicates:                 0
% 3.71/1.00  inst_inst_num_from_inst_to_res:         0
% 3.71/1.00  inst_dismatching_checking_time:         0.
% 3.71/1.00  
% 3.71/1.00  ------ Resolution
% 3.71/1.00  
% 3.71/1.00  res_num_of_clauses:                     0
% 3.71/1.00  res_num_in_passive:                     0
% 3.71/1.00  res_num_in_active:                      0
% 3.71/1.00  res_num_of_loops:                       234
% 3.71/1.00  res_forward_subset_subsumed:            163
% 3.71/1.00  res_backward_subset_subsumed:           4
% 3.71/1.00  res_forward_subsumed:                   2
% 3.71/1.00  res_backward_subsumed:                  0
% 3.71/1.00  res_forward_subsumption_resolution:     1
% 3.71/1.00  res_backward_subsumption_resolution:    0
% 3.71/1.00  res_clause_to_clause_subsumption:       355
% 3.71/1.00  res_orphan_elimination:                 0
% 3.71/1.00  res_tautology_del:                      122
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
% 3.71/1.00  sup_num_of_clauses:                     109
% 3.71/1.00  sup_num_in_active:                      45
% 3.71/1.00  sup_num_in_passive:                     64
% 3.71/1.00  sup_num_of_loops:                       141
% 3.71/1.00  sup_fw_superposition:                   54
% 3.71/1.00  sup_bw_superposition:                   127
% 3.71/1.00  sup_immediate_simplified:               56
% 3.71/1.00  sup_given_eliminated:                   5
% 3.71/1.00  comparisons_done:                       0
% 3.71/1.00  comparisons_avoided:                    3
% 3.71/1.00  
% 3.71/1.00  ------ Simplifications
% 3.71/1.00  
% 3.71/1.00  
% 3.71/1.00  sim_fw_subset_subsumed:                 32
% 3.71/1.00  sim_bw_subset_subsumed:                 1
% 3.71/1.00  sim_fw_subsumed:                        6
% 3.71/1.00  sim_bw_subsumed:                        2
% 3.71/1.00  sim_fw_subsumption_res:                 1
% 3.71/1.00  sim_bw_subsumption_res:                 0
% 3.71/1.00  sim_tautology_del:                      4
% 3.71/1.00  sim_eq_tautology_del:                   8
% 3.71/1.00  sim_eq_res_simp:                        0
% 3.71/1.00  sim_fw_demodulated:                     15
% 3.71/1.00  sim_bw_demodulated:                     106
% 3.71/1.00  sim_light_normalised:                   66
% 3.71/1.00  sim_joinable_taut:                      0
% 3.71/1.00  sim_joinable_simp:                      0
% 3.71/1.00  sim_ac_normalised:                      0
% 3.71/1.00  sim_smt_subsumption:                    0
% 3.71/1.00  
%------------------------------------------------------------------------------
