%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:37 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :  192 (10560 expanded)
%              Number of clauses        :  119 (3272 expanded)
%              Number of leaves         :   18 (2939 expanded)
%              Depth                    :   29
%              Number of atoms          :  694 (66429 expanded)
%              Number of equality atoms :  238 (10745 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
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

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f46,plain,(
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

fof(f45,plain,(
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

fof(f44,plain,
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

fof(f47,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f46,f45,f44])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f67,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f70,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f27])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f6])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f76,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f63])).

fof(f78,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f52,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f54,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f55,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_613,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1036,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_19,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_350,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_351,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_350])).

cnf(c_609,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_351])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_345,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_346,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_345])).

cnf(c_610,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_346])).

cnf(c_1057,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1036,c_609,c_610])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_20,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_332,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_29])).

cnf(c_333,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_332])).

cnf(c_43,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_335,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_333,c_29,c_28,c_43])).

cnf(c_357,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_335])).

cnf(c_358,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_357])).

cnf(c_13,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_419,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_358,c_13])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_435,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_419,c_8])).

cnf(c_608,plain,
    ( ~ v1_funct_2(X0_51,X0_52,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k1_relat_1(X0_51) = X0_52 ),
    inference(subtyping,[status(esa)],[c_435])).

cnf(c_1039,plain,
    ( k1_relat_1(X0_51) = X0_52
    | v1_funct_2(X0_51,X0_52,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_1118,plain,
    ( k1_relat_1(X0_51) = X0_52
    | v1_funct_2(X0_51,X0_52,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1039,c_610])).

cnf(c_1323,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1057,c_1118])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_612,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1037,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_1051,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1037,c_609,c_610])).

cnf(c_1197,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1051])).

cnf(c_1324,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1323])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_628,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1255,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | v1_relat_1(X0_51)
    | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_1363,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1255])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_627,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1386,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_627])).

cnf(c_2124,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1323,c_27,c_25,c_1197,c_1324,c_1363,c_1386])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_620,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1030,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_1393,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1057,c_1030])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_614,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1054,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_614,c_609,c_610])).

cnf(c_1511,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1393,c_1054])).

cnf(c_1513,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1511,c_1393])).

cnf(c_2128,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2124,c_1513])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_616,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1034,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51)
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_616])).

cnf(c_2589,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2128,c_1034])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_1516,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1511,c_1057])).

cnf(c_2127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2124,c_1516])).

cnf(c_1517,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1511,c_1051])).

cnf(c_2129,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2124,c_1517])).

cnf(c_2748,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2589,c_34,c_37,c_2127,c_2129])).

cnf(c_14,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_22,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_454,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_455,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_454])).

cnf(c_607,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_455])).

cnf(c_1040,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_1177,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1040,c_609,c_610])).

cnf(c_1514,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1511,c_1177])).

cnf(c_2339,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1514,c_2124])).

cnf(c_2751,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2748,c_2339])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_626,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | v2_funct_1(k2_funct_1(X0_51))
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_667,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_funct_1(X0_51)) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_669,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_667])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_625,plain,
    ( ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_funct_1(X0_51))
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_670,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k2_funct_1(X0_51)) = iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_672,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_1364,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1363])).

cnf(c_1387,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1386])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_618,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1032,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_2590,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2128,c_1032])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_619,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1031,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_2591,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2128,c_1031])).

cnf(c_2930,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2591,c_34,c_37,c_2127,c_2129])).

cnf(c_2936,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2930,c_1030])).

cnf(c_611,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1038,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_623,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1027,plain,
    ( k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51)
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_1784,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1038,c_1027])).

cnf(c_677,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_2046,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1784,c_27,c_25,c_23,c_677,c_1363,c_1386])).

cnf(c_2943,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2936,c_2046])).

cnf(c_3109,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2943,c_1034])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_621,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k2_funct_1(k2_funct_1(X0_51)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1029,plain,
    ( k2_funct_1(k2_funct_1(X0_51)) = X0_51
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_1755,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1038,c_1029])).

cnf(c_683,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_2039,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1755,c_27,c_25,c_23,c_683,c_1363,c_1386])).

cnf(c_3129,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3109,c_2039])).

cnf(c_3633,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2751,c_34,c_36,c_37,c_669,c_672,c_1364,c_1387,c_2127,c_2129,c_2590,c_2591,c_3129])).

cnf(c_3137,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3129,c_34,c_36,c_37,c_669,c_672,c_1364,c_1387,c_2127,c_2129,c_2590,c_2591])).

cnf(c_3637,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3633,c_3137])).

cnf(c_3641,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3637,c_1038,c_2127,c_2129])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:58:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.62/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/0.99  
% 2.62/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.62/0.99  
% 2.62/0.99  ------  iProver source info
% 2.62/0.99  
% 2.62/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.62/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.62/0.99  git: non_committed_changes: false
% 2.62/0.99  git: last_make_outside_of_git: false
% 2.62/0.99  
% 2.62/0.99  ------ 
% 2.62/0.99  
% 2.62/0.99  ------ Input Options
% 2.62/0.99  
% 2.62/0.99  --out_options                           all
% 2.62/0.99  --tptp_safe_out                         true
% 2.62/0.99  --problem_path                          ""
% 2.62/0.99  --include_path                          ""
% 2.62/0.99  --clausifier                            res/vclausify_rel
% 2.62/0.99  --clausifier_options                    --mode clausify
% 2.62/0.99  --stdin                                 false
% 2.62/0.99  --stats_out                             all
% 2.62/0.99  
% 2.62/0.99  ------ General Options
% 2.62/0.99  
% 2.62/0.99  --fof                                   false
% 2.62/0.99  --time_out_real                         305.
% 2.62/0.99  --time_out_virtual                      -1.
% 2.62/0.99  --symbol_type_check                     false
% 2.62/0.99  --clausify_out                          false
% 2.62/0.99  --sig_cnt_out                           false
% 2.62/0.99  --trig_cnt_out                          false
% 2.62/0.99  --trig_cnt_out_tolerance                1.
% 2.62/0.99  --trig_cnt_out_sk_spl                   false
% 2.62/0.99  --abstr_cl_out                          false
% 2.62/0.99  
% 2.62/0.99  ------ Global Options
% 2.62/0.99  
% 2.62/0.99  --schedule                              default
% 2.62/0.99  --add_important_lit                     false
% 2.62/0.99  --prop_solver_per_cl                    1000
% 2.62/0.99  --min_unsat_core                        false
% 2.62/0.99  --soft_assumptions                      false
% 2.62/0.99  --soft_lemma_size                       3
% 2.62/0.99  --prop_impl_unit_size                   0
% 2.62/0.99  --prop_impl_unit                        []
% 2.62/0.99  --share_sel_clauses                     true
% 2.62/0.99  --reset_solvers                         false
% 2.62/0.99  --bc_imp_inh                            [conj_cone]
% 2.62/0.99  --conj_cone_tolerance                   3.
% 2.62/0.99  --extra_neg_conj                        none
% 2.62/0.99  --large_theory_mode                     true
% 2.62/0.99  --prolific_symb_bound                   200
% 2.62/0.99  --lt_threshold                          2000
% 2.62/0.99  --clause_weak_htbl                      true
% 2.62/0.99  --gc_record_bc_elim                     false
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing Options
% 2.62/0.99  
% 2.62/0.99  --preprocessing_flag                    true
% 2.62/0.99  --time_out_prep_mult                    0.1
% 2.62/0.99  --splitting_mode                        input
% 2.62/0.99  --splitting_grd                         true
% 2.62/0.99  --splitting_cvd                         false
% 2.62/0.99  --splitting_cvd_svl                     false
% 2.62/0.99  --splitting_nvd                         32
% 2.62/0.99  --sub_typing                            true
% 2.62/0.99  --prep_gs_sim                           true
% 2.62/0.99  --prep_unflatten                        true
% 2.62/0.99  --prep_res_sim                          true
% 2.62/0.99  --prep_upred                            true
% 2.62/0.99  --prep_sem_filter                       exhaustive
% 2.62/0.99  --prep_sem_filter_out                   false
% 2.62/0.99  --pred_elim                             true
% 2.62/0.99  --res_sim_input                         true
% 2.62/0.99  --eq_ax_congr_red                       true
% 2.62/0.99  --pure_diseq_elim                       true
% 2.62/0.99  --brand_transform                       false
% 2.62/0.99  --non_eq_to_eq                          false
% 2.62/0.99  --prep_def_merge                        true
% 2.62/0.99  --prep_def_merge_prop_impl              false
% 2.62/0.99  --prep_def_merge_mbd                    true
% 2.62/0.99  --prep_def_merge_tr_red                 false
% 2.62/0.99  --prep_def_merge_tr_cl                  false
% 2.62/0.99  --smt_preprocessing                     true
% 2.62/0.99  --smt_ac_axioms                         fast
% 2.62/0.99  --preprocessed_out                      false
% 2.62/0.99  --preprocessed_stats                    false
% 2.62/0.99  
% 2.62/0.99  ------ Abstraction refinement Options
% 2.62/0.99  
% 2.62/0.99  --abstr_ref                             []
% 2.62/0.99  --abstr_ref_prep                        false
% 2.62/0.99  --abstr_ref_until_sat                   false
% 2.62/0.99  --abstr_ref_sig_restrict                funpre
% 2.62/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/0.99  --abstr_ref_under                       []
% 2.62/0.99  
% 2.62/0.99  ------ SAT Options
% 2.62/0.99  
% 2.62/0.99  --sat_mode                              false
% 2.62/0.99  --sat_fm_restart_options                ""
% 2.62/0.99  --sat_gr_def                            false
% 2.62/0.99  --sat_epr_types                         true
% 2.62/0.99  --sat_non_cyclic_types                  false
% 2.62/0.99  --sat_finite_models                     false
% 2.62/0.99  --sat_fm_lemmas                         false
% 2.62/0.99  --sat_fm_prep                           false
% 2.62/0.99  --sat_fm_uc_incr                        true
% 2.62/0.99  --sat_out_model                         small
% 2.62/0.99  --sat_out_clauses                       false
% 2.62/0.99  
% 2.62/0.99  ------ QBF Options
% 2.62/0.99  
% 2.62/0.99  --qbf_mode                              false
% 2.62/0.99  --qbf_elim_univ                         false
% 2.62/0.99  --qbf_dom_inst                          none
% 2.62/0.99  --qbf_dom_pre_inst                      false
% 2.62/0.99  --qbf_sk_in                             false
% 2.62/0.99  --qbf_pred_elim                         true
% 2.62/0.99  --qbf_split                             512
% 2.62/0.99  
% 2.62/0.99  ------ BMC1 Options
% 2.62/0.99  
% 2.62/0.99  --bmc1_incremental                      false
% 2.62/0.99  --bmc1_axioms                           reachable_all
% 2.62/0.99  --bmc1_min_bound                        0
% 2.62/0.99  --bmc1_max_bound                        -1
% 2.62/0.99  --bmc1_max_bound_default                -1
% 2.62/0.99  --bmc1_symbol_reachability              true
% 2.62/0.99  --bmc1_property_lemmas                  false
% 2.62/0.99  --bmc1_k_induction                      false
% 2.62/0.99  --bmc1_non_equiv_states                 false
% 2.62/0.99  --bmc1_deadlock                         false
% 2.62/0.99  --bmc1_ucm                              false
% 2.62/0.99  --bmc1_add_unsat_core                   none
% 2.62/0.99  --bmc1_unsat_core_children              false
% 2.62/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/0.99  --bmc1_out_stat                         full
% 2.62/0.99  --bmc1_ground_init                      false
% 2.62/0.99  --bmc1_pre_inst_next_state              false
% 2.62/0.99  --bmc1_pre_inst_state                   false
% 2.62/0.99  --bmc1_pre_inst_reach_state             false
% 2.62/0.99  --bmc1_out_unsat_core                   false
% 2.62/0.99  --bmc1_aig_witness_out                  false
% 2.62/0.99  --bmc1_verbose                          false
% 2.62/0.99  --bmc1_dump_clauses_tptp                false
% 2.62/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.62/0.99  --bmc1_dump_file                        -
% 2.62/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.62/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.62/0.99  --bmc1_ucm_extend_mode                  1
% 2.62/0.99  --bmc1_ucm_init_mode                    2
% 2.62/0.99  --bmc1_ucm_cone_mode                    none
% 2.62/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.62/0.99  --bmc1_ucm_relax_model                  4
% 2.62/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.62/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/0.99  --bmc1_ucm_layered_model                none
% 2.62/0.99  --bmc1_ucm_max_lemma_size               10
% 2.62/0.99  
% 2.62/0.99  ------ AIG Options
% 2.62/0.99  
% 2.62/0.99  --aig_mode                              false
% 2.62/0.99  
% 2.62/0.99  ------ Instantiation Options
% 2.62/0.99  
% 2.62/0.99  --instantiation_flag                    true
% 2.62/0.99  --inst_sos_flag                         false
% 2.62/0.99  --inst_sos_phase                        true
% 2.62/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/0.99  --inst_lit_sel_side                     num_symb
% 2.62/0.99  --inst_solver_per_active                1400
% 2.62/0.99  --inst_solver_calls_frac                1.
% 2.62/0.99  --inst_passive_queue_type               priority_queues
% 2.62/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/0.99  --inst_passive_queues_freq              [25;2]
% 2.62/0.99  --inst_dismatching                      true
% 2.62/0.99  --inst_eager_unprocessed_to_passive     true
% 2.62/0.99  --inst_prop_sim_given                   true
% 2.62/0.99  --inst_prop_sim_new                     false
% 2.62/0.99  --inst_subs_new                         false
% 2.62/0.99  --inst_eq_res_simp                      false
% 2.62/0.99  --inst_subs_given                       false
% 2.62/0.99  --inst_orphan_elimination               true
% 2.62/0.99  --inst_learning_loop_flag               true
% 2.62/0.99  --inst_learning_start                   3000
% 2.62/0.99  --inst_learning_factor                  2
% 2.62/0.99  --inst_start_prop_sim_after_learn       3
% 2.62/0.99  --inst_sel_renew                        solver
% 2.62/0.99  --inst_lit_activity_flag                true
% 2.62/0.99  --inst_restr_to_given                   false
% 2.62/0.99  --inst_activity_threshold               500
% 2.62/0.99  --inst_out_proof                        true
% 2.62/0.99  
% 2.62/0.99  ------ Resolution Options
% 2.62/0.99  
% 2.62/0.99  --resolution_flag                       true
% 2.62/0.99  --res_lit_sel                           adaptive
% 2.62/0.99  --res_lit_sel_side                      none
% 2.62/0.99  --res_ordering                          kbo
% 2.62/0.99  --res_to_prop_solver                    active
% 2.62/0.99  --res_prop_simpl_new                    false
% 2.62/0.99  --res_prop_simpl_given                  true
% 2.62/0.99  --res_passive_queue_type                priority_queues
% 2.62/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/0.99  --res_passive_queues_freq               [15;5]
% 2.62/0.99  --res_forward_subs                      full
% 2.62/0.99  --res_backward_subs                     full
% 2.62/0.99  --res_forward_subs_resolution           true
% 2.62/0.99  --res_backward_subs_resolution          true
% 2.62/0.99  --res_orphan_elimination                true
% 2.62/0.99  --res_time_limit                        2.
% 2.62/0.99  --res_out_proof                         true
% 2.62/0.99  
% 2.62/0.99  ------ Superposition Options
% 2.62/0.99  
% 2.62/0.99  --superposition_flag                    true
% 2.62/0.99  --sup_passive_queue_type                priority_queues
% 2.62/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.62/0.99  --demod_completeness_check              fast
% 2.62/0.99  --demod_use_ground                      true
% 2.62/0.99  --sup_to_prop_solver                    passive
% 2.62/0.99  --sup_prop_simpl_new                    true
% 2.62/0.99  --sup_prop_simpl_given                  true
% 2.62/0.99  --sup_fun_splitting                     false
% 2.62/0.99  --sup_smt_interval                      50000
% 2.62/0.99  
% 2.62/0.99  ------ Superposition Simplification Setup
% 2.62/0.99  
% 2.62/0.99  --sup_indices_passive                   []
% 2.62/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_full_bw                           [BwDemod]
% 2.62/0.99  --sup_immed_triv                        [TrivRules]
% 2.62/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_immed_bw_main                     []
% 2.62/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.99  
% 2.62/0.99  ------ Combination Options
% 2.62/0.99  
% 2.62/0.99  --comb_res_mult                         3
% 2.62/0.99  --comb_sup_mult                         2
% 2.62/0.99  --comb_inst_mult                        10
% 2.62/0.99  
% 2.62/0.99  ------ Debug Options
% 2.62/0.99  
% 2.62/0.99  --dbg_backtrace                         false
% 2.62/0.99  --dbg_dump_prop_clauses                 false
% 2.62/0.99  --dbg_dump_prop_clauses_file            -
% 2.62/0.99  --dbg_out_stat                          false
% 2.62/0.99  ------ Parsing...
% 2.62/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.62/0.99  ------ Proving...
% 2.62/0.99  ------ Problem Properties 
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  clauses                                 22
% 2.62/0.99  conjectures                             5
% 2.62/0.99  EPR                                     2
% 2.62/0.99  Horn                                    22
% 2.62/0.99  unary                                   8
% 2.62/0.99  binary                                  1
% 2.62/0.99  lits                                    70
% 2.62/0.99  lits eq                                 14
% 2.62/0.99  fd_pure                                 0
% 2.62/0.99  fd_pseudo                               0
% 2.62/0.99  fd_cond                                 0
% 2.62/0.99  fd_pseudo_cond                          1
% 2.62/0.99  AC symbols                              0
% 2.62/0.99  
% 2.62/0.99  ------ Schedule dynamic 5 is on 
% 2.62/0.99  
% 2.62/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  ------ 
% 2.62/0.99  Current options:
% 2.62/0.99  ------ 
% 2.62/0.99  
% 2.62/0.99  ------ Input Options
% 2.62/0.99  
% 2.62/0.99  --out_options                           all
% 2.62/0.99  --tptp_safe_out                         true
% 2.62/0.99  --problem_path                          ""
% 2.62/0.99  --include_path                          ""
% 2.62/0.99  --clausifier                            res/vclausify_rel
% 2.62/0.99  --clausifier_options                    --mode clausify
% 2.62/0.99  --stdin                                 false
% 2.62/0.99  --stats_out                             all
% 2.62/0.99  
% 2.62/0.99  ------ General Options
% 2.62/0.99  
% 2.62/0.99  --fof                                   false
% 2.62/0.99  --time_out_real                         305.
% 2.62/0.99  --time_out_virtual                      -1.
% 2.62/0.99  --symbol_type_check                     false
% 2.62/0.99  --clausify_out                          false
% 2.62/0.99  --sig_cnt_out                           false
% 2.62/0.99  --trig_cnt_out                          false
% 2.62/0.99  --trig_cnt_out_tolerance                1.
% 2.62/0.99  --trig_cnt_out_sk_spl                   false
% 2.62/0.99  --abstr_cl_out                          false
% 2.62/0.99  
% 2.62/0.99  ------ Global Options
% 2.62/0.99  
% 2.62/0.99  --schedule                              default
% 2.62/0.99  --add_important_lit                     false
% 2.62/0.99  --prop_solver_per_cl                    1000
% 2.62/0.99  --min_unsat_core                        false
% 2.62/0.99  --soft_assumptions                      false
% 2.62/0.99  --soft_lemma_size                       3
% 2.62/0.99  --prop_impl_unit_size                   0
% 2.62/0.99  --prop_impl_unit                        []
% 2.62/0.99  --share_sel_clauses                     true
% 2.62/0.99  --reset_solvers                         false
% 2.62/0.99  --bc_imp_inh                            [conj_cone]
% 2.62/0.99  --conj_cone_tolerance                   3.
% 2.62/0.99  --extra_neg_conj                        none
% 2.62/0.99  --large_theory_mode                     true
% 2.62/0.99  --prolific_symb_bound                   200
% 2.62/0.99  --lt_threshold                          2000
% 2.62/0.99  --clause_weak_htbl                      true
% 2.62/0.99  --gc_record_bc_elim                     false
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing Options
% 2.62/0.99  
% 2.62/0.99  --preprocessing_flag                    true
% 2.62/0.99  --time_out_prep_mult                    0.1
% 2.62/0.99  --splitting_mode                        input
% 2.62/0.99  --splitting_grd                         true
% 2.62/0.99  --splitting_cvd                         false
% 2.62/0.99  --splitting_cvd_svl                     false
% 2.62/0.99  --splitting_nvd                         32
% 2.62/0.99  --sub_typing                            true
% 2.62/0.99  --prep_gs_sim                           true
% 2.62/0.99  --prep_unflatten                        true
% 2.62/0.99  --prep_res_sim                          true
% 2.62/0.99  --prep_upred                            true
% 2.62/0.99  --prep_sem_filter                       exhaustive
% 2.62/0.99  --prep_sem_filter_out                   false
% 2.62/0.99  --pred_elim                             true
% 2.62/0.99  --res_sim_input                         true
% 2.62/0.99  --eq_ax_congr_red                       true
% 2.62/0.99  --pure_diseq_elim                       true
% 2.62/0.99  --brand_transform                       false
% 2.62/0.99  --non_eq_to_eq                          false
% 2.62/0.99  --prep_def_merge                        true
% 2.62/0.99  --prep_def_merge_prop_impl              false
% 2.62/0.99  --prep_def_merge_mbd                    true
% 2.62/0.99  --prep_def_merge_tr_red                 false
% 2.62/0.99  --prep_def_merge_tr_cl                  false
% 2.62/0.99  --smt_preprocessing                     true
% 2.62/0.99  --smt_ac_axioms                         fast
% 2.62/0.99  --preprocessed_out                      false
% 2.62/0.99  --preprocessed_stats                    false
% 2.62/0.99  
% 2.62/0.99  ------ Abstraction refinement Options
% 2.62/0.99  
% 2.62/0.99  --abstr_ref                             []
% 2.62/0.99  --abstr_ref_prep                        false
% 2.62/0.99  --abstr_ref_until_sat                   false
% 2.62/0.99  --abstr_ref_sig_restrict                funpre
% 2.62/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.62/0.99  --abstr_ref_under                       []
% 2.62/0.99  
% 2.62/0.99  ------ SAT Options
% 2.62/0.99  
% 2.62/0.99  --sat_mode                              false
% 2.62/0.99  --sat_fm_restart_options                ""
% 2.62/0.99  --sat_gr_def                            false
% 2.62/0.99  --sat_epr_types                         true
% 2.62/0.99  --sat_non_cyclic_types                  false
% 2.62/0.99  --sat_finite_models                     false
% 2.62/0.99  --sat_fm_lemmas                         false
% 2.62/0.99  --sat_fm_prep                           false
% 2.62/0.99  --sat_fm_uc_incr                        true
% 2.62/0.99  --sat_out_model                         small
% 2.62/0.99  --sat_out_clauses                       false
% 2.62/0.99  
% 2.62/0.99  ------ QBF Options
% 2.62/0.99  
% 2.62/0.99  --qbf_mode                              false
% 2.62/0.99  --qbf_elim_univ                         false
% 2.62/0.99  --qbf_dom_inst                          none
% 2.62/0.99  --qbf_dom_pre_inst                      false
% 2.62/0.99  --qbf_sk_in                             false
% 2.62/0.99  --qbf_pred_elim                         true
% 2.62/0.99  --qbf_split                             512
% 2.62/0.99  
% 2.62/0.99  ------ BMC1 Options
% 2.62/0.99  
% 2.62/0.99  --bmc1_incremental                      false
% 2.62/0.99  --bmc1_axioms                           reachable_all
% 2.62/0.99  --bmc1_min_bound                        0
% 2.62/0.99  --bmc1_max_bound                        -1
% 2.62/0.99  --bmc1_max_bound_default                -1
% 2.62/0.99  --bmc1_symbol_reachability              true
% 2.62/0.99  --bmc1_property_lemmas                  false
% 2.62/0.99  --bmc1_k_induction                      false
% 2.62/0.99  --bmc1_non_equiv_states                 false
% 2.62/0.99  --bmc1_deadlock                         false
% 2.62/0.99  --bmc1_ucm                              false
% 2.62/0.99  --bmc1_add_unsat_core                   none
% 2.62/0.99  --bmc1_unsat_core_children              false
% 2.62/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.62/0.99  --bmc1_out_stat                         full
% 2.62/0.99  --bmc1_ground_init                      false
% 2.62/0.99  --bmc1_pre_inst_next_state              false
% 2.62/0.99  --bmc1_pre_inst_state                   false
% 2.62/0.99  --bmc1_pre_inst_reach_state             false
% 2.62/0.99  --bmc1_out_unsat_core                   false
% 2.62/0.99  --bmc1_aig_witness_out                  false
% 2.62/0.99  --bmc1_verbose                          false
% 2.62/0.99  --bmc1_dump_clauses_tptp                false
% 2.62/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.62/0.99  --bmc1_dump_file                        -
% 2.62/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.62/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.62/0.99  --bmc1_ucm_extend_mode                  1
% 2.62/0.99  --bmc1_ucm_init_mode                    2
% 2.62/0.99  --bmc1_ucm_cone_mode                    none
% 2.62/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.62/0.99  --bmc1_ucm_relax_model                  4
% 2.62/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.62/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.62/0.99  --bmc1_ucm_layered_model                none
% 2.62/0.99  --bmc1_ucm_max_lemma_size               10
% 2.62/0.99  
% 2.62/0.99  ------ AIG Options
% 2.62/0.99  
% 2.62/0.99  --aig_mode                              false
% 2.62/0.99  
% 2.62/0.99  ------ Instantiation Options
% 2.62/0.99  
% 2.62/0.99  --instantiation_flag                    true
% 2.62/0.99  --inst_sos_flag                         false
% 2.62/0.99  --inst_sos_phase                        true
% 2.62/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.62/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.62/0.99  --inst_lit_sel_side                     none
% 2.62/0.99  --inst_solver_per_active                1400
% 2.62/0.99  --inst_solver_calls_frac                1.
% 2.62/0.99  --inst_passive_queue_type               priority_queues
% 2.62/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.62/0.99  --inst_passive_queues_freq              [25;2]
% 2.62/0.99  --inst_dismatching                      true
% 2.62/0.99  --inst_eager_unprocessed_to_passive     true
% 2.62/0.99  --inst_prop_sim_given                   true
% 2.62/0.99  --inst_prop_sim_new                     false
% 2.62/0.99  --inst_subs_new                         false
% 2.62/0.99  --inst_eq_res_simp                      false
% 2.62/0.99  --inst_subs_given                       false
% 2.62/0.99  --inst_orphan_elimination               true
% 2.62/0.99  --inst_learning_loop_flag               true
% 2.62/0.99  --inst_learning_start                   3000
% 2.62/0.99  --inst_learning_factor                  2
% 2.62/0.99  --inst_start_prop_sim_after_learn       3
% 2.62/0.99  --inst_sel_renew                        solver
% 2.62/0.99  --inst_lit_activity_flag                true
% 2.62/0.99  --inst_restr_to_given                   false
% 2.62/0.99  --inst_activity_threshold               500
% 2.62/0.99  --inst_out_proof                        true
% 2.62/0.99  
% 2.62/0.99  ------ Resolution Options
% 2.62/0.99  
% 2.62/0.99  --resolution_flag                       false
% 2.62/0.99  --res_lit_sel                           adaptive
% 2.62/0.99  --res_lit_sel_side                      none
% 2.62/0.99  --res_ordering                          kbo
% 2.62/0.99  --res_to_prop_solver                    active
% 2.62/0.99  --res_prop_simpl_new                    false
% 2.62/0.99  --res_prop_simpl_given                  true
% 2.62/0.99  --res_passive_queue_type                priority_queues
% 2.62/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.62/0.99  --res_passive_queues_freq               [15;5]
% 2.62/0.99  --res_forward_subs                      full
% 2.62/0.99  --res_backward_subs                     full
% 2.62/0.99  --res_forward_subs_resolution           true
% 2.62/0.99  --res_backward_subs_resolution          true
% 2.62/0.99  --res_orphan_elimination                true
% 2.62/0.99  --res_time_limit                        2.
% 2.62/0.99  --res_out_proof                         true
% 2.62/0.99  
% 2.62/0.99  ------ Superposition Options
% 2.62/0.99  
% 2.62/0.99  --superposition_flag                    true
% 2.62/0.99  --sup_passive_queue_type                priority_queues
% 2.62/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.62/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.62/0.99  --demod_completeness_check              fast
% 2.62/0.99  --demod_use_ground                      true
% 2.62/0.99  --sup_to_prop_solver                    passive
% 2.62/0.99  --sup_prop_simpl_new                    true
% 2.62/0.99  --sup_prop_simpl_given                  true
% 2.62/0.99  --sup_fun_splitting                     false
% 2.62/0.99  --sup_smt_interval                      50000
% 2.62/0.99  
% 2.62/0.99  ------ Superposition Simplification Setup
% 2.62/0.99  
% 2.62/0.99  --sup_indices_passive                   []
% 2.62/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.62/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.62/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_full_bw                           [BwDemod]
% 2.62/0.99  --sup_immed_triv                        [TrivRules]
% 2.62/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.62/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_immed_bw_main                     []
% 2.62/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.62/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.62/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.62/0.99  
% 2.62/0.99  ------ Combination Options
% 2.62/0.99  
% 2.62/0.99  --comb_res_mult                         3
% 2.62/0.99  --comb_sup_mult                         2
% 2.62/0.99  --comb_inst_mult                        10
% 2.62/0.99  
% 2.62/0.99  ------ Debug Options
% 2.62/0.99  
% 2.62/0.99  --dbg_backtrace                         false
% 2.62/0.99  --dbg_dump_prop_clauses                 false
% 2.62/0.99  --dbg_dump_prop_clauses_file            -
% 2.62/0.99  --dbg_out_stat                          false
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  ------ Proving...
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  % SZS status Theorem for theBenchmark.p
% 2.62/0.99  
% 2.62/0.99   Resolution empty clause
% 2.62/0.99  
% 2.62/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.62/0.99  
% 2.62/0.99  fof(f15,conjecture,(
% 2.62/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f16,negated_conjecture,(
% 2.62/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.62/0.99    inference(negated_conjecture,[],[f15])).
% 2.62/0.99  
% 2.62/0.99  fof(f40,plain,(
% 2.62/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.62/0.99    inference(ennf_transformation,[],[f16])).
% 2.62/0.99  
% 2.62/0.99  fof(f41,plain,(
% 2.62/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.62/0.99    inference(flattening,[],[f40])).
% 2.62/0.99  
% 2.62/0.99  fof(f46,plain,(
% 2.62/0.99    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.62/0.99    introduced(choice_axiom,[])).
% 2.62/0.99  
% 2.62/0.99  fof(f45,plain,(
% 2.62/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.62/0.99    introduced(choice_axiom,[])).
% 2.62/0.99  
% 2.62/0.99  fof(f44,plain,(
% 2.62/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.62/0.99    introduced(choice_axiom,[])).
% 2.62/0.99  
% 2.62/0.99  fof(f47,plain,(
% 2.62/0.99    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.62/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f46,f45,f44])).
% 2.62/0.99  
% 2.62/0.99  fof(f75,plain,(
% 2.62/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.62/0.99    inference(cnf_transformation,[],[f47])).
% 2.62/0.99  
% 2.62/0.99  fof(f12,axiom,(
% 2.62/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f35,plain,(
% 2.62/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.62/0.99    inference(ennf_transformation,[],[f12])).
% 2.62/0.99  
% 2.62/0.99  fof(f67,plain,(
% 2.62/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f35])).
% 2.62/0.99  
% 2.62/0.99  fof(f70,plain,(
% 2.62/0.99    l1_struct_0(sK0)),
% 2.62/0.99    inference(cnf_transformation,[],[f47])).
% 2.62/0.99  
% 2.62/0.99  fof(f72,plain,(
% 2.62/0.99    l1_struct_0(sK1)),
% 2.62/0.99    inference(cnf_transformation,[],[f47])).
% 2.62/0.99  
% 2.62/0.99  fof(f8,axiom,(
% 2.62/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f27,plain,(
% 2.62/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.62/0.99    inference(ennf_transformation,[],[f8])).
% 2.62/0.99  
% 2.62/0.99  fof(f28,plain,(
% 2.62/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.62/0.99    inference(flattening,[],[f27])).
% 2.62/0.99  
% 2.62/0.99  fof(f59,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f28])).
% 2.62/0.99  
% 2.62/0.99  fof(f13,axiom,(
% 2.62/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f36,plain,(
% 2.62/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.62/0.99    inference(ennf_transformation,[],[f13])).
% 2.62/0.99  
% 2.62/0.99  fof(f37,plain,(
% 2.62/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.62/0.99    inference(flattening,[],[f36])).
% 2.62/0.99  
% 2.62/0.99  fof(f68,plain,(
% 2.62/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f37])).
% 2.62/0.99  
% 2.62/0.99  fof(f71,plain,(
% 2.62/0.99    ~v2_struct_0(sK1)),
% 2.62/0.99    inference(cnf_transformation,[],[f47])).
% 2.62/0.99  
% 2.62/0.99  fof(f9,axiom,(
% 2.62/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f29,plain,(
% 2.62/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.62/0.99    inference(ennf_transformation,[],[f9])).
% 2.62/0.99  
% 2.62/0.99  fof(f30,plain,(
% 2.62/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(flattening,[],[f29])).
% 2.62/0.99  
% 2.62/0.99  fof(f42,plain,(
% 2.62/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.62/0.99    inference(nnf_transformation,[],[f30])).
% 2.62/0.99  
% 2.62/0.99  fof(f60,plain,(
% 2.62/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f42])).
% 2.62/0.99  
% 2.62/0.99  fof(f6,axiom,(
% 2.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f17,plain,(
% 2.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.62/0.99    inference(pure_predicate_removal,[],[f6])).
% 2.62/0.99  
% 2.62/0.99  fof(f25,plain,(
% 2.62/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/0.99    inference(ennf_transformation,[],[f17])).
% 2.62/0.99  
% 2.62/0.99  fof(f56,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f25])).
% 2.62/0.99  
% 2.62/0.99  fof(f73,plain,(
% 2.62/0.99    v1_funct_1(sK2)),
% 2.62/0.99    inference(cnf_transformation,[],[f47])).
% 2.62/0.99  
% 2.62/0.99  fof(f74,plain,(
% 2.62/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.62/0.99    inference(cnf_transformation,[],[f47])).
% 2.62/0.99  
% 2.62/0.99  fof(f1,axiom,(
% 2.62/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f18,plain,(
% 2.62/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.62/0.99    inference(ennf_transformation,[],[f1])).
% 2.62/0.99  
% 2.62/0.99  fof(f48,plain,(
% 2.62/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f18])).
% 2.62/0.99  
% 2.62/0.99  fof(f2,axiom,(
% 2.62/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f49,plain,(
% 2.62/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f2])).
% 2.62/0.99  
% 2.62/0.99  fof(f7,axiom,(
% 2.62/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f26,plain,(
% 2.62/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.62/0.99    inference(ennf_transformation,[],[f7])).
% 2.62/0.99  
% 2.62/0.99  fof(f57,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.62/0.99    inference(cnf_transformation,[],[f26])).
% 2.62/0.99  
% 2.62/0.99  fof(f76,plain,(
% 2.62/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.62/0.99    inference(cnf_transformation,[],[f47])).
% 2.62/0.99  
% 2.62/0.99  fof(f14,axiom,(
% 2.62/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f38,plain,(
% 2.62/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.62/0.99    inference(ennf_transformation,[],[f14])).
% 2.62/0.99  
% 2.62/0.99  fof(f39,plain,(
% 2.62/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.62/0.99    inference(flattening,[],[f38])).
% 2.62/0.99  
% 2.62/0.99  fof(f69,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f39])).
% 2.62/0.99  
% 2.62/0.99  fof(f77,plain,(
% 2.62/0.99    v2_funct_1(sK2)),
% 2.62/0.99    inference(cnf_transformation,[],[f47])).
% 2.62/0.99  
% 2.62/0.99  fof(f10,axiom,(
% 2.62/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f31,plain,(
% 2.62/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.62/0.99    inference(ennf_transformation,[],[f10])).
% 2.62/0.99  
% 2.62/0.99  fof(f32,plain,(
% 2.62/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.62/0.99    inference(flattening,[],[f31])).
% 2.62/0.99  
% 2.62/0.99  fof(f43,plain,(
% 2.62/0.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.62/0.99    inference(nnf_transformation,[],[f32])).
% 2.62/0.99  
% 2.62/0.99  fof(f63,plain,(
% 2.62/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f43])).
% 2.62/0.99  
% 2.62/0.99  fof(f80,plain,(
% 2.62/0.99    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.62/0.99    inference(equality_resolution,[],[f63])).
% 2.62/0.99  
% 2.62/0.99  fof(f78,plain,(
% 2.62/0.99    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.62/0.99    inference(cnf_transformation,[],[f47])).
% 2.62/0.99  
% 2.62/0.99  fof(f3,axiom,(
% 2.62/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f19,plain,(
% 2.62/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.62/0.99    inference(ennf_transformation,[],[f3])).
% 2.62/0.99  
% 2.62/0.99  fof(f20,plain,(
% 2.62/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.62/0.99    inference(flattening,[],[f19])).
% 2.62/0.99  
% 2.62/0.99  fof(f52,plain,(
% 2.62/0.99    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f20])).
% 2.62/0.99  
% 2.62/0.99  fof(f51,plain,(
% 2.62/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f20])).
% 2.62/0.99  
% 2.62/0.99  fof(f11,axiom,(
% 2.62/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f33,plain,(
% 2.62/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.62/0.99    inference(ennf_transformation,[],[f11])).
% 2.62/0.99  
% 2.62/0.99  fof(f34,plain,(
% 2.62/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.62/0.99    inference(flattening,[],[f33])).
% 2.62/0.99  
% 2.62/0.99  fof(f65,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f34])).
% 2.62/0.99  
% 2.62/0.99  fof(f66,plain,(
% 2.62/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f34])).
% 2.62/0.99  
% 2.62/0.99  fof(f4,axiom,(
% 2.62/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f21,plain,(
% 2.62/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.62/0.99    inference(ennf_transformation,[],[f4])).
% 2.62/0.99  
% 2.62/0.99  fof(f22,plain,(
% 2.62/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.62/0.99    inference(flattening,[],[f21])).
% 2.62/0.99  
% 2.62/0.99  fof(f54,plain,(
% 2.62/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f22])).
% 2.62/0.99  
% 2.62/0.99  fof(f5,axiom,(
% 2.62/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.62/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.62/0.99  
% 2.62/0.99  fof(f23,plain,(
% 2.62/0.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.62/0.99    inference(ennf_transformation,[],[f5])).
% 2.62/0.99  
% 2.62/0.99  fof(f24,plain,(
% 2.62/0.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.62/0.99    inference(flattening,[],[f23])).
% 2.62/0.99  
% 2.62/0.99  fof(f55,plain,(
% 2.62/0.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.62/0.99    inference(cnf_transformation,[],[f24])).
% 2.62/0.99  
% 2.62/0.99  cnf(c_25,negated_conjecture,
% 2.62/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.62/0.99      inference(cnf_transformation,[],[f75]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_613,negated_conjecture,
% 2.62/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_25]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1036,plain,
% 2.62/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_19,plain,
% 2.62/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f67]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_30,negated_conjecture,
% 2.62/0.99      ( l1_struct_0(sK0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_350,plain,
% 2.62/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_351,plain,
% 2.62/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_350]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_609,plain,
% 2.62/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_351]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_28,negated_conjecture,
% 2.62/0.99      ( l1_struct_0(sK1) ),
% 2.62/0.99      inference(cnf_transformation,[],[f72]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_345,plain,
% 2.62/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_346,plain,
% 2.62/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_345]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_610,plain,
% 2.62/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_346]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1057,plain,
% 2.62/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_1036,c_609,c_610]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_10,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/0.99      | v1_partfun1(X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | v1_xboole_0(X2)
% 2.62/0.99      | ~ v1_funct_1(X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f59]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_20,plain,
% 2.62/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.62/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_29,negated_conjecture,
% 2.62/0.99      ( ~ v2_struct_0(sK1) ),
% 2.62/0.99      inference(cnf_transformation,[],[f71]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_332,plain,
% 2.62/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_20,c_29]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_333,plain,
% 2.62/0.99      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_332]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_43,plain,
% 2.62/0.99      ( v2_struct_0(sK1)
% 2.62/0.99      | ~ l1_struct_0(sK1)
% 2.62/0.99      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_335,plain,
% 2.62/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_333,c_29,c_28,c_43]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_357,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/0.99      | v1_partfun1(X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | ~ v1_funct_1(X0)
% 2.62/0.99      | u1_struct_0(sK1) != X2 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_10,c_335]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_358,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.62/0.99      | v1_partfun1(X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.62/0.99      | ~ v1_funct_1(X0) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_357]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_13,plain,
% 2.62/0.99      ( ~ v1_partfun1(X0,X1)
% 2.62/0.99      | ~ v4_relat_1(X0,X1)
% 2.62/0.99      | ~ v1_relat_1(X0)
% 2.62/0.99      | k1_relat_1(X0) = X1 ),
% 2.62/0.99      inference(cnf_transformation,[],[f60]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_419,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.62/0.99      | ~ v4_relat_1(X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.62/0.99      | ~ v1_funct_1(X0)
% 2.62/0.99      | ~ v1_relat_1(X0)
% 2.62/0.99      | k1_relat_1(X0) = X1 ),
% 2.62/0.99      inference(resolution,[status(thm)],[c_358,c_13]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_8,plain,
% 2.62/0.99      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.62/0.99      inference(cnf_transformation,[],[f56]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_435,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.62/0.99      | ~ v1_funct_1(X0)
% 2.62/0.99      | ~ v1_relat_1(X0)
% 2.62/0.99      | k1_relat_1(X0) = X1 ),
% 2.62/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_419,c_8]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_608,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0_51,X0_52,u1_struct_0(sK1))
% 2.62/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1))))
% 2.62/0.99      | ~ v1_funct_1(X0_51)
% 2.62/0.99      | ~ v1_relat_1(X0_51)
% 2.62/0.99      | k1_relat_1(X0_51) = X0_52 ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_435]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1039,plain,
% 2.62/0.99      ( k1_relat_1(X0_51) = X0_52
% 2.62/0.99      | v1_funct_2(X0_51,X0_52,u1_struct_0(sK1)) != iProver_top
% 2.62/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1)))) != iProver_top
% 2.62/0.99      | v1_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v1_relat_1(X0_51) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1118,plain,
% 2.62/0.99      ( k1_relat_1(X0_51) = X0_52
% 2.62/0.99      | v1_funct_2(X0_51,X0_52,k2_struct_0(sK1)) != iProver_top
% 2.62/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top
% 2.62/0.99      | v1_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v1_relat_1(X0_51) != iProver_top ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_1039,c_610]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1323,plain,
% 2.62/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.62/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.62/0.99      | v1_funct_1(sK2) != iProver_top
% 2.62/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_1057,c_1118]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_27,negated_conjecture,
% 2.62/0.99      ( v1_funct_1(sK2) ),
% 2.62/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_26,negated_conjecture,
% 2.62/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.62/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_612,negated_conjecture,
% 2.62/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_26]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1037,plain,
% 2.62/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1051,plain,
% 2.62/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_1037,c_609,c_610]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1197,plain,
% 2.62/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
% 2.62/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1051]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1324,plain,
% 2.62/0.99      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
% 2.62/0.99      | ~ v1_funct_1(sK2)
% 2.62/0.99      | ~ v1_relat_1(sK2)
% 2.62/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.62/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1323]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_0,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f48]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_628,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 2.62/0.99      | ~ v1_relat_1(X1_51)
% 2.62/0.99      | v1_relat_1(X0_51) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_0]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1255,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.62/0.99      | v1_relat_1(X0_51)
% 2.62/0.99      | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_628]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1363,plain,
% 2.62/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.62/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.62/0.99      | v1_relat_1(sK2) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_1255]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1,plain,
% 2.62/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.62/0.99      inference(cnf_transformation,[],[f49]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_627,plain,
% 2.62/0.99      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_1]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1386,plain,
% 2.62/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_627]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2124,plain,
% 2.62/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_1323,c_27,c_25,c_1197,c_1324,c_1363,c_1386]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_9,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_620,plain,
% 2.62/0.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.62/0.99      | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_9]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1030,plain,
% 2.62/0.99      ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
% 2.62/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1393,plain,
% 2.62/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_1057,c_1030]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_24,negated_conjecture,
% 2.62/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.62/0.99      inference(cnf_transformation,[],[f76]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_614,negated_conjecture,
% 2.62/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1054,plain,
% 2.62/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_614,c_609,c_610]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1511,plain,
% 2.62/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_1393,c_1054]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1513,plain,
% 2.62/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_1511,c_1393]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2128,plain,
% 2.62/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_2124,c_1513]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_21,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | ~ v1_funct_1(X0)
% 2.62/0.99      | ~ v2_funct_1(X0)
% 2.62/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.62/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.62/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_616,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.62/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.62/0.99      | ~ v1_funct_1(X0_51)
% 2.62/0.99      | ~ v2_funct_1(X0_51)
% 2.62/0.99      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.62/0.99      | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_21]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1034,plain,
% 2.62/0.99      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.62/0.99      | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51)
% 2.62/0.99      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.62/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.62/0.99      | v1_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v2_funct_1(X0_51) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_616]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2589,plain,
% 2.62/0.99      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.62/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.62/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.62/0.99      | v1_funct_1(sK2) != iProver_top
% 2.62/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2128,c_1034]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_34,plain,
% 2.62/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_23,negated_conjecture,
% 2.62/0.99      ( v2_funct_1(sK2) ),
% 2.62/0.99      inference(cnf_transformation,[],[f77]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_37,plain,
% 2.62/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1516,plain,
% 2.62/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_1511,c_1057]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2127,plain,
% 2.62/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_2124,c_1516]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1517,plain,
% 2.62/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_1511,c_1051]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2129,plain,
% 2.62/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_2124,c_1517]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2748,plain,
% 2.62/0.99      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_2589,c_34,c_37,c_2127,c_2129]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_14,plain,
% 2.62/0.99      ( r2_funct_2(X0,X1,X2,X2)
% 2.62/0.99      | ~ v1_funct_2(X2,X0,X1)
% 2.62/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.62/0.99      | ~ v1_funct_1(X2) ),
% 2.62/0.99      inference(cnf_transformation,[],[f80]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_22,negated_conjecture,
% 2.62/0.99      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.62/0.99      inference(cnf_transformation,[],[f78]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_454,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | ~ v1_funct_1(X0)
% 2.62/0.99      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.62/0.99      | u1_struct_0(sK1) != X2
% 2.62/0.99      | u1_struct_0(sK0) != X1
% 2.62/0.99      | sK2 != X0 ),
% 2.62/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_455,plain,
% 2.62/0.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.62/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.62/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.62/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.62/0.99      inference(unflattening,[status(thm)],[c_454]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_607,plain,
% 2.62/0.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.62/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.62/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.62/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_455]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1040,plain,
% 2.62/0.99      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.62/0.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.62/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.62/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1177,plain,
% 2.62/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.62/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.62/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.62/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_1040,c_609,c_610]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1514,plain,
% 2.62/0.99      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.62/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.62/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.62/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_1511,c_1177]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2339,plain,
% 2.62/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 2.62/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.62/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.62/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_1514,c_2124]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2751,plain,
% 2.62/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.62/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.62/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.62/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.62/0.99      inference(demodulation,[status(thm)],[c_2748,c_2339]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_36,plain,
% 2.62/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2,plain,
% 2.62/0.99      ( ~ v1_funct_1(X0)
% 2.62/0.99      | ~ v2_funct_1(X0)
% 2.62/0.99      | v2_funct_1(k2_funct_1(X0))
% 2.62/0.99      | ~ v1_relat_1(X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f52]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_626,plain,
% 2.62/0.99      ( ~ v1_funct_1(X0_51)
% 2.62/0.99      | ~ v2_funct_1(X0_51)
% 2.62/0.99      | v2_funct_1(k2_funct_1(X0_51))
% 2.62/0.99      | ~ v1_relat_1(X0_51) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_2]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_667,plain,
% 2.62/0.99      ( v1_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v2_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v2_funct_1(k2_funct_1(X0_51)) = iProver_top
% 2.62/0.99      | v1_relat_1(X0_51) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_669,plain,
% 2.62/0.99      ( v1_funct_1(sK2) != iProver_top
% 2.62/0.99      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.62/0.99      | v2_funct_1(sK2) != iProver_top
% 2.62/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_667]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3,plain,
% 2.62/0.99      ( ~ v1_funct_1(X0)
% 2.62/0.99      | v1_funct_1(k2_funct_1(X0))
% 2.62/0.99      | ~ v2_funct_1(X0)
% 2.62/0.99      | ~ v1_relat_1(X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f51]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_625,plain,
% 2.62/0.99      ( ~ v1_funct_1(X0_51)
% 2.62/0.99      | v1_funct_1(k2_funct_1(X0_51))
% 2.62/0.99      | ~ v2_funct_1(X0_51)
% 2.62/0.99      | ~ v1_relat_1(X0_51) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_3]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_670,plain,
% 2.62/0.99      ( v1_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v1_funct_1(k2_funct_1(X0_51)) = iProver_top
% 2.62/0.99      | v2_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v1_relat_1(X0_51) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_672,plain,
% 2.62/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.62/0.99      | v1_funct_1(sK2) != iProver_top
% 2.62/0.99      | v2_funct_1(sK2) != iProver_top
% 2.62/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_670]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1364,plain,
% 2.62/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.62/0.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.62/0.99      | v1_relat_1(sK2) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1363]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1387,plain,
% 2.62/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_1386]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_17,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | ~ v1_funct_1(X0)
% 2.62/0.99      | ~ v2_funct_1(X0)
% 2.62/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.62/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_618,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.62/0.99      | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52)
% 2.62/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.62/0.99      | ~ v1_funct_1(X0_51)
% 2.62/0.99      | ~ v2_funct_1(X0_51)
% 2.62/0.99      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_17]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1032,plain,
% 2.62/0.99      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.62/0.99      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.62/0.99      | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52) = iProver_top
% 2.62/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.62/0.99      | v1_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v2_funct_1(X0_51) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2590,plain,
% 2.62/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.62/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.62/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.62/0.99      | v1_funct_1(sK2) != iProver_top
% 2.62/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2128,c_1032]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_16,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.62/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.62/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.62/0.99      | ~ v1_funct_1(X0)
% 2.62/0.99      | ~ v2_funct_1(X0)
% 2.62/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.62/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_619,plain,
% 2.62/0.99      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.62/0.99      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.62/0.99      | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
% 2.62/0.99      | ~ v1_funct_1(X0_51)
% 2.62/0.99      | ~ v2_funct_1(X0_51)
% 2.62/0.99      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_16]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1031,plain,
% 2.62/0.99      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.62/0.99      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.62/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.62/0.99      | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
% 2.62/0.99      | v1_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v2_funct_1(X0_51) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2591,plain,
% 2.62/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.62/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.62/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.62/0.99      | v1_funct_1(sK2) != iProver_top
% 2.62/0.99      | v2_funct_1(sK2) != iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2128,c_1031]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2930,plain,
% 2.62/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_2591,c_34,c_37,c_2127,c_2129]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2936,plain,
% 2.62/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2930,c_1030]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_611,negated_conjecture,
% 2.62/0.99      ( v1_funct_1(sK2) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_27]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1038,plain,
% 2.62/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_5,plain,
% 2.62/0.99      ( ~ v1_funct_1(X0)
% 2.62/0.99      | ~ v2_funct_1(X0)
% 2.62/0.99      | ~ v1_relat_1(X0)
% 2.62/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.62/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_623,plain,
% 2.62/0.99      ( ~ v1_funct_1(X0_51)
% 2.62/0.99      | ~ v2_funct_1(X0_51)
% 2.62/0.99      | ~ v1_relat_1(X0_51)
% 2.62/0.99      | k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51) ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_5]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1027,plain,
% 2.62/0.99      ( k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51)
% 2.62/0.99      | v1_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v2_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v1_relat_1(X0_51) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1784,plain,
% 2.62/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.62/0.99      | v2_funct_1(sK2) != iProver_top
% 2.62/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_1038,c_1027]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_677,plain,
% 2.62/0.99      ( ~ v1_funct_1(sK2)
% 2.62/0.99      | ~ v2_funct_1(sK2)
% 2.62/0.99      | ~ v1_relat_1(sK2)
% 2.62/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_623]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2046,plain,
% 2.62/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_1784,c_27,c_25,c_23,c_677,c_1363,c_1386]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2943,plain,
% 2.62/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_2936,c_2046]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3109,plain,
% 2.62/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.62/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.62/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.62/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.62/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_2943,c_1034]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_7,plain,
% 2.62/0.99      ( ~ v1_funct_1(X0)
% 2.62/0.99      | ~ v2_funct_1(X0)
% 2.62/0.99      | ~ v1_relat_1(X0)
% 2.62/0.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.62/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_621,plain,
% 2.62/0.99      ( ~ v1_funct_1(X0_51)
% 2.62/0.99      | ~ v2_funct_1(X0_51)
% 2.62/0.99      | ~ v1_relat_1(X0_51)
% 2.62/0.99      | k2_funct_1(k2_funct_1(X0_51)) = X0_51 ),
% 2.62/0.99      inference(subtyping,[status(esa)],[c_7]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1029,plain,
% 2.62/0.99      ( k2_funct_1(k2_funct_1(X0_51)) = X0_51
% 2.62/0.99      | v1_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v2_funct_1(X0_51) != iProver_top
% 2.62/0.99      | v1_relat_1(X0_51) != iProver_top ),
% 2.62/0.99      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_1755,plain,
% 2.62/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.62/0.99      | v2_funct_1(sK2) != iProver_top
% 2.62/0.99      | v1_relat_1(sK2) != iProver_top ),
% 2.62/0.99      inference(superposition,[status(thm)],[c_1038,c_1029]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_683,plain,
% 2.62/0.99      ( ~ v1_funct_1(sK2)
% 2.62/0.99      | ~ v2_funct_1(sK2)
% 2.62/0.99      | ~ v1_relat_1(sK2)
% 2.62/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.62/0.99      inference(instantiation,[status(thm)],[c_621]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_2039,plain,
% 2.62/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_1755,c_27,c_25,c_23,c_683,c_1363,c_1386]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3129,plain,
% 2.62/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.62/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.62/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.62/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.62/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_3109,c_2039]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3633,plain,
% 2.62/0.99      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.62/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.62/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_2751,c_34,c_36,c_37,c_669,c_672,c_1364,c_1387,c_2127,
% 2.62/0.99                 c_2129,c_2590,c_2591,c_3129]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3137,plain,
% 2.62/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.62/0.99      inference(global_propositional_subsumption,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_3129,c_34,c_36,c_37,c_669,c_672,c_1364,c_1387,c_2127,
% 2.62/0.99                 c_2129,c_2590,c_2591]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3637,plain,
% 2.62/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.62/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.62/0.99      | v1_funct_1(sK2) != iProver_top ),
% 2.62/0.99      inference(light_normalisation,[status(thm)],[c_3633,c_3137]) ).
% 2.62/0.99  
% 2.62/0.99  cnf(c_3641,plain,
% 2.62/0.99      ( $false ),
% 2.62/0.99      inference(forward_subsumption_resolution,
% 2.62/0.99                [status(thm)],
% 2.62/0.99                [c_3637,c_1038,c_2127,c_2129]) ).
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 2.62/0.99  
% 2.62/0.99  ------                               Statistics
% 2.62/0.99  
% 2.62/0.99  ------ General
% 2.62/0.99  
% 2.62/0.99  abstr_ref_over_cycles:                  0
% 2.62/0.99  abstr_ref_under_cycles:                 0
% 2.62/0.99  gc_basic_clause_elim:                   0
% 2.62/0.99  forced_gc_time:                         0
% 2.62/0.99  parsing_time:                           0.011
% 2.62/0.99  unif_index_cands_time:                  0.
% 2.62/0.99  unif_index_add_time:                    0.
% 2.62/0.99  orderings_time:                         0.
% 2.62/0.99  out_proof_time:                         0.013
% 2.62/0.99  total_time:                             0.16
% 2.62/0.99  num_of_symbols:                         55
% 2.62/0.99  num_of_terms:                           3476
% 2.62/0.99  
% 2.62/0.99  ------ Preprocessing
% 2.62/0.99  
% 2.62/0.99  num_of_splits:                          0
% 2.62/0.99  num_of_split_atoms:                     0
% 2.62/0.99  num_of_reused_defs:                     0
% 2.62/0.99  num_eq_ax_congr_red:                    4
% 2.62/0.99  num_of_sem_filtered_clauses:            1
% 2.62/0.99  num_of_subtypes:                        4
% 2.62/0.99  monotx_restored_types:                  1
% 2.62/0.99  sat_num_of_epr_types:                   0
% 2.62/0.99  sat_num_of_non_cyclic_types:            0
% 2.62/0.99  sat_guarded_non_collapsed_types:        1
% 2.62/0.99  num_pure_diseq_elim:                    0
% 2.62/0.99  simp_replaced_by:                       0
% 2.62/0.99  res_preprocessed:                       131
% 2.62/0.99  prep_upred:                             0
% 2.62/0.99  prep_unflattend:                        15
% 2.62/0.99  smt_new_axioms:                         0
% 2.62/0.99  pred_elim_cands:                        5
% 2.62/0.99  pred_elim:                              6
% 2.62/0.99  pred_elim_cl:                           8
% 2.62/0.99  pred_elim_cycles:                       9
% 2.62/0.99  merged_defs:                            0
% 2.62/0.99  merged_defs_ncl:                        0
% 2.62/0.99  bin_hyper_res:                          0
% 2.62/0.99  prep_cycles:                            4
% 2.62/0.99  pred_elim_time:                         0.004
% 2.62/0.99  splitting_time:                         0.
% 2.62/0.99  sem_filter_time:                        0.
% 2.62/0.99  monotx_time:                            0.001
% 2.62/0.99  subtype_inf_time:                       0.002
% 2.62/0.99  
% 2.62/0.99  ------ Problem properties
% 2.62/0.99  
% 2.62/0.99  clauses:                                22
% 2.62/0.99  conjectures:                            5
% 2.62/0.99  epr:                                    2
% 2.62/0.99  horn:                                   22
% 2.62/0.99  ground:                                 8
% 2.62/0.99  unary:                                  8
% 2.62/0.99  binary:                                 1
% 2.62/0.99  lits:                                   70
% 2.62/0.99  lits_eq:                                14
% 2.62/0.99  fd_pure:                                0
% 2.62/0.99  fd_pseudo:                              0
% 2.62/0.99  fd_cond:                                0
% 2.62/0.99  fd_pseudo_cond:                         1
% 2.62/0.99  ac_symbols:                             0
% 2.62/0.99  
% 2.62/0.99  ------ Propositional Solver
% 2.62/0.99  
% 2.62/0.99  prop_solver_calls:                      29
% 2.62/0.99  prop_fast_solver_calls:                 1029
% 2.62/0.99  smt_solver_calls:                       0
% 2.62/0.99  smt_fast_solver_calls:                  0
% 2.62/0.99  prop_num_of_clauses:                    1340
% 2.62/0.99  prop_preprocess_simplified:             4884
% 2.62/0.99  prop_fo_subsumed:                       44
% 2.62/0.99  prop_solver_time:                       0.
% 2.62/0.99  smt_solver_time:                        0.
% 2.62/0.99  smt_fast_solver_time:                   0.
% 2.62/0.99  prop_fast_solver_time:                  0.
% 2.62/0.99  prop_unsat_core_time:                   0.
% 2.62/0.99  
% 2.62/0.99  ------ QBF
% 2.62/0.99  
% 2.62/0.99  qbf_q_res:                              0
% 2.62/0.99  qbf_num_tautologies:                    0
% 2.62/0.99  qbf_prep_cycles:                        0
% 2.62/0.99  
% 2.62/0.99  ------ BMC1
% 2.62/0.99  
% 2.62/0.99  bmc1_current_bound:                     -1
% 2.62/0.99  bmc1_last_solved_bound:                 -1
% 2.62/0.99  bmc1_unsat_core_size:                   -1
% 2.62/0.99  bmc1_unsat_core_parents_size:           -1
% 2.62/0.99  bmc1_merge_next_fun:                    0
% 2.62/0.99  bmc1_unsat_core_clauses_time:           0.
% 2.62/0.99  
% 2.62/0.99  ------ Instantiation
% 2.62/0.99  
% 2.62/0.99  inst_num_of_clauses:                    496
% 2.62/0.99  inst_num_in_passive:                    98
% 2.62/0.99  inst_num_in_active:                     241
% 2.62/0.99  inst_num_in_unprocessed:                157
% 2.62/0.99  inst_num_of_loops:                      260
% 2.62/0.99  inst_num_of_learning_restarts:          0
% 2.62/0.99  inst_num_moves_active_passive:          15
% 2.62/0.99  inst_lit_activity:                      0
% 2.62/0.99  inst_lit_activity_moves:                0
% 2.62/0.99  inst_num_tautologies:                   0
% 2.62/0.99  inst_num_prop_implied:                  0
% 2.62/0.99  inst_num_existing_simplified:           0
% 2.62/0.99  inst_num_eq_res_simplified:             0
% 2.62/0.99  inst_num_child_elim:                    0
% 2.62/0.99  inst_num_of_dismatching_blockings:      86
% 2.62/0.99  inst_num_of_non_proper_insts:           416
% 2.62/0.99  inst_num_of_duplicates:                 0
% 2.62/0.99  inst_inst_num_from_inst_to_res:         0
% 2.62/0.99  inst_dismatching_checking_time:         0.
% 2.62/0.99  
% 2.62/0.99  ------ Resolution
% 2.62/0.99  
% 2.62/0.99  res_num_of_clauses:                     0
% 2.62/0.99  res_num_in_passive:                     0
% 2.62/0.99  res_num_in_active:                      0
% 2.62/0.99  res_num_of_loops:                       135
% 2.62/0.99  res_forward_subset_subsumed:            48
% 2.62/0.99  res_backward_subset_subsumed:           0
% 2.62/0.99  res_forward_subsumed:                   0
% 2.62/0.99  res_backward_subsumed:                  0
% 2.62/0.99  res_forward_subsumption_resolution:     1
% 2.62/0.99  res_backward_subsumption_resolution:    0
% 2.62/0.99  res_clause_to_clause_subsumption:       134
% 2.62/0.99  res_orphan_elimination:                 0
% 2.62/0.99  res_tautology_del:                      45
% 2.62/0.99  res_num_eq_res_simplified:              0
% 2.62/0.99  res_num_sel_changes:                    0
% 2.62/0.99  res_moves_from_active_to_pass:          0
% 2.62/0.99  
% 2.62/0.99  ------ Superposition
% 2.62/0.99  
% 2.62/0.99  sup_time_total:                         0.
% 2.62/0.99  sup_time_generating:                    0.
% 2.62/0.99  sup_time_sim_full:                      0.
% 2.62/0.99  sup_time_sim_immed:                     0.
% 2.62/0.99  
% 2.62/0.99  sup_num_of_clauses:                     42
% 2.62/0.99  sup_num_in_active:                      39
% 2.62/0.99  sup_num_in_passive:                     3
% 2.62/0.99  sup_num_of_loops:                       51
% 2.62/0.99  sup_fw_superposition:                   24
% 2.62/0.99  sup_bw_superposition:                   22
% 2.62/0.99  sup_immediate_simplified:               22
% 2.62/0.99  sup_given_eliminated:                   0
% 2.62/0.99  comparisons_done:                       0
% 2.62/0.99  comparisons_avoided:                    0
% 2.62/0.99  
% 2.62/0.99  ------ Simplifications
% 2.62/0.99  
% 2.62/0.99  
% 2.62/0.99  sim_fw_subset_subsumed:                 4
% 2.62/0.99  sim_bw_subset_subsumed:                 0
% 2.62/0.99  sim_fw_subsumed:                        3
% 2.62/0.99  sim_bw_subsumed:                        0
% 2.62/0.99  sim_fw_subsumption_res:                 3
% 2.62/0.99  sim_bw_subsumption_res:                 0
% 2.62/0.99  sim_tautology_del:                      0
% 2.62/0.99  sim_eq_tautology_del:                   14
% 2.62/0.99  sim_eq_res_simp:                        0
% 2.62/0.99  sim_fw_demodulated:                     0
% 2.62/0.99  sim_bw_demodulated:                     12
% 2.62/0.99  sim_light_normalised:                   25
% 2.62/0.99  sim_joinable_taut:                      0
% 2.62/0.99  sim_joinable_simp:                      0
% 2.62/0.99  sim_ac_normalised:                      0
% 2.62/0.99  sim_smt_subsumption:                    0
% 2.62/0.99  
%------------------------------------------------------------------------------
