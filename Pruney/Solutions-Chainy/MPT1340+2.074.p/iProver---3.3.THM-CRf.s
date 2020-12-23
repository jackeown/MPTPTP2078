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
% DateTime   : Thu Dec  3 12:17:37 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  193 (5164 expanded)
%              Number of clauses        :  122 (1642 expanded)
%              Number of leaves         :   19 (1442 expanded)
%              Depth                    :   28
%              Number of atoms          :  699 (32356 expanded)
%              Number of equality atoms :  242 (5369 expanded)
%              Maximal formula depth    :   12 (   5 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f45,plain,(
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

fof(f44,plain,(
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

fof(f43,plain,
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

fof(f46,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f45,f44,f43])).

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f65,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f58,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f59,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f74,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f53,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f51,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f76,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_614,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1055,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_18,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_339,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_340,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_339])).

cnf(c_610,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_340])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_334,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_335,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_334])).

cnf(c_611,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_335])).

cnf(c_1077,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1055,c_610,c_611])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_19,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_321,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_322,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_321])).

cnf(c_42,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_324,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_322,c_28,c_27,c_42])).

cnf(c_346,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_324])).

cnf(c_347,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_346])).

cnf(c_13,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_443,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_347,c_13])).

cnf(c_8,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_459,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_443,c_8])).

cnf(c_608,plain,
    ( ~ v1_funct_2(X0_51,X0_52,u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k1_relat_1(X0_51) = X0_52 ),
    inference(subtyping,[status(esa)],[c_459])).

cnf(c_1060,plain,
    ( k1_relat_1(X0_51) = X0_52
    | v1_funct_2(X0_51,X0_52,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_1147,plain,
    ( k1_relat_1(X0_51) = X0_52
    | v1_funct_2(X0_51,X0_52,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1060,c_611])).

cnf(c_1479,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1077,c_1147])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_613,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1056,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_1071,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1056,c_610,c_611])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_629,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1287,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | v1_relat_1(X0_51)
    | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(instantiation,[status(thm)],[c_629])).

cnf(c_1393,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1287])).

cnf(c_1394,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1393])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_628,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1416,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_1417,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1416])).

cnf(c_2147,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1479,c_33,c_35,c_1071,c_1394,c_1417])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_621,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1049,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_1423,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1077,c_1049])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_615,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1074,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_615,c_610,c_611])).

cnf(c_1544,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1423,c_1074])).

cnf(c_1546,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1544,c_1423])).

cnf(c_2151,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2147,c_1546])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_620,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1050,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_2614,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2151,c_1050])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_36,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1548,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1544,c_1077])).

cnf(c_2150,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2147,c_1548])).

cnf(c_1549,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1544,c_1071])).

cnf(c_2152,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2147,c_1549])).

cnf(c_3116,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2614,c_33,c_36,c_2150,c_2152])).

cnf(c_3122,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3116,c_1049])).

cnf(c_612,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1057,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_624,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1046,plain,
    ( k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51)
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_1807,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1057,c_1046])).

cnf(c_680,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_624])).

cnf(c_2069,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1807,c_26,c_24,c_22,c_680,c_1393,c_1416])).

cnf(c_3129,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3122,c_2069])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_617,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1053,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51)
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_3137,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3129,c_1053])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_622,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k2_funct_1(k2_funct_1(X0_51)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1048,plain,
    ( k2_funct_1(k2_funct_1(X0_51)) = X0_51
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_1778,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1057,c_1048])).

cnf(c_686,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(c_2062,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1778,c_26,c_24,c_22,c_686,c_1393,c_1416])).

cnf(c_3157,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3137,c_2062])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_627,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | v2_funct_1(k2_funct_1(X0_51))
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_670,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_funct_1(X0_51)) = iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_627])).

cnf(c_672,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_670])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_626,plain,
    ( ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_funct_1(X0_51))
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_673,plain,
    ( v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k2_funct_1(X0_51)) = iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_675,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_673])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_619,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1051,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_2613,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2151,c_1051])).

cnf(c_3657,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3157,c_33,c_35,c_36,c_672,c_675,c_1394,c_1417,c_2150,c_2152,c_2613,c_2614])).

cnf(c_2612,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2151,c_1053])).

cnf(c_2771,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2612,c_33,c_36,c_2150,c_2152])).

cnf(c_14,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_21,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_369,plain,
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
    inference(resolution_lifted,[status(thm)],[c_14,c_21])).

cnf(c_370,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_609,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_370])).

cnf(c_631,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_609])).

cnf(c_1058,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_1206,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1058,c_610,c_611])).

cnf(c_630,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_51)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_609])).

cnf(c_1059,plain,
    ( v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_1138,plain,
    ( v1_funct_2(X0_51,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1059,c_610,c_611])).

cnf(c_1212,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1206,c_1138])).

cnf(c_2362,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1212,c_1544,c_2147])).

cnf(c_2774,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2771,c_2362])).

cnf(c_3660,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3657,c_2774])).

cnf(c_633,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_663,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3660,c_2152,c_2150,c_663,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 17:48:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.56/0.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/0.97  
% 2.56/0.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.56/0.97  
% 2.56/0.97  ------  iProver source info
% 2.56/0.97  
% 2.56/0.97  git: date: 2020-06-30 10:37:57 +0100
% 2.56/0.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.56/0.97  git: non_committed_changes: false
% 2.56/0.97  git: last_make_outside_of_git: false
% 2.56/0.97  
% 2.56/0.97  ------ 
% 2.56/0.97  
% 2.56/0.97  ------ Input Options
% 2.56/0.97  
% 2.56/0.97  --out_options                           all
% 2.56/0.97  --tptp_safe_out                         true
% 2.56/0.97  --problem_path                          ""
% 2.56/0.97  --include_path                          ""
% 2.56/0.97  --clausifier                            res/vclausify_rel
% 2.56/0.97  --clausifier_options                    --mode clausify
% 2.56/0.97  --stdin                                 false
% 2.56/0.97  --stats_out                             all
% 2.56/0.97  
% 2.56/0.97  ------ General Options
% 2.56/0.97  
% 2.56/0.97  --fof                                   false
% 2.56/0.97  --time_out_real                         305.
% 2.56/0.97  --time_out_virtual                      -1.
% 2.56/0.97  --symbol_type_check                     false
% 2.56/0.97  --clausify_out                          false
% 2.56/0.97  --sig_cnt_out                           false
% 2.56/0.97  --trig_cnt_out                          false
% 2.56/0.97  --trig_cnt_out_tolerance                1.
% 2.56/0.97  --trig_cnt_out_sk_spl                   false
% 2.56/0.97  --abstr_cl_out                          false
% 2.56/0.97  
% 2.56/0.97  ------ Global Options
% 2.56/0.97  
% 2.56/0.97  --schedule                              default
% 2.56/0.97  --add_important_lit                     false
% 2.56/0.97  --prop_solver_per_cl                    1000
% 2.56/0.97  --min_unsat_core                        false
% 2.56/0.97  --soft_assumptions                      false
% 2.56/0.97  --soft_lemma_size                       3
% 2.56/0.97  --prop_impl_unit_size                   0
% 2.56/0.97  --prop_impl_unit                        []
% 2.56/0.97  --share_sel_clauses                     true
% 2.56/0.97  --reset_solvers                         false
% 2.56/0.97  --bc_imp_inh                            [conj_cone]
% 2.56/0.97  --conj_cone_tolerance                   3.
% 2.56/0.97  --extra_neg_conj                        none
% 2.56/0.97  --large_theory_mode                     true
% 2.56/0.97  --prolific_symb_bound                   200
% 2.56/0.97  --lt_threshold                          2000
% 2.56/0.97  --clause_weak_htbl                      true
% 2.56/0.97  --gc_record_bc_elim                     false
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing Options
% 2.56/0.97  
% 2.56/0.97  --preprocessing_flag                    true
% 2.56/0.97  --time_out_prep_mult                    0.1
% 2.56/0.97  --splitting_mode                        input
% 2.56/0.97  --splitting_grd                         true
% 2.56/0.97  --splitting_cvd                         false
% 2.56/0.97  --splitting_cvd_svl                     false
% 2.56/0.97  --splitting_nvd                         32
% 2.56/0.97  --sub_typing                            true
% 2.56/0.97  --prep_gs_sim                           true
% 2.56/0.97  --prep_unflatten                        true
% 2.56/0.97  --prep_res_sim                          true
% 2.56/0.97  --prep_upred                            true
% 2.56/0.97  --prep_sem_filter                       exhaustive
% 2.56/0.97  --prep_sem_filter_out                   false
% 2.56/0.97  --pred_elim                             true
% 2.56/0.97  --res_sim_input                         true
% 2.56/0.97  --eq_ax_congr_red                       true
% 2.56/0.97  --pure_diseq_elim                       true
% 2.56/0.97  --brand_transform                       false
% 2.56/0.97  --non_eq_to_eq                          false
% 2.56/0.97  --prep_def_merge                        true
% 2.56/0.97  --prep_def_merge_prop_impl              false
% 2.56/0.97  --prep_def_merge_mbd                    true
% 2.56/0.97  --prep_def_merge_tr_red                 false
% 2.56/0.97  --prep_def_merge_tr_cl                  false
% 2.56/0.97  --smt_preprocessing                     true
% 2.56/0.97  --smt_ac_axioms                         fast
% 2.56/0.97  --preprocessed_out                      false
% 2.56/0.97  --preprocessed_stats                    false
% 2.56/0.97  
% 2.56/0.97  ------ Abstraction refinement Options
% 2.56/0.97  
% 2.56/0.97  --abstr_ref                             []
% 2.56/0.97  --abstr_ref_prep                        false
% 2.56/0.97  --abstr_ref_until_sat                   false
% 2.56/0.97  --abstr_ref_sig_restrict                funpre
% 2.56/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/0.97  --abstr_ref_under                       []
% 2.56/0.97  
% 2.56/0.97  ------ SAT Options
% 2.56/0.97  
% 2.56/0.97  --sat_mode                              false
% 2.56/0.97  --sat_fm_restart_options                ""
% 2.56/0.97  --sat_gr_def                            false
% 2.56/0.97  --sat_epr_types                         true
% 2.56/0.97  --sat_non_cyclic_types                  false
% 2.56/0.97  --sat_finite_models                     false
% 2.56/0.97  --sat_fm_lemmas                         false
% 2.56/0.97  --sat_fm_prep                           false
% 2.56/0.97  --sat_fm_uc_incr                        true
% 2.56/0.97  --sat_out_model                         small
% 2.56/0.97  --sat_out_clauses                       false
% 2.56/0.97  
% 2.56/0.97  ------ QBF Options
% 2.56/0.97  
% 2.56/0.97  --qbf_mode                              false
% 2.56/0.97  --qbf_elim_univ                         false
% 2.56/0.97  --qbf_dom_inst                          none
% 2.56/0.97  --qbf_dom_pre_inst                      false
% 2.56/0.97  --qbf_sk_in                             false
% 2.56/0.97  --qbf_pred_elim                         true
% 2.56/0.97  --qbf_split                             512
% 2.56/0.97  
% 2.56/0.97  ------ BMC1 Options
% 2.56/0.97  
% 2.56/0.97  --bmc1_incremental                      false
% 2.56/0.97  --bmc1_axioms                           reachable_all
% 2.56/0.97  --bmc1_min_bound                        0
% 2.56/0.97  --bmc1_max_bound                        -1
% 2.56/0.97  --bmc1_max_bound_default                -1
% 2.56/0.97  --bmc1_symbol_reachability              true
% 2.56/0.97  --bmc1_property_lemmas                  false
% 2.56/0.97  --bmc1_k_induction                      false
% 2.56/0.97  --bmc1_non_equiv_states                 false
% 2.56/0.97  --bmc1_deadlock                         false
% 2.56/0.97  --bmc1_ucm                              false
% 2.56/0.97  --bmc1_add_unsat_core                   none
% 2.56/0.97  --bmc1_unsat_core_children              false
% 2.56/0.97  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/0.97  --bmc1_out_stat                         full
% 2.56/0.97  --bmc1_ground_init                      false
% 2.56/0.97  --bmc1_pre_inst_next_state              false
% 2.56/0.97  --bmc1_pre_inst_state                   false
% 2.56/0.97  --bmc1_pre_inst_reach_state             false
% 2.56/0.97  --bmc1_out_unsat_core                   false
% 2.56/0.97  --bmc1_aig_witness_out                  false
% 2.56/0.97  --bmc1_verbose                          false
% 2.56/0.97  --bmc1_dump_clauses_tptp                false
% 2.56/0.97  --bmc1_dump_unsat_core_tptp             false
% 2.56/0.97  --bmc1_dump_file                        -
% 2.56/0.97  --bmc1_ucm_expand_uc_limit              128
% 2.56/0.97  --bmc1_ucm_n_expand_iterations          6
% 2.56/0.97  --bmc1_ucm_extend_mode                  1
% 2.56/0.97  --bmc1_ucm_init_mode                    2
% 2.56/0.97  --bmc1_ucm_cone_mode                    none
% 2.56/0.97  --bmc1_ucm_reduced_relation_type        0
% 2.56/0.97  --bmc1_ucm_relax_model                  4
% 2.56/0.97  --bmc1_ucm_full_tr_after_sat            true
% 2.56/0.97  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/0.97  --bmc1_ucm_layered_model                none
% 2.56/0.97  --bmc1_ucm_max_lemma_size               10
% 2.56/0.97  
% 2.56/0.97  ------ AIG Options
% 2.56/0.97  
% 2.56/0.97  --aig_mode                              false
% 2.56/0.97  
% 2.56/0.97  ------ Instantiation Options
% 2.56/0.97  
% 2.56/0.97  --instantiation_flag                    true
% 2.56/0.97  --inst_sos_flag                         false
% 2.56/0.97  --inst_sos_phase                        true
% 2.56/0.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/0.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/0.97  --inst_lit_sel_side                     num_symb
% 2.56/0.97  --inst_solver_per_active                1400
% 2.56/0.97  --inst_solver_calls_frac                1.
% 2.56/0.97  --inst_passive_queue_type               priority_queues
% 2.56/0.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/0.97  --inst_passive_queues_freq              [25;2]
% 2.56/0.97  --inst_dismatching                      true
% 2.56/0.97  --inst_eager_unprocessed_to_passive     true
% 2.56/0.97  --inst_prop_sim_given                   true
% 2.56/0.97  --inst_prop_sim_new                     false
% 2.56/0.97  --inst_subs_new                         false
% 2.56/0.97  --inst_eq_res_simp                      false
% 2.56/0.97  --inst_subs_given                       false
% 2.56/0.97  --inst_orphan_elimination               true
% 2.56/0.97  --inst_learning_loop_flag               true
% 2.56/0.97  --inst_learning_start                   3000
% 2.56/0.97  --inst_learning_factor                  2
% 2.56/0.97  --inst_start_prop_sim_after_learn       3
% 2.56/0.97  --inst_sel_renew                        solver
% 2.56/0.97  --inst_lit_activity_flag                true
% 2.56/0.97  --inst_restr_to_given                   false
% 2.56/0.97  --inst_activity_threshold               500
% 2.56/0.97  --inst_out_proof                        true
% 2.56/0.97  
% 2.56/0.97  ------ Resolution Options
% 2.56/0.97  
% 2.56/0.97  --resolution_flag                       true
% 2.56/0.97  --res_lit_sel                           adaptive
% 2.56/0.97  --res_lit_sel_side                      none
% 2.56/0.97  --res_ordering                          kbo
% 2.56/0.97  --res_to_prop_solver                    active
% 2.56/0.97  --res_prop_simpl_new                    false
% 2.56/0.97  --res_prop_simpl_given                  true
% 2.56/0.97  --res_passive_queue_type                priority_queues
% 2.56/0.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/0.97  --res_passive_queues_freq               [15;5]
% 2.56/0.97  --res_forward_subs                      full
% 2.56/0.97  --res_backward_subs                     full
% 2.56/0.97  --res_forward_subs_resolution           true
% 2.56/0.97  --res_backward_subs_resolution          true
% 2.56/0.97  --res_orphan_elimination                true
% 2.56/0.97  --res_time_limit                        2.
% 2.56/0.97  --res_out_proof                         true
% 2.56/0.97  
% 2.56/0.97  ------ Superposition Options
% 2.56/0.97  
% 2.56/0.97  --superposition_flag                    true
% 2.56/0.97  --sup_passive_queue_type                priority_queues
% 2.56/0.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/0.97  --sup_passive_queues_freq               [8;1;4]
% 2.56/0.97  --demod_completeness_check              fast
% 2.56/0.97  --demod_use_ground                      true
% 2.56/0.97  --sup_to_prop_solver                    passive
% 2.56/0.97  --sup_prop_simpl_new                    true
% 2.56/0.97  --sup_prop_simpl_given                  true
% 2.56/0.97  --sup_fun_splitting                     false
% 2.56/0.97  --sup_smt_interval                      50000
% 2.56/0.97  
% 2.56/0.97  ------ Superposition Simplification Setup
% 2.56/0.97  
% 2.56/0.97  --sup_indices_passive                   []
% 2.56/0.97  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.97  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/0.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_full_bw                           [BwDemod]
% 2.56/0.97  --sup_immed_triv                        [TrivRules]
% 2.56/0.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/0.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_immed_bw_main                     []
% 2.56/0.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.97  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/0.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.97  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.97  
% 2.56/0.97  ------ Combination Options
% 2.56/0.97  
% 2.56/0.97  --comb_res_mult                         3
% 2.56/0.97  --comb_sup_mult                         2
% 2.56/0.97  --comb_inst_mult                        10
% 2.56/0.97  
% 2.56/0.97  ------ Debug Options
% 2.56/0.97  
% 2.56/0.97  --dbg_backtrace                         false
% 2.56/0.97  --dbg_dump_prop_clauses                 false
% 2.56/0.97  --dbg_dump_prop_clauses_file            -
% 2.56/0.97  --dbg_out_stat                          false
% 2.56/0.97  ------ Parsing...
% 2.56/0.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.56/0.97  ------ Proving...
% 2.56/0.97  ------ Problem Properties 
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  clauses                                 23
% 2.56/0.97  conjectures                             5
% 2.56/0.97  EPR                                     2
% 2.56/0.97  Horn                                    23
% 2.56/0.97  unary                                   8
% 2.56/0.97  binary                                  1
% 2.56/0.97  lits                                    75
% 2.56/0.97  lits eq                                 14
% 2.56/0.97  fd_pure                                 0
% 2.56/0.97  fd_pseudo                               0
% 2.56/0.97  fd_cond                                 0
% 2.56/0.97  fd_pseudo_cond                          1
% 2.56/0.97  AC symbols                              0
% 2.56/0.97  
% 2.56/0.97  ------ Schedule dynamic 5 is on 
% 2.56/0.97  
% 2.56/0.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.56/0.97  
% 2.56/0.97  
% 2.56/0.97  ------ 
% 2.56/0.97  Current options:
% 2.56/0.97  ------ 
% 2.56/0.97  
% 2.56/0.97  ------ Input Options
% 2.56/0.97  
% 2.56/0.97  --out_options                           all
% 2.56/0.97  --tptp_safe_out                         true
% 2.56/0.97  --problem_path                          ""
% 2.56/0.97  --include_path                          ""
% 2.56/0.97  --clausifier                            res/vclausify_rel
% 2.56/0.97  --clausifier_options                    --mode clausify
% 2.56/0.97  --stdin                                 false
% 2.56/0.97  --stats_out                             all
% 2.56/0.97  
% 2.56/0.97  ------ General Options
% 2.56/0.97  
% 2.56/0.97  --fof                                   false
% 2.56/0.97  --time_out_real                         305.
% 2.56/0.97  --time_out_virtual                      -1.
% 2.56/0.97  --symbol_type_check                     false
% 2.56/0.97  --clausify_out                          false
% 2.56/0.97  --sig_cnt_out                           false
% 2.56/0.97  --trig_cnt_out                          false
% 2.56/0.97  --trig_cnt_out_tolerance                1.
% 2.56/0.97  --trig_cnt_out_sk_spl                   false
% 2.56/0.97  --abstr_cl_out                          false
% 2.56/0.97  
% 2.56/0.97  ------ Global Options
% 2.56/0.97  
% 2.56/0.97  --schedule                              default
% 2.56/0.97  --add_important_lit                     false
% 2.56/0.97  --prop_solver_per_cl                    1000
% 2.56/0.97  --min_unsat_core                        false
% 2.56/0.97  --soft_assumptions                      false
% 2.56/0.97  --soft_lemma_size                       3
% 2.56/0.97  --prop_impl_unit_size                   0
% 2.56/0.97  --prop_impl_unit                        []
% 2.56/0.97  --share_sel_clauses                     true
% 2.56/0.97  --reset_solvers                         false
% 2.56/0.97  --bc_imp_inh                            [conj_cone]
% 2.56/0.97  --conj_cone_tolerance                   3.
% 2.56/0.97  --extra_neg_conj                        none
% 2.56/0.97  --large_theory_mode                     true
% 2.56/0.97  --prolific_symb_bound                   200
% 2.56/0.97  --lt_threshold                          2000
% 2.56/0.97  --clause_weak_htbl                      true
% 2.56/0.97  --gc_record_bc_elim                     false
% 2.56/0.97  
% 2.56/0.97  ------ Preprocessing Options
% 2.56/0.97  
% 2.56/0.97  --preprocessing_flag                    true
% 2.56/0.97  --time_out_prep_mult                    0.1
% 2.56/0.97  --splitting_mode                        input
% 2.56/0.97  --splitting_grd                         true
% 2.56/0.97  --splitting_cvd                         false
% 2.56/0.97  --splitting_cvd_svl                     false
% 2.56/0.97  --splitting_nvd                         32
% 2.56/0.97  --sub_typing                            true
% 2.56/0.97  --prep_gs_sim                           true
% 2.56/0.97  --prep_unflatten                        true
% 2.56/0.97  --prep_res_sim                          true
% 2.56/0.97  --prep_upred                            true
% 2.56/0.97  --prep_sem_filter                       exhaustive
% 2.56/0.97  --prep_sem_filter_out                   false
% 2.56/0.97  --pred_elim                             true
% 2.56/0.97  --res_sim_input                         true
% 2.56/0.97  --eq_ax_congr_red                       true
% 2.56/0.97  --pure_diseq_elim                       true
% 2.56/0.97  --brand_transform                       false
% 2.56/0.97  --non_eq_to_eq                          false
% 2.56/0.97  --prep_def_merge                        true
% 2.56/0.97  --prep_def_merge_prop_impl              false
% 2.56/0.97  --prep_def_merge_mbd                    true
% 2.56/0.97  --prep_def_merge_tr_red                 false
% 2.56/0.97  --prep_def_merge_tr_cl                  false
% 2.56/0.97  --smt_preprocessing                     true
% 2.56/0.97  --smt_ac_axioms                         fast
% 2.56/0.97  --preprocessed_out                      false
% 2.56/0.97  --preprocessed_stats                    false
% 2.56/0.97  
% 2.56/0.97  ------ Abstraction refinement Options
% 2.56/0.97  
% 2.56/0.97  --abstr_ref                             []
% 2.56/0.97  --abstr_ref_prep                        false
% 2.56/0.97  --abstr_ref_until_sat                   false
% 2.56/0.97  --abstr_ref_sig_restrict                funpre
% 2.56/0.97  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/0.97  --abstr_ref_under                       []
% 2.56/0.97  
% 2.56/0.97  ------ SAT Options
% 2.56/0.97  
% 2.56/0.97  --sat_mode                              false
% 2.56/0.97  --sat_fm_restart_options                ""
% 2.56/0.98  --sat_gr_def                            false
% 2.56/0.98  --sat_epr_types                         true
% 2.56/0.98  --sat_non_cyclic_types                  false
% 2.56/0.98  --sat_finite_models                     false
% 2.56/0.98  --sat_fm_lemmas                         false
% 2.56/0.98  --sat_fm_prep                           false
% 2.56/0.98  --sat_fm_uc_incr                        true
% 2.56/0.98  --sat_out_model                         small
% 2.56/0.98  --sat_out_clauses                       false
% 2.56/0.98  
% 2.56/0.98  ------ QBF Options
% 2.56/0.98  
% 2.56/0.98  --qbf_mode                              false
% 2.56/0.98  --qbf_elim_univ                         false
% 2.56/0.98  --qbf_dom_inst                          none
% 2.56/0.98  --qbf_dom_pre_inst                      false
% 2.56/0.98  --qbf_sk_in                             false
% 2.56/0.98  --qbf_pred_elim                         true
% 2.56/0.98  --qbf_split                             512
% 2.56/0.98  
% 2.56/0.98  ------ BMC1 Options
% 2.56/0.98  
% 2.56/0.98  --bmc1_incremental                      false
% 2.56/0.98  --bmc1_axioms                           reachable_all
% 2.56/0.98  --bmc1_min_bound                        0
% 2.56/0.98  --bmc1_max_bound                        -1
% 2.56/0.98  --bmc1_max_bound_default                -1
% 2.56/0.98  --bmc1_symbol_reachability              true
% 2.56/0.98  --bmc1_property_lemmas                  false
% 2.56/0.98  --bmc1_k_induction                      false
% 2.56/0.98  --bmc1_non_equiv_states                 false
% 2.56/0.98  --bmc1_deadlock                         false
% 2.56/0.98  --bmc1_ucm                              false
% 2.56/0.98  --bmc1_add_unsat_core                   none
% 2.56/0.98  --bmc1_unsat_core_children              false
% 2.56/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/0.98  --bmc1_out_stat                         full
% 2.56/0.98  --bmc1_ground_init                      false
% 2.56/0.98  --bmc1_pre_inst_next_state              false
% 2.56/0.98  --bmc1_pre_inst_state                   false
% 2.56/0.98  --bmc1_pre_inst_reach_state             false
% 2.56/0.98  --bmc1_out_unsat_core                   false
% 2.56/0.98  --bmc1_aig_witness_out                  false
% 2.56/0.98  --bmc1_verbose                          false
% 2.56/0.98  --bmc1_dump_clauses_tptp                false
% 2.56/0.98  --bmc1_dump_unsat_core_tptp             false
% 2.56/0.98  --bmc1_dump_file                        -
% 2.56/0.98  --bmc1_ucm_expand_uc_limit              128
% 2.56/0.98  --bmc1_ucm_n_expand_iterations          6
% 2.56/0.98  --bmc1_ucm_extend_mode                  1
% 2.56/0.98  --bmc1_ucm_init_mode                    2
% 2.56/0.98  --bmc1_ucm_cone_mode                    none
% 2.56/0.98  --bmc1_ucm_reduced_relation_type        0
% 2.56/0.98  --bmc1_ucm_relax_model                  4
% 2.56/0.98  --bmc1_ucm_full_tr_after_sat            true
% 2.56/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/0.98  --bmc1_ucm_layered_model                none
% 2.56/0.98  --bmc1_ucm_max_lemma_size               10
% 2.56/0.98  
% 2.56/0.98  ------ AIG Options
% 2.56/0.98  
% 2.56/0.98  --aig_mode                              false
% 2.56/0.98  
% 2.56/0.98  ------ Instantiation Options
% 2.56/0.98  
% 2.56/0.98  --instantiation_flag                    true
% 2.56/0.98  --inst_sos_flag                         false
% 2.56/0.98  --inst_sos_phase                        true
% 2.56/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/0.98  --inst_lit_sel_side                     none
% 2.56/0.98  --inst_solver_per_active                1400
% 2.56/0.98  --inst_solver_calls_frac                1.
% 2.56/0.98  --inst_passive_queue_type               priority_queues
% 2.56/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/0.98  --inst_passive_queues_freq              [25;2]
% 2.56/0.98  --inst_dismatching                      true
% 2.56/0.98  --inst_eager_unprocessed_to_passive     true
% 2.56/0.98  --inst_prop_sim_given                   true
% 2.56/0.98  --inst_prop_sim_new                     false
% 2.56/0.98  --inst_subs_new                         false
% 2.56/0.98  --inst_eq_res_simp                      false
% 2.56/0.98  --inst_subs_given                       false
% 2.56/0.98  --inst_orphan_elimination               true
% 2.56/0.98  --inst_learning_loop_flag               true
% 2.56/0.98  --inst_learning_start                   3000
% 2.56/0.98  --inst_learning_factor                  2
% 2.56/0.98  --inst_start_prop_sim_after_learn       3
% 2.56/0.98  --inst_sel_renew                        solver
% 2.56/0.98  --inst_lit_activity_flag                true
% 2.56/0.98  --inst_restr_to_given                   false
% 2.56/0.98  --inst_activity_threshold               500
% 2.56/0.98  --inst_out_proof                        true
% 2.56/0.98  
% 2.56/0.98  ------ Resolution Options
% 2.56/0.98  
% 2.56/0.98  --resolution_flag                       false
% 2.56/0.98  --res_lit_sel                           adaptive
% 2.56/0.98  --res_lit_sel_side                      none
% 2.56/0.98  --res_ordering                          kbo
% 2.56/0.98  --res_to_prop_solver                    active
% 2.56/0.98  --res_prop_simpl_new                    false
% 2.56/0.98  --res_prop_simpl_given                  true
% 2.56/0.98  --res_passive_queue_type                priority_queues
% 2.56/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/0.98  --res_passive_queues_freq               [15;5]
% 2.56/0.98  --res_forward_subs                      full
% 2.56/0.98  --res_backward_subs                     full
% 2.56/0.98  --res_forward_subs_resolution           true
% 2.56/0.98  --res_backward_subs_resolution          true
% 2.56/0.98  --res_orphan_elimination                true
% 2.56/0.98  --res_time_limit                        2.
% 2.56/0.98  --res_out_proof                         true
% 2.56/0.98  
% 2.56/0.98  ------ Superposition Options
% 2.56/0.98  
% 2.56/0.98  --superposition_flag                    true
% 2.56/0.98  --sup_passive_queue_type                priority_queues
% 2.56/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/0.98  --sup_passive_queues_freq               [8;1;4]
% 2.56/0.98  --demod_completeness_check              fast
% 2.56/0.98  --demod_use_ground                      true
% 2.56/0.98  --sup_to_prop_solver                    passive
% 2.56/0.98  --sup_prop_simpl_new                    true
% 2.56/0.98  --sup_prop_simpl_given                  true
% 2.56/0.98  --sup_fun_splitting                     false
% 2.56/0.98  --sup_smt_interval                      50000
% 2.56/0.98  
% 2.56/0.98  ------ Superposition Simplification Setup
% 2.56/0.98  
% 2.56/0.98  --sup_indices_passive                   []
% 2.56/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.98  --sup_full_bw                           [BwDemod]
% 2.56/0.98  --sup_immed_triv                        [TrivRules]
% 2.56/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.98  --sup_immed_bw_main                     []
% 2.56/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/0.98  
% 2.56/0.98  ------ Combination Options
% 2.56/0.98  
% 2.56/0.98  --comb_res_mult                         3
% 2.56/0.98  --comb_sup_mult                         2
% 2.56/0.98  --comb_inst_mult                        10
% 2.56/0.98  
% 2.56/0.98  ------ Debug Options
% 2.56/0.98  
% 2.56/0.98  --dbg_backtrace                         false
% 2.56/0.98  --dbg_dump_prop_clauses                 false
% 2.56/0.98  --dbg_dump_prop_clauses_file            -
% 2.56/0.98  --dbg_out_stat                          false
% 2.56/0.98  
% 2.56/0.98  
% 2.56/0.98  
% 2.56/0.98  
% 2.56/0.98  ------ Proving...
% 2.56/0.98  
% 2.56/0.98  
% 2.56/0.98  % SZS status Theorem for theBenchmark.p
% 2.56/0.98  
% 2.56/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 2.56/0.98  
% 2.56/0.98  fof(f15,conjecture,(
% 2.56/0.98    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f16,negated_conjecture,(
% 2.56/0.98    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.56/0.98    inference(negated_conjecture,[],[f15])).
% 2.56/0.98  
% 2.56/0.98  fof(f40,plain,(
% 2.56/0.98    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.56/0.98    inference(ennf_transformation,[],[f16])).
% 2.56/0.98  
% 2.56/0.98  fof(f41,plain,(
% 2.56/0.98    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.56/0.98    inference(flattening,[],[f40])).
% 2.56/0.98  
% 2.56/0.98  fof(f45,plain,(
% 2.56/0.98    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.56/0.98    introduced(choice_axiom,[])).
% 2.56/0.98  
% 2.56/0.98  fof(f44,plain,(
% 2.56/0.98    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.56/0.98    introduced(choice_axiom,[])).
% 2.56/0.98  
% 2.56/0.98  fof(f43,plain,(
% 2.56/0.98    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.56/0.98    introduced(choice_axiom,[])).
% 2.56/0.98  
% 2.56/0.98  fof(f46,plain,(
% 2.56/0.98    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.56/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f41,f45,f44,f43])).
% 2.56/0.98  
% 2.56/0.98  fof(f73,plain,(
% 2.56/0.98    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.56/0.98    inference(cnf_transformation,[],[f46])).
% 2.56/0.98  
% 2.56/0.98  fof(f12,axiom,(
% 2.56/0.98    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f35,plain,(
% 2.56/0.98    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.56/0.98    inference(ennf_transformation,[],[f12])).
% 2.56/0.98  
% 2.56/0.98  fof(f65,plain,(
% 2.56/0.98    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f35])).
% 2.56/0.98  
% 2.56/0.98  fof(f68,plain,(
% 2.56/0.98    l1_struct_0(sK0)),
% 2.56/0.98    inference(cnf_transformation,[],[f46])).
% 2.56/0.98  
% 2.56/0.98  fof(f70,plain,(
% 2.56/0.98    l1_struct_0(sK1)),
% 2.56/0.98    inference(cnf_transformation,[],[f46])).
% 2.56/0.98  
% 2.56/0.98  fof(f8,axiom,(
% 2.56/0.98    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f27,plain,(
% 2.56/0.98    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.56/0.98    inference(ennf_transformation,[],[f8])).
% 2.56/0.98  
% 2.56/0.98  fof(f28,plain,(
% 2.56/0.98    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.56/0.98    inference(flattening,[],[f27])).
% 2.56/0.98  
% 2.56/0.98  fof(f58,plain,(
% 2.56/0.98    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f28])).
% 2.56/0.98  
% 2.56/0.98  fof(f13,axiom,(
% 2.56/0.98    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f36,plain,(
% 2.56/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.56/0.98    inference(ennf_transformation,[],[f13])).
% 2.56/0.98  
% 2.56/0.98  fof(f37,plain,(
% 2.56/0.98    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.56/0.98    inference(flattening,[],[f36])).
% 2.56/0.98  
% 2.56/0.98  fof(f66,plain,(
% 2.56/0.98    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f37])).
% 2.56/0.98  
% 2.56/0.98  fof(f69,plain,(
% 2.56/0.98    ~v2_struct_0(sK1)),
% 2.56/0.98    inference(cnf_transformation,[],[f46])).
% 2.56/0.98  
% 2.56/0.98  fof(f9,axiom,(
% 2.56/0.98    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f29,plain,(
% 2.56/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.56/0.98    inference(ennf_transformation,[],[f9])).
% 2.56/0.98  
% 2.56/0.98  fof(f30,plain,(
% 2.56/0.98    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.56/0.98    inference(flattening,[],[f29])).
% 2.56/0.98  
% 2.56/0.98  fof(f42,plain,(
% 2.56/0.98    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.56/0.98    inference(nnf_transformation,[],[f30])).
% 2.56/0.98  
% 2.56/0.98  fof(f59,plain,(
% 2.56/0.98    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f42])).
% 2.56/0.98  
% 2.56/0.98  fof(f6,axiom,(
% 2.56/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f17,plain,(
% 2.56/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.56/0.98    inference(pure_predicate_removal,[],[f6])).
% 2.56/0.98  
% 2.56/0.98  fof(f25,plain,(
% 2.56/0.98    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.98    inference(ennf_transformation,[],[f17])).
% 2.56/0.98  
% 2.56/0.98  fof(f55,plain,(
% 2.56/0.98    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/0.98    inference(cnf_transformation,[],[f25])).
% 2.56/0.98  
% 2.56/0.98  fof(f71,plain,(
% 2.56/0.98    v1_funct_1(sK2)),
% 2.56/0.98    inference(cnf_transformation,[],[f46])).
% 2.56/0.98  
% 2.56/0.98  fof(f72,plain,(
% 2.56/0.98    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.56/0.98    inference(cnf_transformation,[],[f46])).
% 2.56/0.98  
% 2.56/0.98  fof(f1,axiom,(
% 2.56/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f18,plain,(
% 2.56/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.56/0.98    inference(ennf_transformation,[],[f1])).
% 2.56/0.98  
% 2.56/0.98  fof(f47,plain,(
% 2.56/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f18])).
% 2.56/0.98  
% 2.56/0.98  fof(f2,axiom,(
% 2.56/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f48,plain,(
% 2.56/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.56/0.98    inference(cnf_transformation,[],[f2])).
% 2.56/0.98  
% 2.56/0.98  fof(f7,axiom,(
% 2.56/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f26,plain,(
% 2.56/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/0.98    inference(ennf_transformation,[],[f7])).
% 2.56/0.98  
% 2.56/0.98  fof(f56,plain,(
% 2.56/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/0.98    inference(cnf_transformation,[],[f26])).
% 2.56/0.98  
% 2.56/0.98  fof(f74,plain,(
% 2.56/0.98    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.56/0.98    inference(cnf_transformation,[],[f46])).
% 2.56/0.98  
% 2.56/0.98  fof(f11,axiom,(
% 2.56/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f33,plain,(
% 2.56/0.98    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.56/0.98    inference(ennf_transformation,[],[f11])).
% 2.56/0.98  
% 2.56/0.98  fof(f34,plain,(
% 2.56/0.98    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.56/0.98    inference(flattening,[],[f33])).
% 2.56/0.98  
% 2.56/0.98  fof(f64,plain,(
% 2.56/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f34])).
% 2.56/0.98  
% 2.56/0.98  fof(f75,plain,(
% 2.56/0.98    v2_funct_1(sK2)),
% 2.56/0.98    inference(cnf_transformation,[],[f46])).
% 2.56/0.98  
% 2.56/0.98  fof(f4,axiom,(
% 2.56/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f21,plain,(
% 2.56/0.98    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.56/0.98    inference(ennf_transformation,[],[f4])).
% 2.56/0.98  
% 2.56/0.98  fof(f22,plain,(
% 2.56/0.98    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.56/0.98    inference(flattening,[],[f21])).
% 2.56/0.98  
% 2.56/0.98  fof(f53,plain,(
% 2.56/0.98    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f22])).
% 2.56/0.98  
% 2.56/0.98  fof(f14,axiom,(
% 2.56/0.98    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f38,plain,(
% 2.56/0.98    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.56/0.98    inference(ennf_transformation,[],[f14])).
% 2.56/0.98  
% 2.56/0.98  fof(f39,plain,(
% 2.56/0.98    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.56/0.98    inference(flattening,[],[f38])).
% 2.56/0.98  
% 2.56/0.98  fof(f67,plain,(
% 2.56/0.98    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f39])).
% 2.56/0.98  
% 2.56/0.98  fof(f5,axiom,(
% 2.56/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f23,plain,(
% 2.56/0.98    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.56/0.98    inference(ennf_transformation,[],[f5])).
% 2.56/0.98  
% 2.56/0.98  fof(f24,plain,(
% 2.56/0.98    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.56/0.98    inference(flattening,[],[f23])).
% 2.56/0.98  
% 2.56/0.98  fof(f54,plain,(
% 2.56/0.98    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f24])).
% 2.56/0.98  
% 2.56/0.98  fof(f3,axiom,(
% 2.56/0.98    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f19,plain,(
% 2.56/0.98    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.56/0.98    inference(ennf_transformation,[],[f3])).
% 2.56/0.98  
% 2.56/0.98  fof(f20,plain,(
% 2.56/0.98    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.56/0.98    inference(flattening,[],[f19])).
% 2.56/0.98  
% 2.56/0.98  fof(f51,plain,(
% 2.56/0.98    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f20])).
% 2.56/0.98  
% 2.56/0.98  fof(f50,plain,(
% 2.56/0.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f20])).
% 2.56/0.98  
% 2.56/0.98  fof(f63,plain,(
% 2.56/0.98    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f34])).
% 2.56/0.98  
% 2.56/0.98  fof(f10,axiom,(
% 2.56/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.56/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/0.98  
% 2.56/0.98  fof(f31,plain,(
% 2.56/0.98    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.56/0.98    inference(ennf_transformation,[],[f10])).
% 2.56/0.98  
% 2.56/0.98  fof(f32,plain,(
% 2.56/0.98    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.56/0.98    inference(flattening,[],[f31])).
% 2.56/0.98  
% 2.56/0.98  fof(f61,plain,(
% 2.56/0.98    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.56/0.98    inference(cnf_transformation,[],[f32])).
% 2.56/0.98  
% 2.56/0.98  fof(f76,plain,(
% 2.56/0.98    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.56/0.98    inference(cnf_transformation,[],[f46])).
% 2.56/0.98  
% 2.56/0.98  cnf(c_24,negated_conjecture,
% 2.56/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.56/0.98      inference(cnf_transformation,[],[f73]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_614,negated_conjecture,
% 2.56/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_24]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1055,plain,
% 2.56/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_18,plain,
% 2.56/0.98      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f65]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_29,negated_conjecture,
% 2.56/0.98      ( l1_struct_0(sK0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f68]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_339,plain,
% 2.56/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_340,plain,
% 2.56/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_339]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_610,plain,
% 2.56/0.98      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_340]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_27,negated_conjecture,
% 2.56/0.98      ( l1_struct_0(sK1) ),
% 2.56/0.98      inference(cnf_transformation,[],[f70]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_334,plain,
% 2.56/0.98      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_335,plain,
% 2.56/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_334]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_611,plain,
% 2.56/0.98      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_335]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1077,plain,
% 2.56/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.56/0.98      inference(light_normalisation,[status(thm)],[c_1055,c_610,c_611]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_10,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/0.98      | v1_partfun1(X0,X1)
% 2.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/0.98      | v1_xboole_0(X2)
% 2.56/0.98      | ~ v1_funct_1(X0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f58]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_19,plain,
% 2.56/0.98      ( v2_struct_0(X0)
% 2.56/0.98      | ~ l1_struct_0(X0)
% 2.56/0.98      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.56/0.98      inference(cnf_transformation,[],[f66]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_28,negated_conjecture,
% 2.56/0.98      ( ~ v2_struct_0(sK1) ),
% 2.56/0.98      inference(cnf_transformation,[],[f69]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_321,plain,
% 2.56/0.98      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_322,plain,
% 2.56/0.98      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_321]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_42,plain,
% 2.56/0.98      ( v2_struct_0(sK1)
% 2.56/0.98      | ~ l1_struct_0(sK1)
% 2.56/0.98      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_19]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_324,plain,
% 2.56/0.98      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_322,c_28,c_27,c_42]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_346,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/0.98      | v1_partfun1(X0,X1)
% 2.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/0.98      | ~ v1_funct_1(X0)
% 2.56/0.98      | u1_struct_0(sK1) != X2 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_10,c_324]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_347,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.56/0.98      | v1_partfun1(X0,X1)
% 2.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.56/0.98      | ~ v1_funct_1(X0) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_346]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_13,plain,
% 2.56/0.98      ( ~ v1_partfun1(X0,X1)
% 2.56/0.98      | ~ v4_relat_1(X0,X1)
% 2.56/0.98      | ~ v1_relat_1(X0)
% 2.56/0.98      | k1_relat_1(X0) = X1 ),
% 2.56/0.98      inference(cnf_transformation,[],[f59]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_443,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.56/0.98      | ~ v4_relat_1(X0,X1)
% 2.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.56/0.98      | ~ v1_funct_1(X0)
% 2.56/0.98      | ~ v1_relat_1(X0)
% 2.56/0.98      | k1_relat_1(X0) = X1 ),
% 2.56/0.98      inference(resolution,[status(thm)],[c_347,c_13]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_8,plain,
% 2.56/0.98      ( v4_relat_1(X0,X1)
% 2.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.56/0.98      inference(cnf_transformation,[],[f55]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_459,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 2.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 2.56/0.98      | ~ v1_funct_1(X0)
% 2.56/0.98      | ~ v1_relat_1(X0)
% 2.56/0.98      | k1_relat_1(X0) = X1 ),
% 2.56/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_443,c_8]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_608,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0_51,X0_52,u1_struct_0(sK1))
% 2.56/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1))))
% 2.56/0.98      | ~ v1_funct_1(X0_51)
% 2.56/0.98      | ~ v1_relat_1(X0_51)
% 2.56/0.98      | k1_relat_1(X0_51) = X0_52 ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_459]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1060,plain,
% 2.56/0.98      ( k1_relat_1(X0_51) = X0_52
% 2.56/0.98      | v1_funct_2(X0_51,X0_52,u1_struct_0(sK1)) != iProver_top
% 2.56/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,u1_struct_0(sK1)))) != iProver_top
% 2.56/0.98      | v1_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v1_relat_1(X0_51) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1147,plain,
% 2.56/0.98      ( k1_relat_1(X0_51) = X0_52
% 2.56/0.98      | v1_funct_2(X0_51,X0_52,k2_struct_0(sK1)) != iProver_top
% 2.56/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top
% 2.56/0.98      | v1_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v1_relat_1(X0_51) != iProver_top ),
% 2.56/0.98      inference(light_normalisation,[status(thm)],[c_1060,c_611]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1479,plain,
% 2.56/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.56/0.98      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.56/0.98      | v1_funct_1(sK2) != iProver_top
% 2.56/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_1077,c_1147]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_26,negated_conjecture,
% 2.56/0.98      ( v1_funct_1(sK2) ),
% 2.56/0.98      inference(cnf_transformation,[],[f71]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_33,plain,
% 2.56/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_35,plain,
% 2.56/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_25,negated_conjecture,
% 2.56/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.56/0.98      inference(cnf_transformation,[],[f72]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_613,negated_conjecture,
% 2.56/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_25]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1056,plain,
% 2.56/0.98      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1071,plain,
% 2.56/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.56/0.98      inference(light_normalisation,[status(thm)],[c_1056,c_610,c_611]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_0,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.56/0.98      | ~ v1_relat_1(X1)
% 2.56/0.98      | v1_relat_1(X0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f47]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_629,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 2.56/0.98      | ~ v1_relat_1(X1_51)
% 2.56/0.98      | v1_relat_1(X0_51) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_0]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1287,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.56/0.98      | v1_relat_1(X0_51)
% 2.56/0.98      | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_629]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1393,plain,
% 2.56/0.98      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.56/0.98      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.56/0.98      | v1_relat_1(sK2) ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_1287]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1394,plain,
% 2.56/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.56/0.98      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.56/0.98      | v1_relat_1(sK2) = iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1393]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1,plain,
% 2.56/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.56/0.98      inference(cnf_transformation,[],[f48]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_628,plain,
% 2.56/0.98      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_1]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1416,plain,
% 2.56/0.98      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_628]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1417,plain,
% 2.56/0.98      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_1416]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2147,plain,
% 2.56/0.98      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_1479,c_33,c_35,c_1071,c_1394,c_1417]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_9,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f56]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_621,plain,
% 2.56/0.98      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.56/0.98      | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_9]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1049,plain,
% 2.56/0.98      ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
% 2.56/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1423,plain,
% 2.56/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_1077,c_1049]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_23,negated_conjecture,
% 2.56/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.56/0.98      inference(cnf_transformation,[],[f74]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_615,negated_conjecture,
% 2.56/0.98      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_23]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1074,plain,
% 2.56/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.56/0.98      inference(light_normalisation,[status(thm)],[c_615,c_610,c_611]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1544,plain,
% 2.56/0.98      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.56/0.98      inference(demodulation,[status(thm)],[c_1423,c_1074]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1546,plain,
% 2.56/0.98      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.56/0.98      inference(demodulation,[status(thm)],[c_1544,c_1423]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2151,plain,
% 2.56/0.98      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.56/0.98      inference(demodulation,[status(thm)],[c_2147,c_1546]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_15,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/0.98      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.56/0.98      | ~ v1_funct_1(X0)
% 2.56/0.98      | ~ v2_funct_1(X0)
% 2.56/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.56/0.98      inference(cnf_transformation,[],[f64]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_620,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.56/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.56/0.98      | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
% 2.56/0.98      | ~ v1_funct_1(X0_51)
% 2.56/0.98      | ~ v2_funct_1(X0_51)
% 2.56/0.98      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_15]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1050,plain,
% 2.56/0.98      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.56/0.98      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.56/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.56/0.98      | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
% 2.56/0.98      | v1_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v2_funct_1(X0_51) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2614,plain,
% 2.56/0.98      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.56/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.56/0.98      | v1_funct_1(sK2) != iProver_top
% 2.56/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_2151,c_1050]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_22,negated_conjecture,
% 2.56/0.98      ( v2_funct_1(sK2) ),
% 2.56/0.98      inference(cnf_transformation,[],[f75]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_36,plain,
% 2.56/0.98      ( v2_funct_1(sK2) = iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1548,plain,
% 2.56/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.56/0.98      inference(demodulation,[status(thm)],[c_1544,c_1077]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2150,plain,
% 2.56/0.98      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.56/0.98      inference(demodulation,[status(thm)],[c_2147,c_1548]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1549,plain,
% 2.56/0.98      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.56/0.98      inference(demodulation,[status(thm)],[c_1544,c_1071]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2152,plain,
% 2.56/0.98      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.56/0.98      inference(demodulation,[status(thm)],[c_2147,c_1549]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_3116,plain,
% 2.56/0.98      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_2614,c_33,c_36,c_2150,c_2152]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_3122,plain,
% 2.56/0.98      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_3116,c_1049]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_612,negated_conjecture,
% 2.56/0.98      ( v1_funct_1(sK2) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_26]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1057,plain,
% 2.56/0.98      ( v1_funct_1(sK2) = iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_5,plain,
% 2.56/0.98      ( ~ v1_funct_1(X0)
% 2.56/0.98      | ~ v2_funct_1(X0)
% 2.56/0.98      | ~ v1_relat_1(X0)
% 2.56/0.98      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f53]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_624,plain,
% 2.56/0.98      ( ~ v1_funct_1(X0_51)
% 2.56/0.98      | ~ v2_funct_1(X0_51)
% 2.56/0.98      | ~ v1_relat_1(X0_51)
% 2.56/0.98      | k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_5]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1046,plain,
% 2.56/0.98      ( k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51)
% 2.56/0.98      | v1_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v2_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v1_relat_1(X0_51) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1807,plain,
% 2.56/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.56/0.98      | v2_funct_1(sK2) != iProver_top
% 2.56/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_1057,c_1046]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_680,plain,
% 2.56/0.98      ( ~ v1_funct_1(sK2)
% 2.56/0.98      | ~ v2_funct_1(sK2)
% 2.56/0.98      | ~ v1_relat_1(sK2)
% 2.56/0.98      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_624]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2069,plain,
% 2.56/0.98      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_1807,c_26,c_24,c_22,c_680,c_1393,c_1416]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_3129,plain,
% 2.56/0.98      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.56/0.98      inference(light_normalisation,[status(thm)],[c_3122,c_2069]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_20,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/0.98      | ~ v1_funct_1(X0)
% 2.56/0.98      | ~ v2_funct_1(X0)
% 2.56/0.98      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.56/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.56/0.98      inference(cnf_transformation,[],[f67]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_617,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.56/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.56/0.98      | ~ v1_funct_1(X0_51)
% 2.56/0.98      | ~ v2_funct_1(X0_51)
% 2.56/0.98      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.56/0.98      | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_20]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1053,plain,
% 2.56/0.98      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.56/0.98      | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51)
% 2.56/0.98      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.56/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.56/0.98      | v1_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v2_funct_1(X0_51) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_3137,plain,
% 2.56/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.56/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.56/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.56/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.56/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_3129,c_1053]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_7,plain,
% 2.56/0.98      ( ~ v1_funct_1(X0)
% 2.56/0.98      | ~ v2_funct_1(X0)
% 2.56/0.98      | ~ v1_relat_1(X0)
% 2.56/0.98      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.56/0.98      inference(cnf_transformation,[],[f54]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_622,plain,
% 2.56/0.98      ( ~ v1_funct_1(X0_51)
% 2.56/0.98      | ~ v2_funct_1(X0_51)
% 2.56/0.98      | ~ v1_relat_1(X0_51)
% 2.56/0.98      | k2_funct_1(k2_funct_1(X0_51)) = X0_51 ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_7]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1048,plain,
% 2.56/0.98      ( k2_funct_1(k2_funct_1(X0_51)) = X0_51
% 2.56/0.98      | v1_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v2_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v1_relat_1(X0_51) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1778,plain,
% 2.56/0.98      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.56/0.98      | v2_funct_1(sK2) != iProver_top
% 2.56/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_1057,c_1048]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_686,plain,
% 2.56/0.98      ( ~ v1_funct_1(sK2)
% 2.56/0.98      | ~ v2_funct_1(sK2)
% 2.56/0.98      | ~ v1_relat_1(sK2)
% 2.56/0.98      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_622]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2062,plain,
% 2.56/0.98      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_1778,c_26,c_24,c_22,c_686,c_1393,c_1416]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_3157,plain,
% 2.56/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.56/0.98      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.56/0.98      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.56/0.98      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.56/0.98      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.56/0.98      inference(light_normalisation,[status(thm)],[c_3137,c_2062]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2,plain,
% 2.56/0.98      ( ~ v1_funct_1(X0)
% 2.56/0.98      | ~ v2_funct_1(X0)
% 2.56/0.98      | v2_funct_1(k2_funct_1(X0))
% 2.56/0.98      | ~ v1_relat_1(X0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f51]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_627,plain,
% 2.56/0.98      ( ~ v1_funct_1(X0_51)
% 2.56/0.98      | ~ v2_funct_1(X0_51)
% 2.56/0.98      | v2_funct_1(k2_funct_1(X0_51))
% 2.56/0.98      | ~ v1_relat_1(X0_51) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_2]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_670,plain,
% 2.56/0.98      ( v1_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v2_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v2_funct_1(k2_funct_1(X0_51)) = iProver_top
% 2.56/0.98      | v1_relat_1(X0_51) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_627]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_672,plain,
% 2.56/0.98      ( v1_funct_1(sK2) != iProver_top
% 2.56/0.98      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.56/0.98      | v2_funct_1(sK2) != iProver_top
% 2.56/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_670]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_3,plain,
% 2.56/0.98      ( ~ v1_funct_1(X0)
% 2.56/0.98      | v1_funct_1(k2_funct_1(X0))
% 2.56/0.98      | ~ v2_funct_1(X0)
% 2.56/0.98      | ~ v1_relat_1(X0) ),
% 2.56/0.98      inference(cnf_transformation,[],[f50]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_626,plain,
% 2.56/0.98      ( ~ v1_funct_1(X0_51)
% 2.56/0.98      | v1_funct_1(k2_funct_1(X0_51))
% 2.56/0.98      | ~ v2_funct_1(X0_51)
% 2.56/0.98      | ~ v1_relat_1(X0_51) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_3]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_673,plain,
% 2.56/0.98      ( v1_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v1_funct_1(k2_funct_1(X0_51)) = iProver_top
% 2.56/0.98      | v2_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v1_relat_1(X0_51) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_675,plain,
% 2.56/0.98      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.56/0.98      | v1_funct_1(sK2) != iProver_top
% 2.56/0.98      | v2_funct_1(sK2) != iProver_top
% 2.56/0.98      | v1_relat_1(sK2) != iProver_top ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_673]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_16,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/0.98      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/0.98      | ~ v1_funct_1(X0)
% 2.56/0.98      | ~ v2_funct_1(X0)
% 2.56/0.98      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.56/0.98      inference(cnf_transformation,[],[f63]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_619,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.56/0.98      | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52)
% 2.56/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.56/0.98      | ~ v1_funct_1(X0_51)
% 2.56/0.98      | ~ v2_funct_1(X0_51)
% 2.56/0.98      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_16]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1051,plain,
% 2.56/0.98      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.56/0.98      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.56/0.98      | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52) = iProver_top
% 2.56/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.56/0.98      | v1_funct_1(X0_51) != iProver_top
% 2.56/0.98      | v2_funct_1(X0_51) != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2613,plain,
% 2.56/0.98      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.56/0.98      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.56/0.98      | v1_funct_1(sK2) != iProver_top
% 2.56/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_2151,c_1051]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_3657,plain,
% 2.56/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_3157,c_33,c_35,c_36,c_672,c_675,c_1394,c_1417,c_2150,
% 2.56/0.98                 c_2152,c_2613,c_2614]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2612,plain,
% 2.56/0.98      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.56/0.98      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.56/0.98      | v1_funct_1(sK2) != iProver_top
% 2.56/0.98      | v2_funct_1(sK2) != iProver_top ),
% 2.56/0.98      inference(superposition,[status(thm)],[c_2151,c_1053]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2771,plain,
% 2.56/0.98      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.56/0.98      inference(global_propositional_subsumption,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_2612,c_33,c_36,c_2150,c_2152]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_14,plain,
% 2.56/0.98      ( r2_funct_2(X0,X1,X2,X2)
% 2.56/0.98      | ~ v1_funct_2(X2,X0,X1)
% 2.56/0.98      | ~ v1_funct_2(X3,X0,X1)
% 2.56/0.98      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.56/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.56/0.98      | ~ v1_funct_1(X2)
% 2.56/0.98      | ~ v1_funct_1(X3) ),
% 2.56/0.98      inference(cnf_transformation,[],[f61]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_21,negated_conjecture,
% 2.56/0.98      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.56/0.98      inference(cnf_transformation,[],[f76]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_369,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/0.98      | ~ v1_funct_2(X3,X1,X2)
% 2.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/0.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/0.98      | ~ v1_funct_1(X0)
% 2.56/0.98      | ~ v1_funct_1(X3)
% 2.56/0.98      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.56/0.98      | u1_struct_0(sK1) != X2
% 2.56/0.98      | u1_struct_0(sK0) != X1
% 2.56/0.98      | sK2 != X0 ),
% 2.56/0.98      inference(resolution_lifted,[status(thm)],[c_14,c_21]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_370,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.56/0.98      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.56/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.56/0.98      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.56/0.98      | ~ v1_funct_1(X0)
% 2.56/0.98      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.56/0.98      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.56/0.98      inference(unflattening,[status(thm)],[c_369]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_609,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.56/0.98      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.56/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.56/0.98      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.56/0.98      | ~ v1_funct_1(X0_51)
% 2.56/0.98      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.56/0.98      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.56/0.98      inference(subtyping,[status(esa)],[c_370]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_631,plain,
% 2.56/0.98      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.56/0.98      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.56/0.98      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.56/0.98      | sP0_iProver_split
% 2.56/0.98      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.56/0.98      inference(splitting,
% 2.56/0.98                [splitting(split),new_symbols(definition,[])],
% 2.56/0.98                [c_609]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1058,plain,
% 2.56/0.98      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.56/0.98      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.56/0.98      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.56/0.98      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.56/0.98      | sP0_iProver_split = iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1206,plain,
% 2.56/0.98      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.56/0.98      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.56/0.98      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.56/0.98      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.56/0.98      | sP0_iProver_split = iProver_top ),
% 2.56/0.98      inference(light_normalisation,[status(thm)],[c_1058,c_610,c_611]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_630,plain,
% 2.56/0.98      ( ~ v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.56/0.98      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.56/0.98      | ~ v1_funct_1(X0_51)
% 2.56/0.98      | ~ sP0_iProver_split ),
% 2.56/0.98      inference(splitting,
% 2.56/0.98                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.56/0.98                [c_609]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1059,plain,
% 2.56/0.98      ( v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.56/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.56/0.98      | v1_funct_1(X0_51) != iProver_top
% 2.56/0.98      | sP0_iProver_split != iProver_top ),
% 2.56/0.98      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1138,plain,
% 2.56/0.98      ( v1_funct_2(X0_51,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.56/0.98      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.56/0.98      | v1_funct_1(X0_51) != iProver_top
% 2.56/0.98      | sP0_iProver_split != iProver_top ),
% 2.56/0.98      inference(light_normalisation,[status(thm)],[c_1059,c_610,c_611]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_1212,plain,
% 2.56/0.98      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.56/0.98      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.56/0.98      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.56/0.98      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.56/0.98      inference(forward_subsumption_resolution,
% 2.56/0.98                [status(thm)],
% 2.56/0.98                [c_1206,c_1138]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2362,plain,
% 2.56/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 2.56/0.98      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/0.98      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.56/0.98      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.56/0.98      inference(light_normalisation,[status(thm)],[c_1212,c_1544,c_2147]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_2774,plain,
% 2.56/0.98      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.56/0.98      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/0.98      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.56/0.98      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.56/0.98      inference(demodulation,[status(thm)],[c_2771,c_2362]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_3660,plain,
% 2.56/0.98      ( sK2 != sK2
% 2.56/0.98      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/0.98      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.56/0.98      | v1_funct_1(sK2) != iProver_top ),
% 2.56/0.98      inference(demodulation,[status(thm)],[c_3657,c_2774]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_633,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.56/0.98  
% 2.56/0.98  cnf(c_663,plain,
% 2.56/0.98      ( sK2 = sK2 ),
% 2.56/0.98      inference(instantiation,[status(thm)],[c_633]) ).
% 2.56/0.98  
% 2.56/0.98  cnf(contradiction,plain,
% 2.56/0.98      ( $false ),
% 2.56/0.98      inference(minisat,[status(thm)],[c_3660,c_2152,c_2150,c_663,c_33]) ).
% 2.56/0.98  
% 2.56/0.98  
% 2.56/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 2.56/0.98  
% 2.56/0.98  ------                               Statistics
% 2.56/0.98  
% 2.56/0.98  ------ General
% 2.56/0.98  
% 2.56/0.98  abstr_ref_over_cycles:                  0
% 2.56/0.98  abstr_ref_under_cycles:                 0
% 2.56/0.98  gc_basic_clause_elim:                   0
% 2.56/0.98  forced_gc_time:                         0
% 2.56/0.98  parsing_time:                           0.016
% 2.56/0.98  unif_index_cands_time:                  0.
% 2.56/0.98  unif_index_add_time:                    0.
% 2.56/0.98  orderings_time:                         0.
% 2.56/0.98  out_proof_time:                         0.018
% 2.56/0.98  total_time:                             0.224
% 2.56/0.98  num_of_symbols:                         56
% 2.56/0.98  num_of_terms:                           3411
% 2.56/0.98  
% 2.56/0.98  ------ Preprocessing
% 2.56/0.98  
% 2.56/0.98  num_of_splits:                          1
% 2.56/0.98  num_of_split_atoms:                     1
% 2.56/0.98  num_of_reused_defs:                     0
% 2.56/0.98  num_eq_ax_congr_red:                    4
% 2.56/0.98  num_of_sem_filtered_clauses:            2
% 2.56/0.98  num_of_subtypes:                        4
% 2.56/0.98  monotx_restored_types:                  1
% 2.56/0.98  sat_num_of_epr_types:                   0
% 2.56/0.98  sat_num_of_non_cyclic_types:            0
% 2.56/0.98  sat_guarded_non_collapsed_types:        1
% 2.56/0.98  num_pure_diseq_elim:                    0
% 2.56/0.98  simp_replaced_by:                       0
% 2.56/0.98  res_preprocessed:                       131
% 2.56/0.98  prep_upred:                             0
% 2.56/0.98  prep_unflattend:                        11
% 2.56/0.98  smt_new_axioms:                         0
% 2.56/0.98  pred_elim_cands:                        5
% 2.56/0.98  pred_elim:                              6
% 2.56/0.98  pred_elim_cl:                           7
% 2.56/0.98  pred_elim_cycles:                       9
% 2.56/0.98  merged_defs:                            0
% 2.56/0.98  merged_defs_ncl:                        0
% 2.56/0.98  bin_hyper_res:                          0
% 2.56/0.98  prep_cycles:                            4
% 2.56/0.98  pred_elim_time:                         0.004
% 2.56/0.98  splitting_time:                         0.
% 2.56/0.98  sem_filter_time:                        0.
% 2.56/0.98  monotx_time:                            0.001
% 2.56/0.98  subtype_inf_time:                       0.002
% 2.56/0.98  
% 2.56/0.98  ------ Problem properties
% 2.56/0.98  
% 2.56/0.98  clauses:                                23
% 2.56/0.98  conjectures:                            5
% 2.56/0.98  epr:                                    2
% 2.56/0.98  horn:                                   23
% 2.56/0.98  ground:                                 8
% 2.56/0.98  unary:                                  8
% 2.56/0.98  binary:                                 1
% 2.56/0.98  lits:                                   75
% 2.56/0.98  lits_eq:                                14
% 2.56/0.98  fd_pure:                                0
% 2.56/0.98  fd_pseudo:                              0
% 2.56/0.98  fd_cond:                                0
% 2.56/0.98  fd_pseudo_cond:                         1
% 2.56/0.98  ac_symbols:                             0
% 2.56/0.98  
% 2.56/0.98  ------ Propositional Solver
% 2.56/0.98  
% 2.56/0.98  prop_solver_calls:                      29
% 2.56/0.98  prop_fast_solver_calls:                 1037
% 2.56/0.98  smt_solver_calls:                       0
% 2.56/0.98  smt_fast_solver_calls:                  0
% 2.56/0.98  prop_num_of_clauses:                    1342
% 2.56/0.98  prop_preprocess_simplified:             4898
% 2.56/0.98  prop_fo_subsumed:                       50
% 2.56/0.98  prop_solver_time:                       0.
% 2.56/0.98  smt_solver_time:                        0.
% 2.56/0.98  smt_fast_solver_time:                   0.
% 2.56/0.98  prop_fast_solver_time:                  0.
% 2.56/0.98  prop_unsat_core_time:                   0.
% 2.56/0.98  
% 2.56/0.98  ------ QBF
% 2.56/0.98  
% 2.56/0.98  qbf_q_res:                              0
% 2.56/0.98  qbf_num_tautologies:                    0
% 2.56/0.98  qbf_prep_cycles:                        0
% 2.56/0.98  
% 2.56/0.98  ------ BMC1
% 2.56/0.98  
% 2.56/0.98  bmc1_current_bound:                     -1
% 2.56/0.98  bmc1_last_solved_bound:                 -1
% 2.56/0.98  bmc1_unsat_core_size:                   -1
% 2.56/0.98  bmc1_unsat_core_parents_size:           -1
% 2.56/0.98  bmc1_merge_next_fun:                    0
% 2.56/0.98  bmc1_unsat_core_clauses_time:           0.
% 2.56/0.98  
% 2.56/0.98  ------ Instantiation
% 2.56/0.98  
% 2.56/0.98  inst_num_of_clauses:                    496
% 2.56/0.98  inst_num_in_passive:                    98
% 2.56/0.98  inst_num_in_active:                     241
% 2.56/0.98  inst_num_in_unprocessed:                157
% 2.56/0.98  inst_num_of_loops:                      260
% 2.56/0.98  inst_num_of_learning_restarts:          0
% 2.56/0.98  inst_num_moves_active_passive:          15
% 2.56/0.98  inst_lit_activity:                      0
% 2.56/0.98  inst_lit_activity_moves:                0
% 2.56/0.98  inst_num_tautologies:                   0
% 2.56/0.98  inst_num_prop_implied:                  0
% 2.56/0.98  inst_num_existing_simplified:           0
% 2.56/0.98  inst_num_eq_res_simplified:             0
% 2.56/0.98  inst_num_child_elim:                    0
% 2.56/0.98  inst_num_of_dismatching_blockings:      86
% 2.56/0.98  inst_num_of_non_proper_insts:           416
% 2.56/0.98  inst_num_of_duplicates:                 0
% 2.56/0.98  inst_inst_num_from_inst_to_res:         0
% 2.56/0.98  inst_dismatching_checking_time:         0.
% 2.56/0.98  
% 2.56/0.98  ------ Resolution
% 2.56/0.98  
% 2.56/0.98  res_num_of_clauses:                     0
% 2.56/0.98  res_num_in_passive:                     0
% 2.56/0.98  res_num_in_active:                      0
% 2.56/0.98  res_num_of_loops:                       135
% 2.56/0.98  res_forward_subset_subsumed:            48
% 2.56/0.98  res_backward_subset_subsumed:           0
% 2.56/0.98  res_forward_subsumed:                   0
% 2.56/0.98  res_backward_subsumed:                  0
% 2.56/0.98  res_forward_subsumption_resolution:     1
% 2.56/0.98  res_backward_subsumption_resolution:    0
% 2.56/0.98  res_clause_to_clause_subsumption:       132
% 2.56/0.98  res_orphan_elimination:                 0
% 2.56/0.98  res_tautology_del:                      44
% 2.56/0.98  res_num_eq_res_simplified:              0
% 2.56/0.98  res_num_sel_changes:                    0
% 2.56/0.98  res_moves_from_active_to_pass:          0
% 2.56/0.98  
% 2.56/0.98  ------ Superposition
% 2.56/0.98  
% 2.56/0.98  sup_time_total:                         0.
% 2.56/0.98  sup_time_generating:                    0.
% 2.56/0.98  sup_time_sim_full:                      0.
% 2.56/0.98  sup_time_sim_immed:                     0.
% 2.56/0.98  
% 2.56/0.98  sup_num_of_clauses:                     44
% 2.56/0.98  sup_num_in_active:                      39
% 2.56/0.98  sup_num_in_passive:                     5
% 2.56/0.98  sup_num_of_loops:                       51
% 2.56/0.98  sup_fw_superposition:                   24
% 2.56/0.98  sup_bw_superposition:                   22
% 2.56/0.98  sup_immediate_simplified:               22
% 2.56/0.98  sup_given_eliminated:                   0
% 2.56/0.98  comparisons_done:                       0
% 2.56/0.98  comparisons_avoided:                    0
% 2.56/0.98  
% 2.56/0.98  ------ Simplifications
% 2.56/0.98  
% 2.56/0.98  
% 2.56/0.98  sim_fw_subset_subsumed:                 4
% 2.56/0.98  sim_bw_subset_subsumed:                 0
% 2.56/0.98  sim_fw_subsumed:                        3
% 2.56/0.98  sim_bw_subsumed:                        0
% 2.56/0.98  sim_fw_subsumption_res:                 1
% 2.56/0.98  sim_bw_subsumption_res:                 0
% 2.56/0.98  sim_tautology_del:                      0
% 2.56/0.98  sim_eq_tautology_del:                   14
% 2.56/0.98  sim_eq_res_simp:                        0
% 2.56/0.98  sim_fw_demodulated:                     0
% 2.56/0.98  sim_bw_demodulated:                     12
% 2.56/0.98  sim_light_normalised:                   25
% 2.56/0.98  sim_joinable_taut:                      0
% 2.56/0.98  sim_joinable_simp:                      0
% 2.56/0.98  sim_ac_normalised:                      0
% 2.56/0.98  sim_smt_subsumption:                    0
% 2.56/0.98  
%------------------------------------------------------------------------------
