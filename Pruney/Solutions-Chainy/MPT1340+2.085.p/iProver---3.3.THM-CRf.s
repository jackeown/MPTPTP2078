%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:40 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :  240 (4740 expanded)
%              Number of clauses        :  156 (1545 expanded)
%              Number of leaves         :   22 (1316 expanded)
%              Depth                    :   26
%              Number of atoms          :  869 (29194 expanded)
%              Number of equality atoms :  355 (5258 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f48,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f49,plain,(
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
    inference(flattening,[],[f48])).

fof(f53,plain,(
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

fof(f52,plain,(
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

fof(f51,plain,
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

fof(f54,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53,f52,f51])).

fof(f86,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f54])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f78,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f83,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
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

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

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
    inference(flattening,[],[f39])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f56,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f85,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f54])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f82,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f88,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
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
    inference(ennf_transformation,[],[f15])).

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

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f28,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f64,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f67,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f24,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f59,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f63,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f58,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f65,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f6,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f6])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_736,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1263,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_736])).

cnf(c_23,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_34,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_413,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_414,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_731,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_414])).

cnf(c_32,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_408,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_409,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_408])).

cnf(c_732,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_409])).

cnf(c_1293,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1263,c_731,c_732])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_743,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1257,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_1844,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1293,c_1257])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_737,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1290,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_737,c_731,c_732])).

cnf(c_1846,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1844,c_1290])).

cnf(c_1882,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1846,c_1293])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_16,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f70])).

cnf(c_494,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_19,c_16])).

cnf(c_13,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_498,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_494,c_13])).

cnf(c_729,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k1_relat_1(X0_54) = X0_55
    | k1_xboole_0 = X1_55 ),
    inference(subtyping,[status(esa)],[c_498])).

cnf(c_1268,plain,
    ( k1_relat_1(X0_54) = X0_55
    | k1_xboole_0 = X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_754,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_797,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_849,plain,
    ( k1_relat_1(X0_54) = X0_55
    | k1_xboole_0 = X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_729])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_755,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
    | ~ v1_relat_1(X1_54)
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1544,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_relat_1(X0_54)
    | ~ v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_1545,plain,
    ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_relat_1(X0_54) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1544])).

cnf(c_3845,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | k1_xboole_0 = X1_55
    | k1_relat_1(X0_54) = X0_55 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1268,c_797,c_849,c_1545])).

cnf(c_3846,plain,
    ( k1_relat_1(X0_54) = X0_55
    | k1_xboole_0 = X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_3845])).

cnf(c_3854,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1882,c_3846])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_735,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1264,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_735])).

cnf(c_1287,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1264,c_731,c_732])).

cnf(c_1883,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1846,c_1287])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_381,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_399,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_381,c_33])).

cnf(c_400,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_399])).

cnf(c_383,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_381])).

cnf(c_402,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_400,c_33,c_32,c_383])).

cnf(c_733,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_402])).

cnf(c_1279,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_732,c_733])).

cnf(c_1884,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1846,c_1279])).

cnf(c_3958,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3854,c_38,c_1883,c_1884])).

cnf(c_1880,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1846,c_1844])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_739,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1261,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_2785,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1880,c_1261])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_41,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3549,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2785,c_38,c_41,c_1882,c_1883])).

cnf(c_17,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_26,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_420,plain,
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
    inference(resolution_lifted,[status(thm)],[c_17,c_26])).

cnf(c_421,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_730,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_421])).

cnf(c_757,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_730])).

cnf(c_1266,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_1465,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1266,c_731,c_732])).

cnf(c_756,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_730])).

cnf(c_1267,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_1358,plain,
    ( v1_funct_2(X0_54,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1267,c_731,c_732])).

cnf(c_1471,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1465,c_1358])).

cnf(c_1881,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1846,c_1471])).

cnf(c_3552,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3549,c_1881])).

cnf(c_3961,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3958,c_3552])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_742,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1258,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_3263,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1880,c_1258])).

cnf(c_3555,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3263,c_38,c_41,c_1882,c_1883])).

cnf(c_3561,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3555,c_1257])).

cnf(c_738,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1262,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_748,plain,
    ( ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1252,plain,
    ( k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54)
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_1990,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1252])).

cnf(c_812,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_1635,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_1722,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_2218,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1990,c_31,c_29,c_27,c_812,c_1635,c_1722])).

cnf(c_3568,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3561,c_2218])).

cnf(c_3684,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3568,c_1261])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_744,plain,
    ( ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1256,plain,
    ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_1967,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1256])).

cnf(c_824,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_744])).

cnf(c_2212,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1967,c_31,c_29,c_27,c_824,c_1635,c_1722])).

cnf(c_3699,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3684,c_2212])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_753,plain,
    ( ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_funct_1(X0_54))
    | ~ v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_800,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_funct_1(X0_54)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_802,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_800])).

cnf(c_1636,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1635])).

cnf(c_1723,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1722])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_741,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1259,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_2689,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1880,c_1259])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_747,plain,
    ( ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k1_relat_1(k2_funct_1(X0_54)) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1253,plain,
    ( k1_relat_1(k2_funct_1(X0_54)) = k2_relat_1(X0_54)
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_2126,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1253])).

cnf(c_815,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_2297,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2126,c_31,c_29,c_27,c_815,c_1635,c_1722])).

cnf(c_5,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_751,plain,
    ( v2_funct_1(X0_54)
    | ~ v2_funct_1(k5_relat_1(X1_54,X0_54))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | ~ v1_relat_1(X0_54)
    | ~ v1_relat_1(X1_54)
    | k1_relat_1(X0_54) != k2_relat_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1249,plain,
    ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
    | v2_funct_1(X0_54) = iProver_top
    | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(X1_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_2300,plain,
    ( k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2297,c_1249])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_752,plain,
    ( ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | v1_relat_1(k2_funct_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_803,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k2_funct_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_805,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_803])).

cnf(c_2956,plain,
    ( v1_relat_1(X0_54) != iProver_top
    | k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2300,c_38,c_40,c_802,c_805,c_1636,c_1723])).

cnf(c_2957,plain,
    ( k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_2956])).

cnf(c_2968,plain,
    ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2957])).

cnf(c_11,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_745,plain,
    ( ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_relat_1(k1_relat_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1255,plain,
    ( k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_relat_1(k1_relat_1(X0_54))
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_2598,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1262,c_1255])).

cnf(c_821,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_745])).

cnf(c_2788,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2598,c_31,c_29,c_27,c_821,c_1635,c_1722])).

cnf(c_2973,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2968,c_2788])).

cnf(c_2980,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2973,c_38,c_40,c_1636,c_1723])).

cnf(c_7,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_749,plain,
    ( v2_funct_1(k6_relat_1(X0_55)) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1251,plain,
    ( v2_funct_1(k6_relat_1(X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_2986,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2980,c_1251])).

cnf(c_3715,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3699,c_38,c_40,c_41,c_802,c_1636,c_1723,c_1882,c_1883,c_2689,c_2986,c_3263])).

cnf(c_3962,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3958,c_3715])).

cnf(c_3987,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_3962])).

cnf(c_3990,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3961,c_3987])).

cnf(c_3991,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3990])).

cnf(c_3967,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3958,c_1882])).

cnf(c_3969,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3958,c_1883])).

cnf(c_3995,plain,
    ( v1_funct_1(sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3991,c_3967,c_3969])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3995,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:08:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.81/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.81/1.00  
% 2.81/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.81/1.00  
% 2.81/1.00  ------  iProver source info
% 2.81/1.00  
% 2.81/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.81/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.81/1.00  git: non_committed_changes: false
% 2.81/1.00  git: last_make_outside_of_git: false
% 2.81/1.00  
% 2.81/1.00  ------ 
% 2.81/1.00  
% 2.81/1.00  ------ Input Options
% 2.81/1.00  
% 2.81/1.00  --out_options                           all
% 2.81/1.00  --tptp_safe_out                         true
% 2.81/1.00  --problem_path                          ""
% 2.81/1.00  --include_path                          ""
% 2.81/1.00  --clausifier                            res/vclausify_rel
% 2.81/1.00  --clausifier_options                    --mode clausify
% 2.81/1.00  --stdin                                 false
% 2.81/1.00  --stats_out                             all
% 2.81/1.00  
% 2.81/1.00  ------ General Options
% 2.81/1.00  
% 2.81/1.00  --fof                                   false
% 2.81/1.00  --time_out_real                         305.
% 2.81/1.00  --time_out_virtual                      -1.
% 2.81/1.00  --symbol_type_check                     false
% 2.81/1.00  --clausify_out                          false
% 2.81/1.00  --sig_cnt_out                           false
% 2.81/1.00  --trig_cnt_out                          false
% 2.81/1.00  --trig_cnt_out_tolerance                1.
% 2.81/1.00  --trig_cnt_out_sk_spl                   false
% 2.81/1.00  --abstr_cl_out                          false
% 2.81/1.00  
% 2.81/1.00  ------ Global Options
% 2.81/1.00  
% 2.81/1.00  --schedule                              default
% 2.81/1.00  --add_important_lit                     false
% 2.81/1.00  --prop_solver_per_cl                    1000
% 2.81/1.00  --min_unsat_core                        false
% 2.81/1.00  --soft_assumptions                      false
% 2.81/1.00  --soft_lemma_size                       3
% 2.81/1.00  --prop_impl_unit_size                   0
% 2.81/1.00  --prop_impl_unit                        []
% 2.81/1.00  --share_sel_clauses                     true
% 2.81/1.00  --reset_solvers                         false
% 2.81/1.00  --bc_imp_inh                            [conj_cone]
% 2.81/1.00  --conj_cone_tolerance                   3.
% 2.81/1.00  --extra_neg_conj                        none
% 2.81/1.00  --large_theory_mode                     true
% 2.81/1.00  --prolific_symb_bound                   200
% 2.81/1.00  --lt_threshold                          2000
% 2.81/1.00  --clause_weak_htbl                      true
% 2.81/1.00  --gc_record_bc_elim                     false
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing Options
% 2.81/1.00  
% 2.81/1.00  --preprocessing_flag                    true
% 2.81/1.00  --time_out_prep_mult                    0.1
% 2.81/1.00  --splitting_mode                        input
% 2.81/1.00  --splitting_grd                         true
% 2.81/1.00  --splitting_cvd                         false
% 2.81/1.00  --splitting_cvd_svl                     false
% 2.81/1.00  --splitting_nvd                         32
% 2.81/1.00  --sub_typing                            true
% 2.81/1.00  --prep_gs_sim                           true
% 2.81/1.00  --prep_unflatten                        true
% 2.81/1.00  --prep_res_sim                          true
% 2.81/1.00  --prep_upred                            true
% 2.81/1.00  --prep_sem_filter                       exhaustive
% 2.81/1.00  --prep_sem_filter_out                   false
% 2.81/1.00  --pred_elim                             true
% 2.81/1.00  --res_sim_input                         true
% 2.81/1.00  --eq_ax_congr_red                       true
% 2.81/1.00  --pure_diseq_elim                       true
% 2.81/1.00  --brand_transform                       false
% 2.81/1.00  --non_eq_to_eq                          false
% 2.81/1.00  --prep_def_merge                        true
% 2.81/1.00  --prep_def_merge_prop_impl              false
% 2.81/1.00  --prep_def_merge_mbd                    true
% 2.81/1.00  --prep_def_merge_tr_red                 false
% 2.81/1.00  --prep_def_merge_tr_cl                  false
% 2.81/1.00  --smt_preprocessing                     true
% 2.81/1.00  --smt_ac_axioms                         fast
% 2.81/1.00  --preprocessed_out                      false
% 2.81/1.00  --preprocessed_stats                    false
% 2.81/1.00  
% 2.81/1.00  ------ Abstraction refinement Options
% 2.81/1.00  
% 2.81/1.00  --abstr_ref                             []
% 2.81/1.00  --abstr_ref_prep                        false
% 2.81/1.00  --abstr_ref_until_sat                   false
% 2.81/1.00  --abstr_ref_sig_restrict                funpre
% 2.81/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/1.00  --abstr_ref_under                       []
% 2.81/1.00  
% 2.81/1.00  ------ SAT Options
% 2.81/1.00  
% 2.81/1.00  --sat_mode                              false
% 2.81/1.00  --sat_fm_restart_options                ""
% 2.81/1.00  --sat_gr_def                            false
% 2.81/1.00  --sat_epr_types                         true
% 2.81/1.00  --sat_non_cyclic_types                  false
% 2.81/1.00  --sat_finite_models                     false
% 2.81/1.00  --sat_fm_lemmas                         false
% 2.81/1.00  --sat_fm_prep                           false
% 2.81/1.00  --sat_fm_uc_incr                        true
% 2.81/1.00  --sat_out_model                         small
% 2.81/1.00  --sat_out_clauses                       false
% 2.81/1.00  
% 2.81/1.00  ------ QBF Options
% 2.81/1.00  
% 2.81/1.00  --qbf_mode                              false
% 2.81/1.00  --qbf_elim_univ                         false
% 2.81/1.00  --qbf_dom_inst                          none
% 2.81/1.00  --qbf_dom_pre_inst                      false
% 2.81/1.00  --qbf_sk_in                             false
% 2.81/1.00  --qbf_pred_elim                         true
% 2.81/1.00  --qbf_split                             512
% 2.81/1.00  
% 2.81/1.00  ------ BMC1 Options
% 2.81/1.00  
% 2.81/1.00  --bmc1_incremental                      false
% 2.81/1.00  --bmc1_axioms                           reachable_all
% 2.81/1.00  --bmc1_min_bound                        0
% 2.81/1.00  --bmc1_max_bound                        -1
% 2.81/1.00  --bmc1_max_bound_default                -1
% 2.81/1.00  --bmc1_symbol_reachability              true
% 2.81/1.00  --bmc1_property_lemmas                  false
% 2.81/1.00  --bmc1_k_induction                      false
% 2.81/1.00  --bmc1_non_equiv_states                 false
% 2.81/1.00  --bmc1_deadlock                         false
% 2.81/1.00  --bmc1_ucm                              false
% 2.81/1.00  --bmc1_add_unsat_core                   none
% 2.81/1.00  --bmc1_unsat_core_children              false
% 2.81/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/1.00  --bmc1_out_stat                         full
% 2.81/1.00  --bmc1_ground_init                      false
% 2.81/1.00  --bmc1_pre_inst_next_state              false
% 2.81/1.00  --bmc1_pre_inst_state                   false
% 2.81/1.00  --bmc1_pre_inst_reach_state             false
% 2.81/1.00  --bmc1_out_unsat_core                   false
% 2.81/1.00  --bmc1_aig_witness_out                  false
% 2.81/1.00  --bmc1_verbose                          false
% 2.81/1.00  --bmc1_dump_clauses_tptp                false
% 2.81/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.81/1.00  --bmc1_dump_file                        -
% 2.81/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.81/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.81/1.00  --bmc1_ucm_extend_mode                  1
% 2.81/1.00  --bmc1_ucm_init_mode                    2
% 2.81/1.00  --bmc1_ucm_cone_mode                    none
% 2.81/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.81/1.00  --bmc1_ucm_relax_model                  4
% 2.81/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.81/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/1.00  --bmc1_ucm_layered_model                none
% 2.81/1.00  --bmc1_ucm_max_lemma_size               10
% 2.81/1.00  
% 2.81/1.00  ------ AIG Options
% 2.81/1.00  
% 2.81/1.00  --aig_mode                              false
% 2.81/1.00  
% 2.81/1.00  ------ Instantiation Options
% 2.81/1.00  
% 2.81/1.00  --instantiation_flag                    true
% 2.81/1.00  --inst_sos_flag                         false
% 2.81/1.00  --inst_sos_phase                        true
% 2.81/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/1.00  --inst_lit_sel_side                     num_symb
% 2.81/1.00  --inst_solver_per_active                1400
% 2.81/1.00  --inst_solver_calls_frac                1.
% 2.81/1.00  --inst_passive_queue_type               priority_queues
% 2.81/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/1.00  --inst_passive_queues_freq              [25;2]
% 2.81/1.00  --inst_dismatching                      true
% 2.81/1.00  --inst_eager_unprocessed_to_passive     true
% 2.81/1.00  --inst_prop_sim_given                   true
% 2.81/1.00  --inst_prop_sim_new                     false
% 2.81/1.00  --inst_subs_new                         false
% 2.81/1.00  --inst_eq_res_simp                      false
% 2.81/1.00  --inst_subs_given                       false
% 2.81/1.00  --inst_orphan_elimination               true
% 2.81/1.00  --inst_learning_loop_flag               true
% 2.81/1.00  --inst_learning_start                   3000
% 2.81/1.00  --inst_learning_factor                  2
% 2.81/1.00  --inst_start_prop_sim_after_learn       3
% 2.81/1.00  --inst_sel_renew                        solver
% 2.81/1.00  --inst_lit_activity_flag                true
% 2.81/1.00  --inst_restr_to_given                   false
% 2.81/1.00  --inst_activity_threshold               500
% 2.81/1.00  --inst_out_proof                        true
% 2.81/1.00  
% 2.81/1.00  ------ Resolution Options
% 2.81/1.00  
% 2.81/1.00  --resolution_flag                       true
% 2.81/1.00  --res_lit_sel                           adaptive
% 2.81/1.00  --res_lit_sel_side                      none
% 2.81/1.00  --res_ordering                          kbo
% 2.81/1.00  --res_to_prop_solver                    active
% 2.81/1.00  --res_prop_simpl_new                    false
% 2.81/1.00  --res_prop_simpl_given                  true
% 2.81/1.00  --res_passive_queue_type                priority_queues
% 2.81/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/1.00  --res_passive_queues_freq               [15;5]
% 2.81/1.00  --res_forward_subs                      full
% 2.81/1.00  --res_backward_subs                     full
% 2.81/1.00  --res_forward_subs_resolution           true
% 2.81/1.00  --res_backward_subs_resolution          true
% 2.81/1.00  --res_orphan_elimination                true
% 2.81/1.00  --res_time_limit                        2.
% 2.81/1.00  --res_out_proof                         true
% 2.81/1.00  
% 2.81/1.00  ------ Superposition Options
% 2.81/1.00  
% 2.81/1.00  --superposition_flag                    true
% 2.81/1.00  --sup_passive_queue_type                priority_queues
% 2.81/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.81/1.00  --demod_completeness_check              fast
% 2.81/1.00  --demod_use_ground                      true
% 2.81/1.00  --sup_to_prop_solver                    passive
% 2.81/1.00  --sup_prop_simpl_new                    true
% 2.81/1.00  --sup_prop_simpl_given                  true
% 2.81/1.00  --sup_fun_splitting                     false
% 2.81/1.00  --sup_smt_interval                      50000
% 2.81/1.00  
% 2.81/1.00  ------ Superposition Simplification Setup
% 2.81/1.00  
% 2.81/1.00  --sup_indices_passive                   []
% 2.81/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.00  --sup_full_bw                           [BwDemod]
% 2.81/1.00  --sup_immed_triv                        [TrivRules]
% 2.81/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.00  --sup_immed_bw_main                     []
% 2.81/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/1.00  
% 2.81/1.00  ------ Combination Options
% 2.81/1.00  
% 2.81/1.00  --comb_res_mult                         3
% 2.81/1.00  --comb_sup_mult                         2
% 2.81/1.00  --comb_inst_mult                        10
% 2.81/1.00  
% 2.81/1.00  ------ Debug Options
% 2.81/1.00  
% 2.81/1.00  --dbg_backtrace                         false
% 2.81/1.00  --dbg_dump_prop_clauses                 false
% 2.81/1.00  --dbg_dump_prop_clauses_file            -
% 2.81/1.00  --dbg_out_stat                          false
% 2.81/1.00  ------ Parsing...
% 2.81/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.81/1.00  ------ Proving...
% 2.81/1.00  ------ Problem Properties 
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  clauses                                 29
% 2.81/1.00  conjectures                             5
% 2.81/1.00  EPR                                     2
% 2.81/1.00  Horn                                    28
% 2.81/1.00  unary                                   10
% 2.81/1.00  binary                                  1
% 2.81/1.00  lits                                    99
% 2.81/1.00  lits eq                                 21
% 2.81/1.00  fd_pure                                 0
% 2.81/1.00  fd_pseudo                               0
% 2.81/1.00  fd_cond                                 0
% 2.81/1.00  fd_pseudo_cond                          1
% 2.81/1.00  AC symbols                              0
% 2.81/1.00  
% 2.81/1.00  ------ Schedule dynamic 5 is on 
% 2.81/1.00  
% 2.81/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  ------ 
% 2.81/1.00  Current options:
% 2.81/1.00  ------ 
% 2.81/1.00  
% 2.81/1.00  ------ Input Options
% 2.81/1.00  
% 2.81/1.00  --out_options                           all
% 2.81/1.00  --tptp_safe_out                         true
% 2.81/1.00  --problem_path                          ""
% 2.81/1.00  --include_path                          ""
% 2.81/1.00  --clausifier                            res/vclausify_rel
% 2.81/1.00  --clausifier_options                    --mode clausify
% 2.81/1.00  --stdin                                 false
% 2.81/1.00  --stats_out                             all
% 2.81/1.00  
% 2.81/1.00  ------ General Options
% 2.81/1.00  
% 2.81/1.00  --fof                                   false
% 2.81/1.00  --time_out_real                         305.
% 2.81/1.00  --time_out_virtual                      -1.
% 2.81/1.00  --symbol_type_check                     false
% 2.81/1.00  --clausify_out                          false
% 2.81/1.00  --sig_cnt_out                           false
% 2.81/1.00  --trig_cnt_out                          false
% 2.81/1.00  --trig_cnt_out_tolerance                1.
% 2.81/1.00  --trig_cnt_out_sk_spl                   false
% 2.81/1.00  --abstr_cl_out                          false
% 2.81/1.00  
% 2.81/1.00  ------ Global Options
% 2.81/1.00  
% 2.81/1.00  --schedule                              default
% 2.81/1.00  --add_important_lit                     false
% 2.81/1.00  --prop_solver_per_cl                    1000
% 2.81/1.00  --min_unsat_core                        false
% 2.81/1.00  --soft_assumptions                      false
% 2.81/1.00  --soft_lemma_size                       3
% 2.81/1.00  --prop_impl_unit_size                   0
% 2.81/1.00  --prop_impl_unit                        []
% 2.81/1.00  --share_sel_clauses                     true
% 2.81/1.00  --reset_solvers                         false
% 2.81/1.00  --bc_imp_inh                            [conj_cone]
% 2.81/1.00  --conj_cone_tolerance                   3.
% 2.81/1.00  --extra_neg_conj                        none
% 2.81/1.00  --large_theory_mode                     true
% 2.81/1.00  --prolific_symb_bound                   200
% 2.81/1.00  --lt_threshold                          2000
% 2.81/1.00  --clause_weak_htbl                      true
% 2.81/1.00  --gc_record_bc_elim                     false
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing Options
% 2.81/1.00  
% 2.81/1.00  --preprocessing_flag                    true
% 2.81/1.00  --time_out_prep_mult                    0.1
% 2.81/1.00  --splitting_mode                        input
% 2.81/1.00  --splitting_grd                         true
% 2.81/1.00  --splitting_cvd                         false
% 2.81/1.00  --splitting_cvd_svl                     false
% 2.81/1.00  --splitting_nvd                         32
% 2.81/1.00  --sub_typing                            true
% 2.81/1.00  --prep_gs_sim                           true
% 2.81/1.00  --prep_unflatten                        true
% 2.81/1.00  --prep_res_sim                          true
% 2.81/1.00  --prep_upred                            true
% 2.81/1.00  --prep_sem_filter                       exhaustive
% 2.81/1.00  --prep_sem_filter_out                   false
% 2.81/1.00  --pred_elim                             true
% 2.81/1.00  --res_sim_input                         true
% 2.81/1.00  --eq_ax_congr_red                       true
% 2.81/1.00  --pure_diseq_elim                       true
% 2.81/1.00  --brand_transform                       false
% 2.81/1.00  --non_eq_to_eq                          false
% 2.81/1.00  --prep_def_merge                        true
% 2.81/1.00  --prep_def_merge_prop_impl              false
% 2.81/1.00  --prep_def_merge_mbd                    true
% 2.81/1.00  --prep_def_merge_tr_red                 false
% 2.81/1.00  --prep_def_merge_tr_cl                  false
% 2.81/1.00  --smt_preprocessing                     true
% 2.81/1.00  --smt_ac_axioms                         fast
% 2.81/1.00  --preprocessed_out                      false
% 2.81/1.00  --preprocessed_stats                    false
% 2.81/1.00  
% 2.81/1.00  ------ Abstraction refinement Options
% 2.81/1.00  
% 2.81/1.00  --abstr_ref                             []
% 2.81/1.00  --abstr_ref_prep                        false
% 2.81/1.00  --abstr_ref_until_sat                   false
% 2.81/1.00  --abstr_ref_sig_restrict                funpre
% 2.81/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.81/1.00  --abstr_ref_under                       []
% 2.81/1.00  
% 2.81/1.00  ------ SAT Options
% 2.81/1.00  
% 2.81/1.00  --sat_mode                              false
% 2.81/1.00  --sat_fm_restart_options                ""
% 2.81/1.00  --sat_gr_def                            false
% 2.81/1.00  --sat_epr_types                         true
% 2.81/1.00  --sat_non_cyclic_types                  false
% 2.81/1.00  --sat_finite_models                     false
% 2.81/1.00  --sat_fm_lemmas                         false
% 2.81/1.00  --sat_fm_prep                           false
% 2.81/1.00  --sat_fm_uc_incr                        true
% 2.81/1.00  --sat_out_model                         small
% 2.81/1.00  --sat_out_clauses                       false
% 2.81/1.00  
% 2.81/1.00  ------ QBF Options
% 2.81/1.00  
% 2.81/1.00  --qbf_mode                              false
% 2.81/1.00  --qbf_elim_univ                         false
% 2.81/1.00  --qbf_dom_inst                          none
% 2.81/1.00  --qbf_dom_pre_inst                      false
% 2.81/1.00  --qbf_sk_in                             false
% 2.81/1.00  --qbf_pred_elim                         true
% 2.81/1.00  --qbf_split                             512
% 2.81/1.00  
% 2.81/1.00  ------ BMC1 Options
% 2.81/1.00  
% 2.81/1.00  --bmc1_incremental                      false
% 2.81/1.00  --bmc1_axioms                           reachable_all
% 2.81/1.00  --bmc1_min_bound                        0
% 2.81/1.00  --bmc1_max_bound                        -1
% 2.81/1.00  --bmc1_max_bound_default                -1
% 2.81/1.00  --bmc1_symbol_reachability              true
% 2.81/1.00  --bmc1_property_lemmas                  false
% 2.81/1.00  --bmc1_k_induction                      false
% 2.81/1.00  --bmc1_non_equiv_states                 false
% 2.81/1.00  --bmc1_deadlock                         false
% 2.81/1.00  --bmc1_ucm                              false
% 2.81/1.00  --bmc1_add_unsat_core                   none
% 2.81/1.00  --bmc1_unsat_core_children              false
% 2.81/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.81/1.00  --bmc1_out_stat                         full
% 2.81/1.00  --bmc1_ground_init                      false
% 2.81/1.00  --bmc1_pre_inst_next_state              false
% 2.81/1.00  --bmc1_pre_inst_state                   false
% 2.81/1.00  --bmc1_pre_inst_reach_state             false
% 2.81/1.00  --bmc1_out_unsat_core                   false
% 2.81/1.00  --bmc1_aig_witness_out                  false
% 2.81/1.00  --bmc1_verbose                          false
% 2.81/1.00  --bmc1_dump_clauses_tptp                false
% 2.81/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.81/1.00  --bmc1_dump_file                        -
% 2.81/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.81/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.81/1.00  --bmc1_ucm_extend_mode                  1
% 2.81/1.00  --bmc1_ucm_init_mode                    2
% 2.81/1.00  --bmc1_ucm_cone_mode                    none
% 2.81/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.81/1.00  --bmc1_ucm_relax_model                  4
% 2.81/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.81/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.81/1.00  --bmc1_ucm_layered_model                none
% 2.81/1.00  --bmc1_ucm_max_lemma_size               10
% 2.81/1.00  
% 2.81/1.00  ------ AIG Options
% 2.81/1.00  
% 2.81/1.00  --aig_mode                              false
% 2.81/1.00  
% 2.81/1.00  ------ Instantiation Options
% 2.81/1.00  
% 2.81/1.00  --instantiation_flag                    true
% 2.81/1.00  --inst_sos_flag                         false
% 2.81/1.00  --inst_sos_phase                        true
% 2.81/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.81/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.81/1.00  --inst_lit_sel_side                     none
% 2.81/1.00  --inst_solver_per_active                1400
% 2.81/1.00  --inst_solver_calls_frac                1.
% 2.81/1.00  --inst_passive_queue_type               priority_queues
% 2.81/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.81/1.00  --inst_passive_queues_freq              [25;2]
% 2.81/1.00  --inst_dismatching                      true
% 2.81/1.00  --inst_eager_unprocessed_to_passive     true
% 2.81/1.00  --inst_prop_sim_given                   true
% 2.81/1.00  --inst_prop_sim_new                     false
% 2.81/1.00  --inst_subs_new                         false
% 2.81/1.00  --inst_eq_res_simp                      false
% 2.81/1.00  --inst_subs_given                       false
% 2.81/1.00  --inst_orphan_elimination               true
% 2.81/1.00  --inst_learning_loop_flag               true
% 2.81/1.00  --inst_learning_start                   3000
% 2.81/1.00  --inst_learning_factor                  2
% 2.81/1.00  --inst_start_prop_sim_after_learn       3
% 2.81/1.00  --inst_sel_renew                        solver
% 2.81/1.00  --inst_lit_activity_flag                true
% 2.81/1.00  --inst_restr_to_given                   false
% 2.81/1.00  --inst_activity_threshold               500
% 2.81/1.00  --inst_out_proof                        true
% 2.81/1.00  
% 2.81/1.00  ------ Resolution Options
% 2.81/1.00  
% 2.81/1.00  --resolution_flag                       false
% 2.81/1.00  --res_lit_sel                           adaptive
% 2.81/1.00  --res_lit_sel_side                      none
% 2.81/1.00  --res_ordering                          kbo
% 2.81/1.00  --res_to_prop_solver                    active
% 2.81/1.00  --res_prop_simpl_new                    false
% 2.81/1.00  --res_prop_simpl_given                  true
% 2.81/1.00  --res_passive_queue_type                priority_queues
% 2.81/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.81/1.00  --res_passive_queues_freq               [15;5]
% 2.81/1.00  --res_forward_subs                      full
% 2.81/1.00  --res_backward_subs                     full
% 2.81/1.00  --res_forward_subs_resolution           true
% 2.81/1.00  --res_backward_subs_resolution          true
% 2.81/1.00  --res_orphan_elimination                true
% 2.81/1.00  --res_time_limit                        2.
% 2.81/1.00  --res_out_proof                         true
% 2.81/1.00  
% 2.81/1.00  ------ Superposition Options
% 2.81/1.00  
% 2.81/1.00  --superposition_flag                    true
% 2.81/1.00  --sup_passive_queue_type                priority_queues
% 2.81/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.81/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.81/1.00  --demod_completeness_check              fast
% 2.81/1.00  --demod_use_ground                      true
% 2.81/1.00  --sup_to_prop_solver                    passive
% 2.81/1.00  --sup_prop_simpl_new                    true
% 2.81/1.00  --sup_prop_simpl_given                  true
% 2.81/1.00  --sup_fun_splitting                     false
% 2.81/1.00  --sup_smt_interval                      50000
% 2.81/1.00  
% 2.81/1.00  ------ Superposition Simplification Setup
% 2.81/1.00  
% 2.81/1.00  --sup_indices_passive                   []
% 2.81/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.81/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.81/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.00  --sup_full_bw                           [BwDemod]
% 2.81/1.00  --sup_immed_triv                        [TrivRules]
% 2.81/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.81/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.00  --sup_immed_bw_main                     []
% 2.81/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.81/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.81/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.81/1.00  
% 2.81/1.00  ------ Combination Options
% 2.81/1.00  
% 2.81/1.00  --comb_res_mult                         3
% 2.81/1.00  --comb_sup_mult                         2
% 2.81/1.00  --comb_inst_mult                        10
% 2.81/1.00  
% 2.81/1.00  ------ Debug Options
% 2.81/1.00  
% 2.81/1.00  --dbg_backtrace                         false
% 2.81/1.00  --dbg_dump_prop_clauses                 false
% 2.81/1.00  --dbg_dump_prop_clauses_file            -
% 2.81/1.00  --dbg_out_stat                          false
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  ------ Proving...
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  % SZS status Theorem for theBenchmark.p
% 2.81/1.00  
% 2.81/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.81/1.00  
% 2.81/1.00  fof(f19,conjecture,(
% 2.81/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f20,negated_conjecture,(
% 2.81/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.81/1.00    inference(negated_conjecture,[],[f19])).
% 2.81/1.00  
% 2.81/1.00  fof(f48,plain,(
% 2.81/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.81/1.00    inference(ennf_transformation,[],[f20])).
% 2.81/1.00  
% 2.81/1.00  fof(f49,plain,(
% 2.81/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.81/1.00    inference(flattening,[],[f48])).
% 2.81/1.00  
% 2.81/1.00  fof(f53,plain,(
% 2.81/1.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.81/1.00    introduced(choice_axiom,[])).
% 2.81/1.00  
% 2.81/1.00  fof(f52,plain,(
% 2.81/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.81/1.00    introduced(choice_axiom,[])).
% 2.81/1.00  
% 2.81/1.00  fof(f51,plain,(
% 2.81/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.81/1.00    introduced(choice_axiom,[])).
% 2.81/1.00  
% 2.81/1.00  fof(f54,plain,(
% 2.81/1.00    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.81/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53,f52,f51])).
% 2.81/1.00  
% 2.81/1.00  fof(f86,plain,(
% 2.81/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.81/1.00    inference(cnf_transformation,[],[f54])).
% 2.81/1.00  
% 2.81/1.00  fof(f16,axiom,(
% 2.81/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f43,plain,(
% 2.81/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.81/1.00    inference(ennf_transformation,[],[f16])).
% 2.81/1.00  
% 2.81/1.00  fof(f78,plain,(
% 2.81/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f43])).
% 2.81/1.00  
% 2.81/1.00  fof(f81,plain,(
% 2.81/1.00    l1_struct_0(sK0)),
% 2.81/1.00    inference(cnf_transformation,[],[f54])).
% 2.81/1.00  
% 2.81/1.00  fof(f83,plain,(
% 2.81/1.00    l1_struct_0(sK1)),
% 2.81/1.00    inference(cnf_transformation,[],[f54])).
% 2.81/1.00  
% 2.81/1.00  fof(f11,axiom,(
% 2.81/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f34,plain,(
% 2.81/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.81/1.00    inference(ennf_transformation,[],[f11])).
% 2.81/1.00  
% 2.81/1.00  fof(f69,plain,(
% 2.81/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.81/1.00    inference(cnf_transformation,[],[f34])).
% 2.81/1.00  
% 2.81/1.00  fof(f87,plain,(
% 2.81/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.81/1.00    inference(cnf_transformation,[],[f54])).
% 2.81/1.00  
% 2.81/1.00  fof(f14,axiom,(
% 2.81/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f39,plain,(
% 2.81/1.00    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.81/1.00    inference(ennf_transformation,[],[f14])).
% 2.81/1.00  
% 2.81/1.00  fof(f40,plain,(
% 2.81/1.00    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.81/1.00    inference(flattening,[],[f39])).
% 2.81/1.00  
% 2.81/1.00  fof(f73,plain,(
% 2.81/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f40])).
% 2.81/1.00  
% 2.81/1.00  fof(f12,axiom,(
% 2.81/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f35,plain,(
% 2.81/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.81/1.00    inference(ennf_transformation,[],[f12])).
% 2.81/1.00  
% 2.81/1.00  fof(f36,plain,(
% 2.81/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.81/1.00    inference(flattening,[],[f35])).
% 2.81/1.00  
% 2.81/1.00  fof(f50,plain,(
% 2.81/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.81/1.00    inference(nnf_transformation,[],[f36])).
% 2.81/1.00  
% 2.81/1.00  fof(f70,plain,(
% 2.81/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f50])).
% 2.81/1.00  
% 2.81/1.00  fof(f10,axiom,(
% 2.81/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f21,plain,(
% 2.81/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.81/1.00    inference(pure_predicate_removal,[],[f10])).
% 2.81/1.00  
% 2.81/1.00  fof(f33,plain,(
% 2.81/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.81/1.00    inference(ennf_transformation,[],[f21])).
% 2.81/1.00  
% 2.81/1.00  fof(f68,plain,(
% 2.81/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.81/1.00    inference(cnf_transformation,[],[f33])).
% 2.81/1.00  
% 2.81/1.00  fof(f3,axiom,(
% 2.81/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f57,plain,(
% 2.81/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.81/1.00    inference(cnf_transformation,[],[f3])).
% 2.81/1.00  
% 2.81/1.00  fof(f2,axiom,(
% 2.81/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f22,plain,(
% 2.81/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.81/1.00    inference(ennf_transformation,[],[f2])).
% 2.81/1.00  
% 2.81/1.00  fof(f56,plain,(
% 2.81/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f22])).
% 2.81/1.00  
% 2.81/1.00  fof(f84,plain,(
% 2.81/1.00    v1_funct_1(sK2)),
% 2.81/1.00    inference(cnf_transformation,[],[f54])).
% 2.81/1.00  
% 2.81/1.00  fof(f85,plain,(
% 2.81/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.81/1.00    inference(cnf_transformation,[],[f54])).
% 2.81/1.00  
% 2.81/1.00  fof(f1,axiom,(
% 2.81/1.00    v1_xboole_0(k1_xboole_0)),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f55,plain,(
% 2.81/1.00    v1_xboole_0(k1_xboole_0)),
% 2.81/1.00    inference(cnf_transformation,[],[f1])).
% 2.81/1.00  
% 2.81/1.00  fof(f17,axiom,(
% 2.81/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f44,plain,(
% 2.81/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.81/1.00    inference(ennf_transformation,[],[f17])).
% 2.81/1.00  
% 2.81/1.00  fof(f45,plain,(
% 2.81/1.00    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.81/1.00    inference(flattening,[],[f44])).
% 2.81/1.00  
% 2.81/1.00  fof(f79,plain,(
% 2.81/1.00    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f45])).
% 2.81/1.00  
% 2.81/1.00  fof(f82,plain,(
% 2.81/1.00    ~v2_struct_0(sK1)),
% 2.81/1.00    inference(cnf_transformation,[],[f54])).
% 2.81/1.00  
% 2.81/1.00  fof(f18,axiom,(
% 2.81/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f46,plain,(
% 2.81/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.81/1.00    inference(ennf_transformation,[],[f18])).
% 2.81/1.00  
% 2.81/1.00  fof(f47,plain,(
% 2.81/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.81/1.00    inference(flattening,[],[f46])).
% 2.81/1.00  
% 2.81/1.00  fof(f80,plain,(
% 2.81/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f47])).
% 2.81/1.00  
% 2.81/1.00  fof(f88,plain,(
% 2.81/1.00    v2_funct_1(sK2)),
% 2.81/1.00    inference(cnf_transformation,[],[f54])).
% 2.81/1.00  
% 2.81/1.00  fof(f13,axiom,(
% 2.81/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f37,plain,(
% 2.81/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.81/1.00    inference(ennf_transformation,[],[f13])).
% 2.81/1.00  
% 2.81/1.00  fof(f38,plain,(
% 2.81/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.81/1.00    inference(flattening,[],[f37])).
% 2.81/1.00  
% 2.81/1.00  fof(f72,plain,(
% 2.81/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f38])).
% 2.81/1.00  
% 2.81/1.00  fof(f89,plain,(
% 2.81/1.00    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.81/1.00    inference(cnf_transformation,[],[f54])).
% 2.81/1.00  
% 2.81/1.00  fof(f15,axiom,(
% 2.81/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f41,plain,(
% 2.81/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.81/1.00    inference(ennf_transformation,[],[f15])).
% 2.81/1.00  
% 2.81/1.00  fof(f42,plain,(
% 2.81/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.81/1.00    inference(flattening,[],[f41])).
% 2.81/1.00  
% 2.81/1.00  fof(f77,plain,(
% 2.81/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f7,axiom,(
% 2.81/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f27,plain,(
% 2.81/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.81/1.00    inference(ennf_transformation,[],[f7])).
% 2.81/1.00  
% 2.81/1.00  fof(f28,plain,(
% 2.81/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.81/1.00    inference(flattening,[],[f27])).
% 2.81/1.00  
% 2.81/1.00  fof(f64,plain,(
% 2.81/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f28])).
% 2.81/1.00  
% 2.81/1.00  fof(f9,axiom,(
% 2.81/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f31,plain,(
% 2.81/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.81/1.00    inference(ennf_transformation,[],[f9])).
% 2.81/1.00  
% 2.81/1.00  fof(f32,plain,(
% 2.81/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.81/1.00    inference(flattening,[],[f31])).
% 2.81/1.00  
% 2.81/1.00  fof(f67,plain,(
% 2.81/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f32])).
% 2.81/1.00  
% 2.81/1.00  fof(f4,axiom,(
% 2.81/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f23,plain,(
% 2.81/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.81/1.00    inference(ennf_transformation,[],[f4])).
% 2.81/1.00  
% 2.81/1.00  fof(f24,plain,(
% 2.81/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.81/1.00    inference(flattening,[],[f23])).
% 2.81/1.00  
% 2.81/1.00  fof(f59,plain,(
% 2.81/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f24])).
% 2.81/1.00  
% 2.81/1.00  fof(f76,plain,(
% 2.81/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f42])).
% 2.81/1.00  
% 2.81/1.00  fof(f63,plain,(
% 2.81/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f28])).
% 2.81/1.00  
% 2.81/1.00  fof(f5,axiom,(
% 2.81/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f25,plain,(
% 2.81/1.00    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.81/1.00    inference(ennf_transformation,[],[f5])).
% 2.81/1.00  
% 2.81/1.00  fof(f26,plain,(
% 2.81/1.00    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.81/1.00    inference(flattening,[],[f25])).
% 2.81/1.00  
% 2.81/1.00  fof(f61,plain,(
% 2.81/1.00    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f26])).
% 2.81/1.00  
% 2.81/1.00  fof(f58,plain,(
% 2.81/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f24])).
% 2.81/1.00  
% 2.81/1.00  fof(f8,axiom,(
% 2.81/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f29,plain,(
% 2.81/1.00    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.81/1.00    inference(ennf_transformation,[],[f8])).
% 2.81/1.00  
% 2.81/1.00  fof(f30,plain,(
% 2.81/1.00    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.81/1.00    inference(flattening,[],[f29])).
% 2.81/1.00  
% 2.81/1.00  fof(f65,plain,(
% 2.81/1.00    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.81/1.00    inference(cnf_transformation,[],[f30])).
% 2.81/1.00  
% 2.81/1.00  fof(f6,axiom,(
% 2.81/1.00    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.81/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.81/1.00  
% 2.81/1.00  fof(f62,plain,(
% 2.81/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.81/1.00    inference(cnf_transformation,[],[f6])).
% 2.81/1.00  
% 2.81/1.00  cnf(c_29,negated_conjecture,
% 2.81/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.81/1.00      inference(cnf_transformation,[],[f86]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_736,negated_conjecture,
% 2.81/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_29]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1263,plain,
% 2.81/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_736]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_23,plain,
% 2.81/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_34,negated_conjecture,
% 2.81/1.00      ( l1_struct_0(sK0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f81]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_413,plain,
% 2.81/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.81/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_414,plain,
% 2.81/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.81/1.00      inference(unflattening,[status(thm)],[c_413]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_731,plain,
% 2.81/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_414]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_32,negated_conjecture,
% 2.81/1.00      ( l1_struct_0(sK1) ),
% 2.81/1.00      inference(cnf_transformation,[],[f83]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_408,plain,
% 2.81/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.81/1.00      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_409,plain,
% 2.81/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.81/1.00      inference(unflattening,[status(thm)],[c_408]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_732,plain,
% 2.81/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_409]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1293,plain,
% 2.81/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.81/1.00      inference(light_normalisation,[status(thm)],[c_1263,c_731,c_732]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_14,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f69]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_743,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.81/1.00      | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1257,plain,
% 2.81/1.00      ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
% 2.81/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1844,plain,
% 2.81/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1293,c_1257]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_28,negated_conjecture,
% 2.81/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.81/1.00      inference(cnf_transformation,[],[f87]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_737,negated_conjecture,
% 2.81/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_28]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1290,plain,
% 2.81/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.81/1.00      inference(light_normalisation,[status(thm)],[c_737,c_731,c_732]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1846,plain,
% 2.81/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_1844,c_1290]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1882,plain,
% 2.81/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_1846,c_1293]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_19,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.81/1.00      | v1_partfun1(X0,X1)
% 2.81/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | k1_xboole_0 = X2 ),
% 2.81/1.00      inference(cnf_transformation,[],[f73]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_16,plain,
% 2.81/1.00      ( ~ v1_partfun1(X0,X1)
% 2.81/1.00      | ~ v4_relat_1(X0,X1)
% 2.81/1.00      | ~ v1_relat_1(X0)
% 2.81/1.00      | k1_relat_1(X0) = X1 ),
% 2.81/1.00      inference(cnf_transformation,[],[f70]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_494,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.81/1.00      | ~ v4_relat_1(X0,X1)
% 2.81/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | ~ v1_relat_1(X0)
% 2.81/1.00      | k1_relat_1(X0) = X1
% 2.81/1.00      | k1_xboole_0 = X2 ),
% 2.81/1.00      inference(resolution,[status(thm)],[c_19,c_16]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_13,plain,
% 2.81/1.00      ( v4_relat_1(X0,X1)
% 2.81/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.81/1.00      inference(cnf_transformation,[],[f68]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_498,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.81/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | ~ v1_relat_1(X0)
% 2.81/1.00      | k1_relat_1(X0) = X1
% 2.81/1.00      | k1_xboole_0 = X2 ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_494,c_13]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_729,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.81/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.81/1.00      | ~ v1_funct_1(X0_54)
% 2.81/1.00      | ~ v1_relat_1(X0_54)
% 2.81/1.00      | k1_relat_1(X0_54) = X0_55
% 2.81/1.00      | k1_xboole_0 = X1_55 ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_498]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1268,plain,
% 2.81/1.00      ( k1_relat_1(X0_54) = X0_55
% 2.81/1.00      | k1_xboole_0 = X1_55
% 2.81/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.81/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2,plain,
% 2.81/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f57]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_754,plain,
% 2.81/1.00      ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_797,plain,
% 2.81/1.00      ( v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_849,plain,
% 2.81/1.00      ( k1_relat_1(X0_54) = X0_55
% 2.81/1.00      | k1_xboole_0 = X1_55
% 2.81/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.81/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_729]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.81/1.00      | ~ v1_relat_1(X1)
% 2.81/1.00      | v1_relat_1(X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f56]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_755,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(X1_54))
% 2.81/1.00      | ~ v1_relat_1(X1_54)
% 2.81/1.00      | v1_relat_1(X0_54) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1544,plain,
% 2.81/1.00      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.81/1.00      | v1_relat_1(X0_54)
% 2.81/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_755]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1545,plain,
% 2.81/1.00      ( m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_54) = iProver_top
% 2.81/1.00      | v1_relat_1(k2_zfmisc_1(X0_55,X1_55)) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1544]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3845,plain,
% 2.81/1.00      ( v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.81/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.81/1.00      | k1_xboole_0 = X1_55
% 2.81/1.00      | k1_relat_1(X0_54) = X0_55 ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_1268,c_797,c_849,c_1545]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3846,plain,
% 2.81/1.00      ( k1_relat_1(X0_54) = X0_55
% 2.81/1.00      | k1_xboole_0 = X1_55
% 2.81/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.81/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(renaming,[status(thm)],[c_3845]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3854,plain,
% 2.81/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.81/1.00      | k2_relat_1(sK2) = k1_xboole_0
% 2.81/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1882,c_3846]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_31,negated_conjecture,
% 2.81/1.00      ( v1_funct_1(sK2) ),
% 2.81/1.00      inference(cnf_transformation,[],[f84]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_38,plain,
% 2.81/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_30,negated_conjecture,
% 2.81/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_735,negated_conjecture,
% 2.81/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_30]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1264,plain,
% 2.81/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_735]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1287,plain,
% 2.81/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.81/1.00      inference(light_normalisation,[status(thm)],[c_1264,c_731,c_732]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1883,plain,
% 2.81/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_1846,c_1287]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_0,plain,
% 2.81/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f55]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_24,plain,
% 2.81/1.00      ( v2_struct_0(X0)
% 2.81/1.00      | ~ l1_struct_0(X0)
% 2.81/1.00      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f79]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_381,plain,
% 2.81/1.00      ( v2_struct_0(X0)
% 2.81/1.00      | ~ l1_struct_0(X0)
% 2.81/1.00      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.81/1.00      inference(resolution_lifted,[status(thm)],[c_0,c_24]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_33,negated_conjecture,
% 2.81/1.00      ( ~ v2_struct_0(sK1) ),
% 2.81/1.00      inference(cnf_transformation,[],[f82]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_399,plain,
% 2.81/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.81/1.00      inference(resolution_lifted,[status(thm)],[c_381,c_33]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_400,plain,
% 2.81/1.00      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.81/1.00      inference(unflattening,[status(thm)],[c_399]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_383,plain,
% 2.81/1.00      ( v2_struct_0(sK1)
% 2.81/1.00      | ~ l1_struct_0(sK1)
% 2.81/1.00      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_381]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_402,plain,
% 2.81/1.00      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_400,c_33,c_32,c_383]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_733,plain,
% 2.81/1.00      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_402]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1279,plain,
% 2.81/1.00      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_732,c_733]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1884,plain,
% 2.81/1.00      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_1846,c_1279]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3958,plain,
% 2.81/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_3854,c_38,c_1883,c_1884]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1880,plain,
% 2.81/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_1846,c_1844]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_25,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.81/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | ~ v2_funct_1(X0)
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.81/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.81/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_739,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.81/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.81/1.00      | ~ v2_funct_1(X0_54)
% 2.81/1.00      | ~ v1_funct_1(X0_54)
% 2.81/1.00      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.81/1.00      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1261,plain,
% 2.81/1.00      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.81/1.00      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
% 2.81/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.81/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.81/1.00      | v2_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2785,plain,
% 2.81/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.81/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.81/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.81/1.00      | v2_funct_1(sK2) != iProver_top
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1880,c_1261]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_27,negated_conjecture,
% 2.81/1.00      ( v2_funct_1(sK2) ),
% 2.81/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_41,plain,
% 2.81/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3549,plain,
% 2.81/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_2785,c_38,c_41,c_1882,c_1883]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_17,plain,
% 2.81/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 2.81/1.00      | ~ v1_funct_2(X3,X0,X1)
% 2.81/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.81/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.81/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.81/1.00      | ~ v1_funct_1(X3)
% 2.81/1.00      | ~ v1_funct_1(X2) ),
% 2.81/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_26,negated_conjecture,
% 2.81/1.00      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.81/1.00      inference(cnf_transformation,[],[f89]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_420,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.81/1.00      | ~ v1_funct_2(X3,X1,X2)
% 2.81/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | ~ v1_funct_1(X3)
% 2.81/1.00      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X3
% 2.81/1.00      | u1_struct_0(sK1) != X2
% 2.81/1.00      | u1_struct_0(sK0) != X1
% 2.81/1.00      | sK2 != X3 ),
% 2.81/1.00      inference(resolution_lifted,[status(thm)],[c_17,c_26]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_421,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.81/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.81/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.81/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.81/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.81/1.00      inference(unflattening,[status(thm)],[c_420]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_730,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.81/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.81/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.81/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.81/1.00      | ~ v1_funct_1(X0_54)
% 2.81/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.81/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_421]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_757,plain,
% 2.81/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.81/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.81/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.81/1.00      | sP0_iProver_split
% 2.81/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.81/1.00      inference(splitting,
% 2.81/1.00                [splitting(split),new_symbols(definition,[])],
% 2.81/1.00                [c_730]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1266,plain,
% 2.81/1.00      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.81/1.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.81/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.81/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.81/1.00      | sP0_iProver_split = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1465,plain,
% 2.81/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.81/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.81/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.81/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.81/1.00      | sP0_iProver_split = iProver_top ),
% 2.81/1.00      inference(light_normalisation,[status(thm)],[c_1266,c_731,c_732]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_756,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.81/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.81/1.00      | ~ v1_funct_1(X0_54)
% 2.81/1.00      | ~ sP0_iProver_split ),
% 2.81/1.00      inference(splitting,
% 2.81/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.81/1.00                [c_730]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1267,plain,
% 2.81/1.00      ( v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.81/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | sP0_iProver_split != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1358,plain,
% 2.81/1.00      ( v1_funct_2(X0_54,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.81/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | sP0_iProver_split != iProver_top ),
% 2.81/1.00      inference(light_normalisation,[status(thm)],[c_1267,c_731,c_732]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1471,plain,
% 2.81/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.81/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.81/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.81/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.81/1.00      inference(forward_subsumption_resolution,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_1465,c_1358]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1881,plain,
% 2.81/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.81/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.81/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.81/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_1846,c_1471]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3552,plain,
% 2.81/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.81/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.81/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.81/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_3549,c_1881]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3961,plain,
% 2.81/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.81/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.81/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.81/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_3958,c_3552]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_20,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.81/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.81/1.00      | ~ v2_funct_1(X0)
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.81/1.00      inference(cnf_transformation,[],[f77]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_742,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.81/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.81/1.00      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
% 2.81/1.00      | ~ v2_funct_1(X0_54)
% 2.81/1.00      | ~ v1_funct_1(X0_54)
% 2.81/1.00      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1258,plain,
% 2.81/1.00      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.81/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.81/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.81/1.00      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
% 2.81/1.00      | v2_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3263,plain,
% 2.81/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.81/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 2.81/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.81/1.00      | v2_funct_1(sK2) != iProver_top
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1880,c_1258]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3555,plain,
% 2.81/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_3263,c_38,c_41,c_1882,c_1883]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3561,plain,
% 2.81/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_3555,c_1257]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_738,negated_conjecture,
% 2.81/1.00      ( v2_funct_1(sK2) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_27]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1262,plain,
% 2.81/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_8,plain,
% 2.81/1.00      ( ~ v2_funct_1(X0)
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | ~ v1_relat_1(X0)
% 2.81/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_748,plain,
% 2.81/1.00      ( ~ v2_funct_1(X0_54)
% 2.81/1.00      | ~ v1_funct_1(X0_54)
% 2.81/1.00      | ~ v1_relat_1(X0_54)
% 2.81/1.00      | k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_8]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1252,plain,
% 2.81/1.00      ( k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54)
% 2.81/1.00      | v2_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1990,plain,
% 2.81/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top
% 2.81/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1262,c_1252]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_812,plain,
% 2.81/1.00      ( ~ v2_funct_1(sK2)
% 2.81/1.00      | ~ v1_funct_1(sK2)
% 2.81/1.00      | ~ v1_relat_1(sK2)
% 2.81/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_748]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1635,plain,
% 2.81/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.81/1.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.81/1.00      | v1_relat_1(sK2) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_1544]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1722,plain,
% 2.81/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_754]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2218,plain,
% 2.81/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_1990,c_31,c_29,c_27,c_812,c_1635,c_1722]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3568,plain,
% 2.81/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.81/1.00      inference(light_normalisation,[status(thm)],[c_3561,c_2218]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3684,plain,
% 2.81/1.00      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.81/1.00      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.81/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.81/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.81/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.81/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_3568,c_1261]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_12,plain,
% 2.81/1.00      ( ~ v2_funct_1(X0)
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | ~ v1_relat_1(X0)
% 2.81/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.81/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_744,plain,
% 2.81/1.00      ( ~ v2_funct_1(X0_54)
% 2.81/1.00      | ~ v1_funct_1(X0_54)
% 2.81/1.00      | ~ v1_relat_1(X0_54)
% 2.81/1.00      | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_12]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1256,plain,
% 2.81/1.00      ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
% 2.81/1.00      | v2_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1967,plain,
% 2.81/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top
% 2.81/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1262,c_1256]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_824,plain,
% 2.81/1.00      ( ~ v2_funct_1(sK2)
% 2.81/1.00      | ~ v1_funct_1(sK2)
% 2.81/1.00      | ~ v1_relat_1(sK2)
% 2.81/1.00      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_744]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2212,plain,
% 2.81/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_1967,c_31,c_29,c_27,c_824,c_1635,c_1722]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3699,plain,
% 2.81/1.00      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.81/1.00      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.81/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.81/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.81/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.81/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.81/1.00      inference(light_normalisation,[status(thm)],[c_3684,c_2212]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_40,plain,
% 2.81/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3,plain,
% 2.81/1.00      ( ~ v1_funct_1(X0)
% 2.81/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.81/1.00      | ~ v1_relat_1(X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f59]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_753,plain,
% 2.81/1.00      ( ~ v1_funct_1(X0_54)
% 2.81/1.00      | v1_funct_1(k2_funct_1(X0_54))
% 2.81/1.00      | ~ v1_relat_1(X0_54) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_800,plain,
% 2.81/1.00      ( v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_funct_1(k2_funct_1(X0_54)) = iProver_top
% 2.81/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_802,plain,
% 2.81/1.00      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top
% 2.81/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_800]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1636,plain,
% 2.81/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.81/1.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.81/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1635]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1723,plain,
% 2.81/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_1722]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_21,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.81/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.81/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.81/1.00      | ~ v2_funct_1(X0)
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.81/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_741,plain,
% 2.81/1.00      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 2.81/1.00      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
% 2.81/1.00      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 2.81/1.00      | ~ v2_funct_1(X0_54)
% 2.81/1.00      | ~ v1_funct_1(X0_54)
% 2.81/1.00      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_21]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1259,plain,
% 2.81/1.00      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 2.81/1.00      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 2.81/1.00      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
% 2.81/1.00      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 2.81/1.00      | v2_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2689,plain,
% 2.81/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 2.81/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.81/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.81/1.00      | v2_funct_1(sK2) != iProver_top
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1880,c_1259]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_9,plain,
% 2.81/1.00      ( ~ v2_funct_1(X0)
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | ~ v1_relat_1(X0)
% 2.81/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.81/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_747,plain,
% 2.81/1.00      ( ~ v2_funct_1(X0_54)
% 2.81/1.00      | ~ v1_funct_1(X0_54)
% 2.81/1.00      | ~ v1_relat_1(X0_54)
% 2.81/1.00      | k1_relat_1(k2_funct_1(X0_54)) = k2_relat_1(X0_54) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1253,plain,
% 2.81/1.00      ( k1_relat_1(k2_funct_1(X0_54)) = k2_relat_1(X0_54)
% 2.81/1.00      | v2_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2126,plain,
% 2.81/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top
% 2.81/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1262,c_1253]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_815,plain,
% 2.81/1.00      ( ~ v2_funct_1(sK2)
% 2.81/1.00      | ~ v1_funct_1(sK2)
% 2.81/1.00      | ~ v1_relat_1(sK2)
% 2.81/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_747]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2297,plain,
% 2.81/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_2126,c_31,c_29,c_27,c_815,c_1635,c_1722]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_5,plain,
% 2.81/1.00      ( v2_funct_1(X0)
% 2.81/1.00      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | ~ v1_funct_1(X1)
% 2.81/1.00      | ~ v1_relat_1(X0)
% 2.81/1.00      | ~ v1_relat_1(X1)
% 2.81/1.00      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 2.81/1.00      inference(cnf_transformation,[],[f61]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_751,plain,
% 2.81/1.00      ( v2_funct_1(X0_54)
% 2.81/1.00      | ~ v2_funct_1(k5_relat_1(X1_54,X0_54))
% 2.81/1.00      | ~ v1_funct_1(X0_54)
% 2.81/1.00      | ~ v1_funct_1(X1_54)
% 2.81/1.00      | ~ v1_relat_1(X0_54)
% 2.81/1.00      | ~ v1_relat_1(X1_54)
% 2.81/1.00      | k1_relat_1(X0_54) != k2_relat_1(X1_54) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1249,plain,
% 2.81/1.00      ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
% 2.81/1.00      | v2_funct_1(X0_54) = iProver_top
% 2.81/1.00      | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
% 2.81/1.00      | v1_funct_1(X1_54) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_54) != iProver_top
% 2.81/1.00      | v1_relat_1(X1_54) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2300,plain,
% 2.81/1.00      ( k2_relat_1(X0_54) != k2_relat_1(sK2)
% 2.81/1.00      | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
% 2.81/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_54) != iProver_top
% 2.81/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_2297,c_1249]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_4,plain,
% 2.81/1.00      ( ~ v1_funct_1(X0)
% 2.81/1.00      | ~ v1_relat_1(X0)
% 2.81/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f58]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_752,plain,
% 2.81/1.00      ( ~ v1_funct_1(X0_54)
% 2.81/1.00      | ~ v1_relat_1(X0_54)
% 2.81/1.00      | v1_relat_1(k2_funct_1(X0_54)) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_803,plain,
% 2.81/1.00      ( v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_54) != iProver_top
% 2.81/1.00      | v1_relat_1(k2_funct_1(X0_54)) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_805,plain,
% 2.81/1.00      ( v1_funct_1(sK2) != iProver_top
% 2.81/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.81/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_803]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2956,plain,
% 2.81/1.00      ( v1_relat_1(X0_54) != iProver_top
% 2.81/1.00      | k2_relat_1(X0_54) != k2_relat_1(sK2)
% 2.81/1.00      | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
% 2.81/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_2300,c_38,c_40,c_802,c_805,c_1636,c_1723]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2957,plain,
% 2.81/1.00      ( k2_relat_1(X0_54) != k2_relat_1(sK2)
% 2.81/1.00      | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
% 2.81/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(renaming,[status(thm)],[c_2956]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2968,plain,
% 2.81/1.00      ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
% 2.81/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top
% 2.81/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.81/1.00      inference(equality_resolution,[status(thm)],[c_2957]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_11,plain,
% 2.81/1.00      ( ~ v2_funct_1(X0)
% 2.81/1.00      | ~ v1_funct_1(X0)
% 2.81/1.00      | ~ v1_relat_1(X0)
% 2.81/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f65]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_745,plain,
% 2.81/1.00      ( ~ v2_funct_1(X0_54)
% 2.81/1.00      | ~ v1_funct_1(X0_54)
% 2.81/1.00      | ~ v1_relat_1(X0_54)
% 2.81/1.00      | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_relat_1(k1_relat_1(X0_54)) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1255,plain,
% 2.81/1.00      ( k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_relat_1(k1_relat_1(X0_54))
% 2.81/1.00      | v2_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_funct_1(X0_54) != iProver_top
% 2.81/1.00      | v1_relat_1(X0_54) != iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2598,plain,
% 2.81/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top
% 2.81/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.81/1.00      inference(superposition,[status(thm)],[c_1262,c_1255]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_821,plain,
% 2.81/1.00      ( ~ v2_funct_1(sK2)
% 2.81/1.00      | ~ v1_funct_1(sK2)
% 2.81/1.00      | ~ v1_relat_1(sK2)
% 2.81/1.00      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 2.81/1.00      inference(instantiation,[status(thm)],[c_745]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2788,plain,
% 2.81/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_2598,c_31,c_29,c_27,c_821,c_1635,c_1722]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2973,plain,
% 2.81/1.00      ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
% 2.81/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top
% 2.81/1.00      | v1_relat_1(sK2) != iProver_top ),
% 2.81/1.00      inference(light_normalisation,[status(thm)],[c_2968,c_2788]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2980,plain,
% 2.81/1.00      ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
% 2.81/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_2973,c_38,c_40,c_1636,c_1723]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_7,plain,
% 2.81/1.00      ( v2_funct_1(k6_relat_1(X0)) ),
% 2.81/1.00      inference(cnf_transformation,[],[f62]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_749,plain,
% 2.81/1.00      ( v2_funct_1(k6_relat_1(X0_55)) ),
% 2.81/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_1251,plain,
% 2.81/1.00      ( v2_funct_1(k6_relat_1(X0_55)) = iProver_top ),
% 2.81/1.00      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_2986,plain,
% 2.81/1.00      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.81/1.00      inference(forward_subsumption_resolution,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_2980,c_1251]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3715,plain,
% 2.81/1.00      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.81/1.00      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.81/1.00      inference(global_propositional_subsumption,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_3699,c_38,c_40,c_41,c_802,c_1636,c_1723,c_1882,c_1883,
% 2.81/1.00                 c_2689,c_2986,c_3263]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3962,plain,
% 2.81/1.00      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 2.81/1.00      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_3958,c_3715]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3987,plain,
% 2.81/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.81/1.00      inference(equality_resolution_simp,[status(thm)],[c_3962]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3990,plain,
% 2.81/1.00      ( sK2 != sK2
% 2.81/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.81/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.81/1.00      inference(light_normalisation,[status(thm)],[c_3961,c_3987]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3991,plain,
% 2.81/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.81/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.81/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.81/1.00      inference(equality_resolution_simp,[status(thm)],[c_3990]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3967,plain,
% 2.81/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_3958,c_1882]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3969,plain,
% 2.81/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.81/1.00      inference(demodulation,[status(thm)],[c_3958,c_1883]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(c_3995,plain,
% 2.81/1.00      ( v1_funct_1(sK2) != iProver_top ),
% 2.81/1.00      inference(forward_subsumption_resolution,
% 2.81/1.00                [status(thm)],
% 2.81/1.00                [c_3991,c_3967,c_3969]) ).
% 2.81/1.00  
% 2.81/1.00  cnf(contradiction,plain,
% 2.81/1.00      ( $false ),
% 2.81/1.00      inference(minisat,[status(thm)],[c_3995,c_38]) ).
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.81/1.00  
% 2.81/1.00  ------                               Statistics
% 2.81/1.00  
% 2.81/1.00  ------ General
% 2.81/1.00  
% 2.81/1.00  abstr_ref_over_cycles:                  0
% 2.81/1.00  abstr_ref_under_cycles:                 0
% 2.81/1.00  gc_basic_clause_elim:                   0
% 2.81/1.00  forced_gc_time:                         0
% 2.81/1.00  parsing_time:                           0.009
% 2.81/1.00  unif_index_cands_time:                  0.
% 2.81/1.00  unif_index_add_time:                    0.
% 2.81/1.00  orderings_time:                         0.
% 2.81/1.00  out_proof_time:                         0.017
% 2.81/1.00  total_time:                             0.182
% 2.81/1.00  num_of_symbols:                         62
% 2.81/1.00  num_of_terms:                           3785
% 2.81/1.00  
% 2.81/1.00  ------ Preprocessing
% 2.81/1.00  
% 2.81/1.00  num_of_splits:                          1
% 2.81/1.00  num_of_split_atoms:                     1
% 2.81/1.00  num_of_reused_defs:                     0
% 2.81/1.00  num_eq_ax_congr_red:                    4
% 2.81/1.00  num_of_sem_filtered_clauses:            2
% 2.81/1.00  num_of_subtypes:                        4
% 2.81/1.00  monotx_restored_types:                  1
% 2.81/1.00  sat_num_of_epr_types:                   0
% 2.81/1.00  sat_num_of_non_cyclic_types:            0
% 2.81/1.00  sat_guarded_non_collapsed_types:        1
% 2.81/1.00  num_pure_diseq_elim:                    0
% 2.81/1.00  simp_replaced_by:                       0
% 2.81/1.00  res_preprocessed:                       159
% 2.81/1.00  prep_upred:                             0
% 2.81/1.00  prep_unflattend:                        12
% 2.81/1.00  smt_new_axioms:                         0
% 2.81/1.00  pred_elim_cands:                        5
% 2.81/1.00  pred_elim:                              6
% 2.81/1.00  pred_elim_cl:                           7
% 2.81/1.00  pred_elim_cycles:                       9
% 2.81/1.00  merged_defs:                            0
% 2.81/1.00  merged_defs_ncl:                        0
% 2.81/1.00  bin_hyper_res:                          0
% 2.81/1.00  prep_cycles:                            4
% 2.81/1.00  pred_elim_time:                         0.005
% 2.81/1.00  splitting_time:                         0.
% 2.81/1.00  sem_filter_time:                        0.
% 2.81/1.00  monotx_time:                            0.013
% 2.81/1.00  subtype_inf_time:                       0.015
% 2.81/1.00  
% 2.81/1.00  ------ Problem properties
% 2.81/1.00  
% 2.81/1.00  clauses:                                29
% 2.81/1.00  conjectures:                            5
% 2.81/1.00  epr:                                    2
% 2.81/1.00  horn:                                   28
% 2.81/1.00  ground:                                 9
% 2.81/1.00  unary:                                  10
% 2.81/1.00  binary:                                 1
% 2.81/1.00  lits:                                   99
% 2.81/1.00  lits_eq:                                21
% 2.81/1.00  fd_pure:                                0
% 2.81/1.00  fd_pseudo:                              0
% 2.81/1.00  fd_cond:                                0
% 2.81/1.00  fd_pseudo_cond:                         1
% 2.81/1.00  ac_symbols:                             0
% 2.81/1.00  
% 2.81/1.00  ------ Propositional Solver
% 2.81/1.00  
% 2.81/1.00  prop_solver_calls:                      29
% 2.81/1.00  prop_fast_solver_calls:                 1307
% 2.81/1.00  smt_solver_calls:                       0
% 2.81/1.00  smt_fast_solver_calls:                  0
% 2.81/1.00  prop_num_of_clauses:                    1390
% 2.81/1.00  prop_preprocess_simplified:             5356
% 2.81/1.00  prop_fo_subsumed:                       61
% 2.81/1.00  prop_solver_time:                       0.
% 2.81/1.00  smt_solver_time:                        0.
% 2.81/1.00  smt_fast_solver_time:                   0.
% 2.81/1.00  prop_fast_solver_time:                  0.
% 2.81/1.00  prop_unsat_core_time:                   0.
% 2.81/1.00  
% 2.81/1.00  ------ QBF
% 2.81/1.00  
% 2.81/1.00  qbf_q_res:                              0
% 2.81/1.00  qbf_num_tautologies:                    0
% 2.81/1.00  qbf_prep_cycles:                        0
% 2.81/1.00  
% 2.81/1.00  ------ BMC1
% 2.81/1.00  
% 2.81/1.00  bmc1_current_bound:                     -1
% 2.81/1.00  bmc1_last_solved_bound:                 -1
% 2.81/1.00  bmc1_unsat_core_size:                   -1
% 2.81/1.00  bmc1_unsat_core_parents_size:           -1
% 2.81/1.00  bmc1_merge_next_fun:                    0
% 2.81/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.81/1.00  
% 2.81/1.00  ------ Instantiation
% 2.81/1.00  
% 2.81/1.00  inst_num_of_clauses:                    465
% 2.81/1.00  inst_num_in_passive:                    135
% 2.81/1.00  inst_num_in_active:                     258
% 2.81/1.00  inst_num_in_unprocessed:                72
% 2.81/1.00  inst_num_of_loops:                      310
% 2.81/1.00  inst_num_of_learning_restarts:          0
% 2.81/1.00  inst_num_moves_active_passive:          47
% 2.81/1.00  inst_lit_activity:                      0
% 2.81/1.00  inst_lit_activity_moves:                0
% 2.81/1.00  inst_num_tautologies:                   0
% 2.81/1.00  inst_num_prop_implied:                  0
% 2.81/1.00  inst_num_existing_simplified:           0
% 2.81/1.00  inst_num_eq_res_simplified:             0
% 2.81/1.00  inst_num_child_elim:                    0
% 2.81/1.00  inst_num_of_dismatching_blockings:      103
% 2.81/1.00  inst_num_of_non_proper_insts:           445
% 2.81/1.00  inst_num_of_duplicates:                 0
% 2.81/1.00  inst_inst_num_from_inst_to_res:         0
% 2.81/1.00  inst_dismatching_checking_time:         0.
% 2.81/1.00  
% 2.81/1.00  ------ Resolution
% 2.81/1.00  
% 2.81/1.00  res_num_of_clauses:                     0
% 2.81/1.00  res_num_in_passive:                     0
% 2.81/1.00  res_num_in_active:                      0
% 2.81/1.00  res_num_of_loops:                       163
% 2.81/1.00  res_forward_subset_subsumed:            46
% 2.81/1.00  res_backward_subset_subsumed:           0
% 2.81/1.00  res_forward_subsumed:                   0
% 2.81/1.00  res_backward_subsumed:                  0
% 2.81/1.00  res_forward_subsumption_resolution:     1
% 2.81/1.00  res_backward_subsumption_resolution:    0
% 2.81/1.00  res_clause_to_clause_subsumption:       88
% 2.81/1.00  res_orphan_elimination:                 0
% 2.81/1.00  res_tautology_del:                      42
% 2.81/1.00  res_num_eq_res_simplified:              0
% 2.81/1.00  res_num_sel_changes:                    0
% 2.81/1.00  res_moves_from_active_to_pass:          0
% 2.81/1.00  
% 2.81/1.00  ------ Superposition
% 2.81/1.00  
% 2.81/1.00  sup_time_total:                         0.
% 2.81/1.00  sup_time_generating:                    0.
% 2.81/1.00  sup_time_sim_full:                      0.
% 2.81/1.00  sup_time_sim_immed:                     0.
% 2.81/1.00  
% 2.81/1.00  sup_num_of_clauses:                     54
% 2.81/1.00  sup_num_in_active:                      43
% 2.81/1.00  sup_num_in_passive:                     11
% 2.81/1.00  sup_num_of_loops:                       61
% 2.81/1.00  sup_fw_superposition:                   23
% 2.81/1.00  sup_bw_superposition:                   17
% 2.81/1.00  sup_immediate_simplified:               18
% 2.81/1.00  sup_given_eliminated:                   0
% 2.81/1.00  comparisons_done:                       0
% 2.81/1.00  comparisons_avoided:                    0
% 2.81/1.00  
% 2.81/1.00  ------ Simplifications
% 2.81/1.00  
% 2.81/1.00  
% 2.81/1.00  sim_fw_subset_subsumed:                 6
% 2.81/1.00  sim_bw_subset_subsumed:                 0
% 2.81/1.00  sim_fw_subsumed:                        3
% 2.81/1.00  sim_bw_subsumed:                        0
% 2.81/1.00  sim_fw_subsumption_res:                 4
% 2.81/1.00  sim_bw_subsumption_res:                 0
% 2.81/1.00  sim_tautology_del:                      0
% 2.81/1.00  sim_eq_tautology_del:                   5
% 2.81/1.00  sim_eq_res_simp:                        2
% 2.81/1.00  sim_fw_demodulated:                     0
% 2.81/1.00  sim_bw_demodulated:                     19
% 2.81/1.00  sim_light_normalised:                   17
% 2.81/1.00  sim_joinable_taut:                      0
% 2.81/1.00  sim_joinable_simp:                      0
% 2.81/1.00  sim_ac_normalised:                      0
% 2.81/1.00  sim_smt_subsumption:                    0
% 2.81/1.00  
%------------------------------------------------------------------------------
