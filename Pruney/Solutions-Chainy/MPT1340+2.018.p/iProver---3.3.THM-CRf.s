%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:24 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :  251 (10671 expanded)
%              Number of clauses        :  165 (3394 expanded)
%              Number of leaves         :   24 (2991 expanded)
%              Depth                    :   26
%              Number of atoms          :  937 (66300 expanded)
%              Number of equality atoms :  412 (11911 expanded)
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

fof(f87,plain,(
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

fof(f79,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f82,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f54])).

fof(f84,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f88,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f54])).

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
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

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

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f85,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f86,plain,(
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

fof(f80,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
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

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f89,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f71,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f90,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f54])).

fof(f14,axiom,(
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

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f27,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f64,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f62,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f24])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f57,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f91,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f59,f70])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_739,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1264,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_739])).

cnf(c_23,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_34,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_421,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_34])).

cnf(c_422,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_733,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_422])).

cnf(c_32,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_416,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_32])).

cnf(c_417,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_416])).

cnf(c_734,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_417])).

cnf(c_1295,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1264,c_733,c_734])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_747,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1257,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_747])).

cnf(c_1838,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1295,c_1257])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_740,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_28])).

cnf(c_1292,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_740,c_733,c_734])).

cnf(c_1840,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1838,c_1292])).

cnf(c_1895,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1840,c_1295])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_11,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_14,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f68])).

cnf(c_463,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_11,c_14])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_467,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_463,c_14,c_11,c_10])).

cnf(c_468,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_467])).

cnf(c_507,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_17,c_468])).

cnf(c_511,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_507,c_17,c_10,c_463])).

cnf(c_512,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_511])).

cnf(c_731,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v1_funct_1(X0_54)
    | k1_relat_1(X0_54) = X0_55
    | k1_xboole_0 = X1_55 ),
    inference(subtyping,[status(esa)],[c_512])).

cnf(c_1270,plain,
    ( k1_relat_1(X0_54) = X0_55
    | k1_xboole_0 = X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_731])).

cnf(c_4001,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1895,c_1270])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_38,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_738,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_30])).

cnf(c_1265,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_738])).

cnf(c_1289,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1265,c_733,c_734])).

cnf(c_1896,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1840,c_1289])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_24,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_389,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_24])).

cnf(c_33,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_407,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_389,c_33])).

cnf(c_408,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_391,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_389])).

cnf(c_410,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_408,c_33,c_32,c_391])).

cnf(c_735,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_410])).

cnf(c_1283,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_734,c_735])).

cnf(c_1897,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1840,c_1283])).

cnf(c_4211,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4001,c_38,c_1896,c_1897])).

cnf(c_1893,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1840,c_1838])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_742,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1262,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_2757,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_1262])).

cnf(c_27,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_41,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3186,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2757,c_38,c_41,c_1895,c_1896])).

cnf(c_15,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_26,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_428,plain,
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
    inference(resolution_lifted,[status(thm)],[c_15,c_26])).

cnf(c_429,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_428])).

cnf(c_732,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_429])).

cnf(c_759,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_732])).

cnf(c_1268,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_1469,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1268,c_733,c_734])).

cnf(c_758,plain,
    ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_54)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_732])).

cnf(c_1269,plain,
    ( v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_758])).

cnf(c_1348,plain,
    ( v1_funct_2(X0_54,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1269,c_733,c_734])).

cnf(c_1475,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1469,c_1348])).

cnf(c_1894,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1840,c_1475])).

cnf(c_3189,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3186,c_1894])).

cnf(c_4214,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4211,c_3189])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_746,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1258,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_2647,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_1258])).

cnf(c_3444,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2647,c_38,c_41,c_1895,c_1896])).

cnf(c_3450,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_3444,c_1257])).

cnf(c_741,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1263,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_751,plain,
    ( ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1253,plain,
    ( k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54)
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_2019,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1253])).

cnf(c_813,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_748,plain,
    ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | v1_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1538,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_748])).

cnf(c_2233,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2019,c_31,c_29,c_27,c_813,c_1538])).

cnf(c_3455,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_3450,c_2233])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_744,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k1_xboole_0 = X1_55
    | k5_relat_1(k2_funct_1(X0_54),X0_54) = k6_partfun1(X1_55) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1260,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k1_xboole_0 = X1_55
    | k5_relat_1(k2_funct_1(X0_54),X0_54) = k6_partfun1(X1_55)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_744])).

cnf(c_3496,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0
    | k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3455,c_1260])).

cnf(c_9,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_749,plain,
    ( ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1255,plain,
    ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_1996,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1255])).

cnf(c_819,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_2227,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1996,c_31,c_29,c_27,c_819,c_1538])).

cnf(c_3534,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_xboole_0
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3496,c_2227])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_743,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k1_xboole_0 = X1_55
    | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_partfun1(X0_55) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1261,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | k1_xboole_0 = X1_55
    | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_partfun1(X0_55)
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_2859,plain,
    ( k2_relat_1(sK2) = k1_xboole_0
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_1261])).

cnf(c_3683,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3534,c_38,c_41,c_1895,c_1896,c_1897,c_2859])).

cnf(c_8,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_750,plain,
    ( ~ v2_funct_1(X0_54)
    | ~ v1_relat_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k1_relat_1(k2_funct_1(X0_54)) = k2_relat_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1254,plain,
    ( k1_relat_1(k2_funct_1(X0_54)) = k2_relat_1(X0_54)
    | v2_funct_1(X0_54) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_2139,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1263,c_1254])).

cnf(c_816,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_750])).

cnf(c_2320,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2139,c_31,c_29,c_27,c_816,c_1538])).

cnf(c_5,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_753,plain,
    ( v2_funct_1(X0_54)
    | ~ v2_funct_1(k5_relat_1(X1_54,X0_54))
    | ~ v1_relat_1(X0_54)
    | ~ v1_relat_1(X1_54)
    | ~ v1_funct_1(X0_54)
    | ~ v1_funct_1(X1_54)
    | k1_relat_1(X0_54) != k2_relat_1(X1_54) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1251,plain,
    ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
    | v2_funct_1(X0_54) = iProver_top
    | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(X1_54) != iProver_top
    | v1_funct_1(X1_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_753])).

cnf(c_2324,plain,
    ( k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2320,c_1251])).

cnf(c_40,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_757,plain,
    ( ~ v1_relat_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | v1_funct_1(k2_funct_1(X0_54)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_798,plain,
    ( v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top
    | v1_funct_1(k2_funct_1(X0_54)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_800,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_798])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_756,plain,
    ( ~ v1_relat_1(X0_54)
    | v1_relat_1(k2_funct_1(X0_54))
    | ~ v1_funct_1(X0_54) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_801,plain,
    ( v1_relat_1(X0_54) != iProver_top
    | v1_relat_1(k2_funct_1(X0_54)) = iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_756])).

cnf(c_803,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_801])).

cnf(c_1539,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1538])).

cnf(c_2961,plain,
    ( v1_funct_1(X0_54) != iProver_top
    | k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2324,c_38,c_40,c_800,c_803,c_1539])).

cnf(c_2962,plain,
    ( k2_relat_1(X0_54) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(renaming,[status(thm)],[c_2961])).

cnf(c_2973,plain,
    ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_2962])).

cnf(c_771,plain,
    ( k2_relat_1(X0_54) = k2_relat_1(X1_54)
    | X0_54 != X1_54 ),
    theory(equality)).

cnf(c_784,plain,
    ( k2_relat_1(sK2) = k2_relat_1(sK2)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_771])).

cnf(c_761,plain,
    ( X0_54 = X0_54 ),
    theory(equality)).

cnf(c_794,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_2964,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2962])).

cnf(c_3116,plain,
    ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2973,c_38,c_40,c_784,c_794,c_1539,c_2964])).

cnf(c_3686,plain,
    ( v2_funct_1(k6_partfun1(k2_struct_0(sK0))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3683,c_3116])).

cnf(c_3,plain,
    ( v2_funct_1(k6_partfun1(X0)) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_755,plain,
    ( v2_funct_1(k6_partfun1(X0_55)) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1249,plain,
    ( v2_funct_1(k6_partfun1(X0_55)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_3852,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3686,c_1249])).

cnf(c_3497,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3455,c_1262])).

cnf(c_3520,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3497,c_2227])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_745,plain,
    ( ~ v1_funct_2(X0_54,X0_55,X1_55)
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
    | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
    | ~ v2_funct_1(X0_54)
    | ~ v1_funct_1(X0_54)
    | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1259,plain,
    ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
    | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
    | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
    | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
    | v2_funct_1(X0_54) != iProver_top
    | v1_funct_1(X0_54) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_745])).

cnf(c_2656,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1893,c_1259])).

cnf(c_3561,plain,
    ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3520,c_38,c_40,c_41,c_800,c_1539,c_1895,c_1896,c_2647,c_2656])).

cnf(c_3562,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3561])).

cnf(c_4216,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4211,c_3562])).

cnf(c_4241,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4216])).

cnf(c_4651,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4214,c_3852,c_4241])).

cnf(c_4217,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4211,c_3455])).

cnf(c_4458,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4217,c_1262])).

cnf(c_4478,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4458,c_2227])).

cnf(c_4533,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4478,c_3852,c_4241])).

cnf(c_4655,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4651,c_4533])).

cnf(c_737,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_31])).

cnf(c_1266,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_4221,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4211,c_1895])).

cnf(c_4223,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4211,c_1896])).

cnf(c_4659,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4655,c_1266,c_4221,c_4223])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 20:20:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.01/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.02  
% 3.01/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.01/1.02  
% 3.01/1.02  ------  iProver source info
% 3.01/1.02  
% 3.01/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.01/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.01/1.02  git: non_committed_changes: false
% 3.01/1.02  git: last_make_outside_of_git: false
% 3.01/1.02  
% 3.01/1.02  ------ 
% 3.01/1.02  
% 3.01/1.02  ------ Input Options
% 3.01/1.02  
% 3.01/1.02  --out_options                           all
% 3.01/1.02  --tptp_safe_out                         true
% 3.01/1.02  --problem_path                          ""
% 3.01/1.02  --include_path                          ""
% 3.01/1.02  --clausifier                            res/vclausify_rel
% 3.01/1.02  --clausifier_options                    --mode clausify
% 3.01/1.02  --stdin                                 false
% 3.01/1.02  --stats_out                             all
% 3.01/1.02  
% 3.01/1.02  ------ General Options
% 3.01/1.02  
% 3.01/1.02  --fof                                   false
% 3.01/1.02  --time_out_real                         305.
% 3.01/1.02  --time_out_virtual                      -1.
% 3.01/1.02  --symbol_type_check                     false
% 3.01/1.02  --clausify_out                          false
% 3.01/1.02  --sig_cnt_out                           false
% 3.01/1.02  --trig_cnt_out                          false
% 3.01/1.02  --trig_cnt_out_tolerance                1.
% 3.01/1.02  --trig_cnt_out_sk_spl                   false
% 3.01/1.02  --abstr_cl_out                          false
% 3.01/1.02  
% 3.01/1.02  ------ Global Options
% 3.01/1.02  
% 3.01/1.02  --schedule                              default
% 3.01/1.02  --add_important_lit                     false
% 3.01/1.02  --prop_solver_per_cl                    1000
% 3.01/1.02  --min_unsat_core                        false
% 3.01/1.02  --soft_assumptions                      false
% 3.01/1.02  --soft_lemma_size                       3
% 3.01/1.02  --prop_impl_unit_size                   0
% 3.01/1.02  --prop_impl_unit                        []
% 3.01/1.02  --share_sel_clauses                     true
% 3.01/1.02  --reset_solvers                         false
% 3.01/1.02  --bc_imp_inh                            [conj_cone]
% 3.01/1.02  --conj_cone_tolerance                   3.
% 3.01/1.02  --extra_neg_conj                        none
% 3.01/1.02  --large_theory_mode                     true
% 3.01/1.02  --prolific_symb_bound                   200
% 3.01/1.02  --lt_threshold                          2000
% 3.01/1.02  --clause_weak_htbl                      true
% 3.01/1.02  --gc_record_bc_elim                     false
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing Options
% 3.01/1.02  
% 3.01/1.02  --preprocessing_flag                    true
% 3.01/1.02  --time_out_prep_mult                    0.1
% 3.01/1.02  --splitting_mode                        input
% 3.01/1.02  --splitting_grd                         true
% 3.01/1.02  --splitting_cvd                         false
% 3.01/1.02  --splitting_cvd_svl                     false
% 3.01/1.02  --splitting_nvd                         32
% 3.01/1.02  --sub_typing                            true
% 3.01/1.02  --prep_gs_sim                           true
% 3.01/1.02  --prep_unflatten                        true
% 3.01/1.02  --prep_res_sim                          true
% 3.01/1.02  --prep_upred                            true
% 3.01/1.02  --prep_sem_filter                       exhaustive
% 3.01/1.02  --prep_sem_filter_out                   false
% 3.01/1.02  --pred_elim                             true
% 3.01/1.02  --res_sim_input                         true
% 3.01/1.02  --eq_ax_congr_red                       true
% 3.01/1.02  --pure_diseq_elim                       true
% 3.01/1.02  --brand_transform                       false
% 3.01/1.02  --non_eq_to_eq                          false
% 3.01/1.02  --prep_def_merge                        true
% 3.01/1.02  --prep_def_merge_prop_impl              false
% 3.01/1.02  --prep_def_merge_mbd                    true
% 3.01/1.02  --prep_def_merge_tr_red                 false
% 3.01/1.02  --prep_def_merge_tr_cl                  false
% 3.01/1.02  --smt_preprocessing                     true
% 3.01/1.02  --smt_ac_axioms                         fast
% 3.01/1.02  --preprocessed_out                      false
% 3.01/1.02  --preprocessed_stats                    false
% 3.01/1.02  
% 3.01/1.02  ------ Abstraction refinement Options
% 3.01/1.02  
% 3.01/1.02  --abstr_ref                             []
% 3.01/1.02  --abstr_ref_prep                        false
% 3.01/1.02  --abstr_ref_until_sat                   false
% 3.01/1.02  --abstr_ref_sig_restrict                funpre
% 3.01/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.02  --abstr_ref_under                       []
% 3.01/1.02  
% 3.01/1.02  ------ SAT Options
% 3.01/1.02  
% 3.01/1.02  --sat_mode                              false
% 3.01/1.02  --sat_fm_restart_options                ""
% 3.01/1.02  --sat_gr_def                            false
% 3.01/1.02  --sat_epr_types                         true
% 3.01/1.02  --sat_non_cyclic_types                  false
% 3.01/1.02  --sat_finite_models                     false
% 3.01/1.02  --sat_fm_lemmas                         false
% 3.01/1.02  --sat_fm_prep                           false
% 3.01/1.02  --sat_fm_uc_incr                        true
% 3.01/1.02  --sat_out_model                         small
% 3.01/1.02  --sat_out_clauses                       false
% 3.01/1.02  
% 3.01/1.02  ------ QBF Options
% 3.01/1.02  
% 3.01/1.02  --qbf_mode                              false
% 3.01/1.02  --qbf_elim_univ                         false
% 3.01/1.02  --qbf_dom_inst                          none
% 3.01/1.02  --qbf_dom_pre_inst                      false
% 3.01/1.02  --qbf_sk_in                             false
% 3.01/1.02  --qbf_pred_elim                         true
% 3.01/1.02  --qbf_split                             512
% 3.01/1.02  
% 3.01/1.02  ------ BMC1 Options
% 3.01/1.02  
% 3.01/1.02  --bmc1_incremental                      false
% 3.01/1.02  --bmc1_axioms                           reachable_all
% 3.01/1.02  --bmc1_min_bound                        0
% 3.01/1.02  --bmc1_max_bound                        -1
% 3.01/1.02  --bmc1_max_bound_default                -1
% 3.01/1.02  --bmc1_symbol_reachability              true
% 3.01/1.02  --bmc1_property_lemmas                  false
% 3.01/1.02  --bmc1_k_induction                      false
% 3.01/1.02  --bmc1_non_equiv_states                 false
% 3.01/1.02  --bmc1_deadlock                         false
% 3.01/1.02  --bmc1_ucm                              false
% 3.01/1.02  --bmc1_add_unsat_core                   none
% 3.01/1.02  --bmc1_unsat_core_children              false
% 3.01/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.02  --bmc1_out_stat                         full
% 3.01/1.02  --bmc1_ground_init                      false
% 3.01/1.02  --bmc1_pre_inst_next_state              false
% 3.01/1.02  --bmc1_pre_inst_state                   false
% 3.01/1.02  --bmc1_pre_inst_reach_state             false
% 3.01/1.02  --bmc1_out_unsat_core                   false
% 3.01/1.02  --bmc1_aig_witness_out                  false
% 3.01/1.02  --bmc1_verbose                          false
% 3.01/1.02  --bmc1_dump_clauses_tptp                false
% 3.01/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.02  --bmc1_dump_file                        -
% 3.01/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.02  --bmc1_ucm_extend_mode                  1
% 3.01/1.02  --bmc1_ucm_init_mode                    2
% 3.01/1.02  --bmc1_ucm_cone_mode                    none
% 3.01/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.02  --bmc1_ucm_relax_model                  4
% 3.01/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.02  --bmc1_ucm_layered_model                none
% 3.01/1.02  --bmc1_ucm_max_lemma_size               10
% 3.01/1.02  
% 3.01/1.02  ------ AIG Options
% 3.01/1.02  
% 3.01/1.02  --aig_mode                              false
% 3.01/1.02  
% 3.01/1.02  ------ Instantiation Options
% 3.01/1.02  
% 3.01/1.02  --instantiation_flag                    true
% 3.01/1.02  --inst_sos_flag                         false
% 3.01/1.02  --inst_sos_phase                        true
% 3.01/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.02  --inst_lit_sel_side                     num_symb
% 3.01/1.02  --inst_solver_per_active                1400
% 3.01/1.02  --inst_solver_calls_frac                1.
% 3.01/1.02  --inst_passive_queue_type               priority_queues
% 3.01/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.02  --inst_passive_queues_freq              [25;2]
% 3.01/1.02  --inst_dismatching                      true
% 3.01/1.02  --inst_eager_unprocessed_to_passive     true
% 3.01/1.02  --inst_prop_sim_given                   true
% 3.01/1.02  --inst_prop_sim_new                     false
% 3.01/1.02  --inst_subs_new                         false
% 3.01/1.02  --inst_eq_res_simp                      false
% 3.01/1.02  --inst_subs_given                       false
% 3.01/1.02  --inst_orphan_elimination               true
% 3.01/1.02  --inst_learning_loop_flag               true
% 3.01/1.02  --inst_learning_start                   3000
% 3.01/1.02  --inst_learning_factor                  2
% 3.01/1.02  --inst_start_prop_sim_after_learn       3
% 3.01/1.02  --inst_sel_renew                        solver
% 3.01/1.02  --inst_lit_activity_flag                true
% 3.01/1.02  --inst_restr_to_given                   false
% 3.01/1.02  --inst_activity_threshold               500
% 3.01/1.02  --inst_out_proof                        true
% 3.01/1.02  
% 3.01/1.02  ------ Resolution Options
% 3.01/1.02  
% 3.01/1.02  --resolution_flag                       true
% 3.01/1.02  --res_lit_sel                           adaptive
% 3.01/1.02  --res_lit_sel_side                      none
% 3.01/1.02  --res_ordering                          kbo
% 3.01/1.02  --res_to_prop_solver                    active
% 3.01/1.02  --res_prop_simpl_new                    false
% 3.01/1.02  --res_prop_simpl_given                  true
% 3.01/1.02  --res_passive_queue_type                priority_queues
% 3.01/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.02  --res_passive_queues_freq               [15;5]
% 3.01/1.02  --res_forward_subs                      full
% 3.01/1.02  --res_backward_subs                     full
% 3.01/1.02  --res_forward_subs_resolution           true
% 3.01/1.02  --res_backward_subs_resolution          true
% 3.01/1.02  --res_orphan_elimination                true
% 3.01/1.02  --res_time_limit                        2.
% 3.01/1.02  --res_out_proof                         true
% 3.01/1.02  
% 3.01/1.02  ------ Superposition Options
% 3.01/1.02  
% 3.01/1.02  --superposition_flag                    true
% 3.01/1.02  --sup_passive_queue_type                priority_queues
% 3.01/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.02  --demod_completeness_check              fast
% 3.01/1.02  --demod_use_ground                      true
% 3.01/1.02  --sup_to_prop_solver                    passive
% 3.01/1.02  --sup_prop_simpl_new                    true
% 3.01/1.02  --sup_prop_simpl_given                  true
% 3.01/1.02  --sup_fun_splitting                     false
% 3.01/1.02  --sup_smt_interval                      50000
% 3.01/1.02  
% 3.01/1.02  ------ Superposition Simplification Setup
% 3.01/1.02  
% 3.01/1.02  --sup_indices_passive                   []
% 3.01/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.02  --sup_full_bw                           [BwDemod]
% 3.01/1.02  --sup_immed_triv                        [TrivRules]
% 3.01/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.02  --sup_immed_bw_main                     []
% 3.01/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.02  
% 3.01/1.02  ------ Combination Options
% 3.01/1.02  
% 3.01/1.02  --comb_res_mult                         3
% 3.01/1.02  --comb_sup_mult                         2
% 3.01/1.02  --comb_inst_mult                        10
% 3.01/1.02  
% 3.01/1.02  ------ Debug Options
% 3.01/1.02  
% 3.01/1.02  --dbg_backtrace                         false
% 3.01/1.02  --dbg_dump_prop_clauses                 false
% 3.01/1.02  --dbg_dump_prop_clauses_file            -
% 3.01/1.02  --dbg_out_stat                          false
% 3.01/1.02  ------ Parsing...
% 3.01/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.01/1.02  ------ Proving...
% 3.01/1.02  ------ Problem Properties 
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  clauses                                 29
% 3.01/1.02  conjectures                             5
% 3.01/1.02  EPR                                     2
% 3.01/1.02  Horn                                    26
% 3.01/1.02  unary                                   10
% 3.01/1.02  binary                                  2
% 3.01/1.02  lits                                    100
% 3.01/1.02  lits eq                                 24
% 3.01/1.02  fd_pure                                 0
% 3.01/1.02  fd_pseudo                               0
% 3.01/1.02  fd_cond                                 2
% 3.01/1.02  fd_pseudo_cond                          1
% 3.01/1.02  AC symbols                              0
% 3.01/1.02  
% 3.01/1.02  ------ Schedule dynamic 5 is on 
% 3.01/1.02  
% 3.01/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  ------ 
% 3.01/1.02  Current options:
% 3.01/1.02  ------ 
% 3.01/1.02  
% 3.01/1.02  ------ Input Options
% 3.01/1.02  
% 3.01/1.02  --out_options                           all
% 3.01/1.02  --tptp_safe_out                         true
% 3.01/1.02  --problem_path                          ""
% 3.01/1.02  --include_path                          ""
% 3.01/1.02  --clausifier                            res/vclausify_rel
% 3.01/1.02  --clausifier_options                    --mode clausify
% 3.01/1.02  --stdin                                 false
% 3.01/1.02  --stats_out                             all
% 3.01/1.02  
% 3.01/1.02  ------ General Options
% 3.01/1.02  
% 3.01/1.02  --fof                                   false
% 3.01/1.02  --time_out_real                         305.
% 3.01/1.02  --time_out_virtual                      -1.
% 3.01/1.02  --symbol_type_check                     false
% 3.01/1.02  --clausify_out                          false
% 3.01/1.02  --sig_cnt_out                           false
% 3.01/1.02  --trig_cnt_out                          false
% 3.01/1.02  --trig_cnt_out_tolerance                1.
% 3.01/1.02  --trig_cnt_out_sk_spl                   false
% 3.01/1.02  --abstr_cl_out                          false
% 3.01/1.02  
% 3.01/1.02  ------ Global Options
% 3.01/1.02  
% 3.01/1.02  --schedule                              default
% 3.01/1.02  --add_important_lit                     false
% 3.01/1.02  --prop_solver_per_cl                    1000
% 3.01/1.02  --min_unsat_core                        false
% 3.01/1.02  --soft_assumptions                      false
% 3.01/1.02  --soft_lemma_size                       3
% 3.01/1.02  --prop_impl_unit_size                   0
% 3.01/1.02  --prop_impl_unit                        []
% 3.01/1.02  --share_sel_clauses                     true
% 3.01/1.02  --reset_solvers                         false
% 3.01/1.02  --bc_imp_inh                            [conj_cone]
% 3.01/1.02  --conj_cone_tolerance                   3.
% 3.01/1.02  --extra_neg_conj                        none
% 3.01/1.02  --large_theory_mode                     true
% 3.01/1.02  --prolific_symb_bound                   200
% 3.01/1.02  --lt_threshold                          2000
% 3.01/1.02  --clause_weak_htbl                      true
% 3.01/1.02  --gc_record_bc_elim                     false
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing Options
% 3.01/1.02  
% 3.01/1.02  --preprocessing_flag                    true
% 3.01/1.02  --time_out_prep_mult                    0.1
% 3.01/1.02  --splitting_mode                        input
% 3.01/1.02  --splitting_grd                         true
% 3.01/1.02  --splitting_cvd                         false
% 3.01/1.02  --splitting_cvd_svl                     false
% 3.01/1.02  --splitting_nvd                         32
% 3.01/1.02  --sub_typing                            true
% 3.01/1.02  --prep_gs_sim                           true
% 3.01/1.02  --prep_unflatten                        true
% 3.01/1.02  --prep_res_sim                          true
% 3.01/1.02  --prep_upred                            true
% 3.01/1.02  --prep_sem_filter                       exhaustive
% 3.01/1.02  --prep_sem_filter_out                   false
% 3.01/1.02  --pred_elim                             true
% 3.01/1.02  --res_sim_input                         true
% 3.01/1.02  --eq_ax_congr_red                       true
% 3.01/1.02  --pure_diseq_elim                       true
% 3.01/1.02  --brand_transform                       false
% 3.01/1.02  --non_eq_to_eq                          false
% 3.01/1.02  --prep_def_merge                        true
% 3.01/1.02  --prep_def_merge_prop_impl              false
% 3.01/1.02  --prep_def_merge_mbd                    true
% 3.01/1.02  --prep_def_merge_tr_red                 false
% 3.01/1.02  --prep_def_merge_tr_cl                  false
% 3.01/1.02  --smt_preprocessing                     true
% 3.01/1.02  --smt_ac_axioms                         fast
% 3.01/1.02  --preprocessed_out                      false
% 3.01/1.02  --preprocessed_stats                    false
% 3.01/1.02  
% 3.01/1.02  ------ Abstraction refinement Options
% 3.01/1.02  
% 3.01/1.02  --abstr_ref                             []
% 3.01/1.02  --abstr_ref_prep                        false
% 3.01/1.02  --abstr_ref_until_sat                   false
% 3.01/1.02  --abstr_ref_sig_restrict                funpre
% 3.01/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.01/1.02  --abstr_ref_under                       []
% 3.01/1.02  
% 3.01/1.02  ------ SAT Options
% 3.01/1.02  
% 3.01/1.02  --sat_mode                              false
% 3.01/1.02  --sat_fm_restart_options                ""
% 3.01/1.02  --sat_gr_def                            false
% 3.01/1.02  --sat_epr_types                         true
% 3.01/1.02  --sat_non_cyclic_types                  false
% 3.01/1.02  --sat_finite_models                     false
% 3.01/1.02  --sat_fm_lemmas                         false
% 3.01/1.02  --sat_fm_prep                           false
% 3.01/1.02  --sat_fm_uc_incr                        true
% 3.01/1.02  --sat_out_model                         small
% 3.01/1.02  --sat_out_clauses                       false
% 3.01/1.02  
% 3.01/1.02  ------ QBF Options
% 3.01/1.02  
% 3.01/1.02  --qbf_mode                              false
% 3.01/1.02  --qbf_elim_univ                         false
% 3.01/1.02  --qbf_dom_inst                          none
% 3.01/1.02  --qbf_dom_pre_inst                      false
% 3.01/1.02  --qbf_sk_in                             false
% 3.01/1.02  --qbf_pred_elim                         true
% 3.01/1.02  --qbf_split                             512
% 3.01/1.02  
% 3.01/1.02  ------ BMC1 Options
% 3.01/1.02  
% 3.01/1.02  --bmc1_incremental                      false
% 3.01/1.02  --bmc1_axioms                           reachable_all
% 3.01/1.02  --bmc1_min_bound                        0
% 3.01/1.02  --bmc1_max_bound                        -1
% 3.01/1.02  --bmc1_max_bound_default                -1
% 3.01/1.02  --bmc1_symbol_reachability              true
% 3.01/1.02  --bmc1_property_lemmas                  false
% 3.01/1.02  --bmc1_k_induction                      false
% 3.01/1.02  --bmc1_non_equiv_states                 false
% 3.01/1.02  --bmc1_deadlock                         false
% 3.01/1.02  --bmc1_ucm                              false
% 3.01/1.02  --bmc1_add_unsat_core                   none
% 3.01/1.02  --bmc1_unsat_core_children              false
% 3.01/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.01/1.02  --bmc1_out_stat                         full
% 3.01/1.02  --bmc1_ground_init                      false
% 3.01/1.02  --bmc1_pre_inst_next_state              false
% 3.01/1.02  --bmc1_pre_inst_state                   false
% 3.01/1.02  --bmc1_pre_inst_reach_state             false
% 3.01/1.02  --bmc1_out_unsat_core                   false
% 3.01/1.02  --bmc1_aig_witness_out                  false
% 3.01/1.02  --bmc1_verbose                          false
% 3.01/1.02  --bmc1_dump_clauses_tptp                false
% 3.01/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.01/1.02  --bmc1_dump_file                        -
% 3.01/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.01/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.01/1.02  --bmc1_ucm_extend_mode                  1
% 3.01/1.02  --bmc1_ucm_init_mode                    2
% 3.01/1.02  --bmc1_ucm_cone_mode                    none
% 3.01/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.01/1.02  --bmc1_ucm_relax_model                  4
% 3.01/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.01/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.01/1.02  --bmc1_ucm_layered_model                none
% 3.01/1.02  --bmc1_ucm_max_lemma_size               10
% 3.01/1.02  
% 3.01/1.02  ------ AIG Options
% 3.01/1.02  
% 3.01/1.02  --aig_mode                              false
% 3.01/1.02  
% 3.01/1.02  ------ Instantiation Options
% 3.01/1.02  
% 3.01/1.02  --instantiation_flag                    true
% 3.01/1.02  --inst_sos_flag                         false
% 3.01/1.02  --inst_sos_phase                        true
% 3.01/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.01/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.01/1.02  --inst_lit_sel_side                     none
% 3.01/1.02  --inst_solver_per_active                1400
% 3.01/1.02  --inst_solver_calls_frac                1.
% 3.01/1.02  --inst_passive_queue_type               priority_queues
% 3.01/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.01/1.02  --inst_passive_queues_freq              [25;2]
% 3.01/1.02  --inst_dismatching                      true
% 3.01/1.02  --inst_eager_unprocessed_to_passive     true
% 3.01/1.02  --inst_prop_sim_given                   true
% 3.01/1.02  --inst_prop_sim_new                     false
% 3.01/1.02  --inst_subs_new                         false
% 3.01/1.02  --inst_eq_res_simp                      false
% 3.01/1.02  --inst_subs_given                       false
% 3.01/1.02  --inst_orphan_elimination               true
% 3.01/1.02  --inst_learning_loop_flag               true
% 3.01/1.02  --inst_learning_start                   3000
% 3.01/1.02  --inst_learning_factor                  2
% 3.01/1.02  --inst_start_prop_sim_after_learn       3
% 3.01/1.02  --inst_sel_renew                        solver
% 3.01/1.02  --inst_lit_activity_flag                true
% 3.01/1.02  --inst_restr_to_given                   false
% 3.01/1.02  --inst_activity_threshold               500
% 3.01/1.02  --inst_out_proof                        true
% 3.01/1.02  
% 3.01/1.02  ------ Resolution Options
% 3.01/1.02  
% 3.01/1.02  --resolution_flag                       false
% 3.01/1.02  --res_lit_sel                           adaptive
% 3.01/1.02  --res_lit_sel_side                      none
% 3.01/1.02  --res_ordering                          kbo
% 3.01/1.02  --res_to_prop_solver                    active
% 3.01/1.02  --res_prop_simpl_new                    false
% 3.01/1.02  --res_prop_simpl_given                  true
% 3.01/1.02  --res_passive_queue_type                priority_queues
% 3.01/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.01/1.02  --res_passive_queues_freq               [15;5]
% 3.01/1.02  --res_forward_subs                      full
% 3.01/1.02  --res_backward_subs                     full
% 3.01/1.02  --res_forward_subs_resolution           true
% 3.01/1.02  --res_backward_subs_resolution          true
% 3.01/1.02  --res_orphan_elimination                true
% 3.01/1.02  --res_time_limit                        2.
% 3.01/1.02  --res_out_proof                         true
% 3.01/1.02  
% 3.01/1.02  ------ Superposition Options
% 3.01/1.02  
% 3.01/1.02  --superposition_flag                    true
% 3.01/1.02  --sup_passive_queue_type                priority_queues
% 3.01/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.01/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.01/1.02  --demod_completeness_check              fast
% 3.01/1.02  --demod_use_ground                      true
% 3.01/1.02  --sup_to_prop_solver                    passive
% 3.01/1.02  --sup_prop_simpl_new                    true
% 3.01/1.02  --sup_prop_simpl_given                  true
% 3.01/1.02  --sup_fun_splitting                     false
% 3.01/1.02  --sup_smt_interval                      50000
% 3.01/1.02  
% 3.01/1.02  ------ Superposition Simplification Setup
% 3.01/1.02  
% 3.01/1.02  --sup_indices_passive                   []
% 3.01/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.01/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.01/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.02  --sup_full_bw                           [BwDemod]
% 3.01/1.02  --sup_immed_triv                        [TrivRules]
% 3.01/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.01/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.02  --sup_immed_bw_main                     []
% 3.01/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.01/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.01/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.01/1.02  
% 3.01/1.02  ------ Combination Options
% 3.01/1.02  
% 3.01/1.02  --comb_res_mult                         3
% 3.01/1.02  --comb_sup_mult                         2
% 3.01/1.02  --comb_inst_mult                        10
% 3.01/1.02  
% 3.01/1.02  ------ Debug Options
% 3.01/1.02  
% 3.01/1.02  --dbg_backtrace                         false
% 3.01/1.02  --dbg_dump_prop_clauses                 false
% 3.01/1.02  --dbg_dump_prop_clauses_file            -
% 3.01/1.02  --dbg_out_stat                          false
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  ------ Proving...
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  % SZS status Theorem for theBenchmark.p
% 3.01/1.02  
% 3.01/1.02   Resolution empty clause
% 3.01/1.02  
% 3.01/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.01/1.02  
% 3.01/1.02  fof(f19,conjecture,(
% 3.01/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f20,negated_conjecture,(
% 3.01/1.02    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.01/1.02    inference(negated_conjecture,[],[f19])).
% 3.01/1.02  
% 3.01/1.02  fof(f48,plain,(
% 3.01/1.02    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.01/1.02    inference(ennf_transformation,[],[f20])).
% 3.01/1.02  
% 3.01/1.02  fof(f49,plain,(
% 3.01/1.02    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.01/1.02    inference(flattening,[],[f48])).
% 3.01/1.02  
% 3.01/1.02  fof(f53,plain,(
% 3.01/1.02    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.01/1.02    introduced(choice_axiom,[])).
% 3.01/1.02  
% 3.01/1.02  fof(f52,plain,(
% 3.01/1.02    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.01/1.02    introduced(choice_axiom,[])).
% 3.01/1.02  
% 3.01/1.02  fof(f51,plain,(
% 3.01/1.02    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.01/1.02    introduced(choice_axiom,[])).
% 3.01/1.02  
% 3.01/1.02  fof(f54,plain,(
% 3.01/1.02    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.01/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f49,f53,f52,f51])).
% 3.01/1.02  
% 3.01/1.02  fof(f87,plain,(
% 3.01/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.01/1.02    inference(cnf_transformation,[],[f54])).
% 3.01/1.02  
% 3.01/1.02  fof(f16,axiom,(
% 3.01/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f43,plain,(
% 3.01/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.01/1.02    inference(ennf_transformation,[],[f16])).
% 3.01/1.02  
% 3.01/1.02  fof(f79,plain,(
% 3.01/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f43])).
% 3.01/1.02  
% 3.01/1.02  fof(f82,plain,(
% 3.01/1.02    l1_struct_0(sK0)),
% 3.01/1.02    inference(cnf_transformation,[],[f54])).
% 3.01/1.02  
% 3.01/1.02  fof(f84,plain,(
% 3.01/1.02    l1_struct_0(sK1)),
% 3.01/1.02    inference(cnf_transformation,[],[f54])).
% 3.01/1.02  
% 3.01/1.02  fof(f9,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f32,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(ennf_transformation,[],[f9])).
% 3.01/1.02  
% 3.01/1.02  fof(f67,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f32])).
% 3.01/1.02  
% 3.01/1.02  fof(f88,plain,(
% 3.01/1.02    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.01/1.02    inference(cnf_transformation,[],[f54])).
% 3.01/1.02  
% 3.01/1.02  fof(f13,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f37,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 3.01/1.02    inference(ennf_transformation,[],[f13])).
% 3.01/1.02  
% 3.01/1.02  fof(f38,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 3.01/1.02    inference(flattening,[],[f37])).
% 3.01/1.02  
% 3.01/1.02  fof(f72,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f38])).
% 3.01/1.02  
% 3.01/1.02  fof(f8,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f21,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.01/1.02    inference(pure_predicate_removal,[],[f8])).
% 3.01/1.02  
% 3.01/1.02  fof(f31,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(ennf_transformation,[],[f21])).
% 3.01/1.02  
% 3.01/1.02  fof(f66,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f31])).
% 3.01/1.02  
% 3.01/1.02  fof(f10,axiom,(
% 3.01/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f33,plain,(
% 3.01/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.01/1.02    inference(ennf_transformation,[],[f10])).
% 3.01/1.02  
% 3.01/1.02  fof(f34,plain,(
% 3.01/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.01/1.02    inference(flattening,[],[f33])).
% 3.01/1.02  
% 3.01/1.02  fof(f50,plain,(
% 3.01/1.02    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.01/1.02    inference(nnf_transformation,[],[f34])).
% 3.01/1.02  
% 3.01/1.02  fof(f68,plain,(
% 3.01/1.02    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f50])).
% 3.01/1.02  
% 3.01/1.02  fof(f7,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f30,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.01/1.02    inference(ennf_transformation,[],[f7])).
% 3.01/1.02  
% 3.01/1.02  fof(f65,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f30])).
% 3.01/1.02  
% 3.01/1.02  fof(f85,plain,(
% 3.01/1.02    v1_funct_1(sK2)),
% 3.01/1.02    inference(cnf_transformation,[],[f54])).
% 3.01/1.02  
% 3.01/1.02  fof(f86,plain,(
% 3.01/1.02    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.01/1.02    inference(cnf_transformation,[],[f54])).
% 3.01/1.02  
% 3.01/1.02  fof(f1,axiom,(
% 3.01/1.02    v1_xboole_0(k1_xboole_0)),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f55,plain,(
% 3.01/1.02    v1_xboole_0(k1_xboole_0)),
% 3.01/1.02    inference(cnf_transformation,[],[f1])).
% 3.01/1.02  
% 3.01/1.02  fof(f17,axiom,(
% 3.01/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f44,plain,(
% 3.01/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.01/1.02    inference(ennf_transformation,[],[f17])).
% 3.01/1.02  
% 3.01/1.02  fof(f45,plain,(
% 3.01/1.02    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.01/1.02    inference(flattening,[],[f44])).
% 3.01/1.02  
% 3.01/1.02  fof(f80,plain,(
% 3.01/1.02    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f45])).
% 3.01/1.02  
% 3.01/1.02  fof(f83,plain,(
% 3.01/1.02    ~v2_struct_0(sK1)),
% 3.01/1.02    inference(cnf_transformation,[],[f54])).
% 3.01/1.02  
% 3.01/1.02  fof(f18,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f46,plain,(
% 3.01/1.02    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.01/1.02    inference(ennf_transformation,[],[f18])).
% 3.01/1.02  
% 3.01/1.02  fof(f47,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.01/1.02    inference(flattening,[],[f46])).
% 3.01/1.02  
% 3.01/1.02  fof(f81,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f47])).
% 3.01/1.02  
% 3.01/1.02  fof(f89,plain,(
% 3.01/1.02    v2_funct_1(sK2)),
% 3.01/1.02    inference(cnf_transformation,[],[f54])).
% 3.01/1.02  
% 3.01/1.02  fof(f12,axiom,(
% 3.01/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f35,plain,(
% 3.01/1.02    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.01/1.02    inference(ennf_transformation,[],[f12])).
% 3.01/1.02  
% 3.01/1.02  fof(f36,plain,(
% 3.01/1.02    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.01/1.02    inference(flattening,[],[f35])).
% 3.01/1.02  
% 3.01/1.02  fof(f71,plain,(
% 3.01/1.02    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f36])).
% 3.01/1.02  
% 3.01/1.02  fof(f90,plain,(
% 3.01/1.02    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.01/1.02    inference(cnf_transformation,[],[f54])).
% 3.01/1.02  
% 3.01/1.02  fof(f14,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f39,plain,(
% 3.01/1.02    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.01/1.02    inference(ennf_transformation,[],[f14])).
% 3.01/1.02  
% 3.01/1.02  fof(f40,plain,(
% 3.01/1.02    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.01/1.02    inference(flattening,[],[f39])).
% 3.01/1.02  
% 3.01/1.02  fof(f76,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f40])).
% 3.01/1.02  
% 3.01/1.02  fof(f5,axiom,(
% 3.01/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f26,plain,(
% 3.01/1.02    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.01/1.02    inference(ennf_transformation,[],[f5])).
% 3.01/1.02  
% 3.01/1.02  fof(f27,plain,(
% 3.01/1.02    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.01/1.02    inference(flattening,[],[f26])).
% 3.01/1.02  
% 3.01/1.02  fof(f63,plain,(
% 3.01/1.02    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f27])).
% 3.01/1.02  
% 3.01/1.02  fof(f15,axiom,(
% 3.01/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1)))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f41,plain,(
% 3.01/1.02    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.01/1.02    inference(ennf_transformation,[],[f15])).
% 3.01/1.02  
% 3.01/1.02  fof(f42,plain,(
% 3.01/1.02    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.01/1.02    inference(flattening,[],[f41])).
% 3.01/1.02  
% 3.01/1.02  fof(f78,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f42])).
% 3.01/1.02  
% 3.01/1.02  fof(f6,axiom,(
% 3.01/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f28,plain,(
% 3.01/1.02    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.01/1.02    inference(ennf_transformation,[],[f6])).
% 3.01/1.02  
% 3.01/1.02  fof(f29,plain,(
% 3.01/1.02    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.01/1.02    inference(flattening,[],[f28])).
% 3.01/1.02  
% 3.01/1.02  fof(f64,plain,(
% 3.01/1.02    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f29])).
% 3.01/1.02  
% 3.01/1.02  fof(f77,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (k5_relat_1(X2,k2_funct_1(X2)) = k6_partfun1(X0) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f42])).
% 3.01/1.02  
% 3.01/1.02  fof(f62,plain,(
% 3.01/1.02    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f27])).
% 3.01/1.02  
% 3.01/1.02  fof(f4,axiom,(
% 3.01/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f24,plain,(
% 3.01/1.02    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.01/1.02    inference(ennf_transformation,[],[f4])).
% 3.01/1.02  
% 3.01/1.02  fof(f25,plain,(
% 3.01/1.02    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.01/1.02    inference(flattening,[],[f24])).
% 3.01/1.02  
% 3.01/1.02  fof(f61,plain,(
% 3.01/1.02    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f25])).
% 3.01/1.02  
% 3.01/1.02  fof(f2,axiom,(
% 3.01/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f22,plain,(
% 3.01/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.01/1.02    inference(ennf_transformation,[],[f2])).
% 3.01/1.02  
% 3.01/1.02  fof(f23,plain,(
% 3.01/1.02    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.01/1.02    inference(flattening,[],[f22])).
% 3.01/1.02  
% 3.01/1.02  fof(f57,plain,(
% 3.01/1.02    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f23])).
% 3.01/1.02  
% 3.01/1.02  fof(f56,plain,(
% 3.01/1.02    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f23])).
% 3.01/1.02  
% 3.01/1.02  fof(f3,axiom,(
% 3.01/1.02    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f59,plain,(
% 3.01/1.02    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.01/1.02    inference(cnf_transformation,[],[f3])).
% 3.01/1.02  
% 3.01/1.02  fof(f11,axiom,(
% 3.01/1.02    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 3.01/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.01/1.02  
% 3.01/1.02  fof(f70,plain,(
% 3.01/1.02    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f11])).
% 3.01/1.02  
% 3.01/1.02  fof(f91,plain,(
% 3.01/1.02    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 3.01/1.02    inference(definition_unfolding,[],[f59,f70])).
% 3.01/1.02  
% 3.01/1.02  fof(f75,plain,(
% 3.01/1.02    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.01/1.02    inference(cnf_transformation,[],[f40])).
% 3.01/1.02  
% 3.01/1.02  cnf(c_29,negated_conjecture,
% 3.01/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.01/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_739,negated_conjecture,
% 3.01/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_29]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1264,plain,
% 3.01/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_739]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_23,plain,
% 3.01/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f79]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_34,negated_conjecture,
% 3.01/1.02      ( l1_struct_0(sK0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f82]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_421,plain,
% 3.01/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_34]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_422,plain,
% 3.01/1.02      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_421]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_733,plain,
% 3.01/1.02      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_422]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_32,negated_conjecture,
% 3.01/1.02      ( l1_struct_0(sK1) ),
% 3.01/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_416,plain,
% 3.01/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_23,c_32]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_417,plain,
% 3.01/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_416]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_734,plain,
% 3.01/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_417]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1295,plain,
% 3.01/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_1264,c_733,c_734]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_12,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f67]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_747,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/1.02      | k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_12]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1257,plain,
% 3.01/1.02      ( k2_relset_1(X0_55,X1_55,X0_54) = k2_relat_1(X0_54)
% 3.01/1.02      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_747]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1838,plain,
% 3.01/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1295,c_1257]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_28,negated_conjecture,
% 3.01/1.02      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.01/1.02      inference(cnf_transformation,[],[f88]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_740,negated_conjecture,
% 3.01/1.02      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_28]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1292,plain,
% 3.01/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_740,c_733,c_734]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1840,plain,
% 3.01/1.02      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_1838,c_1292]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1895,plain,
% 3.01/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_1840,c_1295]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_17,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.02      | v1_partfun1(X0,X1)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k1_xboole_0 = X2 ),
% 3.01/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_11,plain,
% 3.01/1.02      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.01/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_14,plain,
% 3.01/1.02      ( ~ v1_partfun1(X0,X1)
% 3.01/1.02      | ~ v4_relat_1(X0,X1)
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | k1_relat_1(X0) = X1 ),
% 3.01/1.02      inference(cnf_transformation,[],[f68]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_463,plain,
% 3.01/1.02      ( ~ v1_partfun1(X0,X1)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | k1_relat_1(X0) = X1 ),
% 3.01/1.02      inference(resolution,[status(thm)],[c_11,c_14]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_10,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_467,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v1_partfun1(X0,X1)
% 3.01/1.02      | k1_relat_1(X0) = X1 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_463,c_14,c_11,c_10]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_468,plain,
% 3.01/1.02      ( ~ v1_partfun1(X0,X1)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | k1_relat_1(X0) = X1 ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_467]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_507,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k1_relat_1(X0) = X1
% 3.01/1.02      | k1_xboole_0 = X2 ),
% 3.01/1.02      inference(resolution,[status(thm)],[c_17,c_468]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_511,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v1_funct_2(X0,X1,X2)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k1_relat_1(X0) = X1
% 3.01/1.02      | k1_xboole_0 = X2 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_507,c_17,c_10,c_463]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_512,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k1_relat_1(X0) = X1
% 3.01/1.02      | k1_xboole_0 = X2 ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_511]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_731,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.01/1.02      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | k1_relat_1(X0_54) = X0_55
% 3.01/1.02      | k1_xboole_0 = X1_55 ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_512]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1270,plain,
% 3.01/1.02      ( k1_relat_1(X0_54) = X0_55
% 3.01/1.02      | k1_xboole_0 = X1_55
% 3.01/1.02      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.01/1.02      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_731]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4001,plain,
% 3.01/1.02      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.01/1.02      | k2_relat_1(sK2) = k1_xboole_0
% 3.01/1.02      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1895,c_1270]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_31,negated_conjecture,
% 3.01/1.02      ( v1_funct_1(sK2) ),
% 3.01/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_38,plain,
% 3.01/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_30,negated_conjecture,
% 3.01/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.01/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_738,negated_conjecture,
% 3.01/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_30]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1265,plain,
% 3.01/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_738]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1289,plain,
% 3.01/1.02      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_1265,c_733,c_734]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1896,plain,
% 3.01/1.02      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_1840,c_1289]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_0,plain,
% 3.01/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f55]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_24,plain,
% 3.01/1.02      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.01/1.02      inference(cnf_transformation,[],[f80]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_389,plain,
% 3.01/1.02      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_0,c_24]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_33,negated_conjecture,
% 3.01/1.02      ( ~ v2_struct_0(sK1) ),
% 3.01/1.02      inference(cnf_transformation,[],[f83]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_407,plain,
% 3.01/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_389,c_33]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_408,plain,
% 3.01/1.02      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_407]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_391,plain,
% 3.01/1.02      ( v2_struct_0(sK1)
% 3.01/1.02      | ~ l1_struct_0(sK1)
% 3.01/1.02      | u1_struct_0(sK1) != k1_xboole_0 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_389]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_410,plain,
% 3.01/1.02      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_408,c_33,c_32,c_391]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_735,plain,
% 3.01/1.02      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_410]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1283,plain,
% 3.01/1.02      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_734,c_735]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1897,plain,
% 3.01/1.02      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_1840,c_1283]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4211,plain,
% 3.01/1.02      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_4001,c_38,c_1896,c_1897]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1893,plain,
% 3.01/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_1840,c_1838]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_25,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v2_funct_1(X0)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.01/1.02      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.01/1.02      inference(cnf_transformation,[],[f81]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_742,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.01/1.02      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/1.02      | ~ v2_funct_1(X0_54)
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.01/1.02      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_25]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1262,plain,
% 3.01/1.02      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.01/1.02      | k2_tops_2(X0_55,X1_55,X0_54) = k2_funct_1(X0_54)
% 3.01/1.02      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.01/1.02      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/1.02      | v2_funct_1(X0_54) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2757,plain,
% 3.01/1.02      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 3.01/1.02      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.01/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.01/1.02      | v2_funct_1(sK2) != iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1893,c_1262]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_27,negated_conjecture,
% 3.01/1.02      ( v2_funct_1(sK2) ),
% 3.01/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_41,plain,
% 3.01/1.02      ( v2_funct_1(sK2) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3186,plain,
% 3.01/1.02      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_2757,c_38,c_41,c_1895,c_1896]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_15,plain,
% 3.01/1.02      ( r2_funct_2(X0,X1,X2,X2)
% 3.01/1.02      | ~ v1_funct_2(X3,X0,X1)
% 3.01/1.02      | ~ v1_funct_2(X2,X0,X1)
% 3.01/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.01/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.01/1.02      | ~ v1_funct_1(X3)
% 3.01/1.02      | ~ v1_funct_1(X2) ),
% 3.01/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_26,negated_conjecture,
% 3.01/1.02      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.01/1.02      inference(cnf_transformation,[],[f90]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_428,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.02      | ~ v1_funct_2(X3,X1,X2)
% 3.01/1.02      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_funct_1(X3)
% 3.01/1.02      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X3
% 3.01/1.02      | u1_struct_0(sK1) != X2
% 3.01/1.02      | u1_struct_0(sK0) != X1
% 3.01/1.02      | sK2 != X3 ),
% 3.01/1.02      inference(resolution_lifted,[status(thm)],[c_15,c_26]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_429,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.01/1.02      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/1.02      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.01/1.02      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.01/1.02      inference(unflattening,[status(thm)],[c_428]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_732,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.01/1.02      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.01/1.02      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/1.02      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.01/1.02      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_429]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_759,plain,
% 3.01/1.02      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.01/1.02      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/1.02      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.01/1.02      | sP0_iProver_split
% 3.01/1.02      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.01/1.02      inference(splitting,
% 3.01/1.02                [splitting(split),new_symbols(definition,[])],
% 3.01/1.02                [c_732]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1268,plain,
% 3.01/1.02      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.01/1.02      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 3.01/1.02      | sP0_iProver_split = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1469,plain,
% 3.01/1.02      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.01/1.02      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 3.01/1.02      | sP0_iProver_split = iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_1268,c_733,c_734]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_758,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.01/1.02      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | ~ sP0_iProver_split ),
% 3.01/1.02      inference(splitting,
% 3.01/1.02                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.01/1.02                [c_732]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1269,plain,
% 3.01/1.02      ( v1_funct_2(X0_54,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.01/1.02      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top
% 3.01/1.02      | sP0_iProver_split != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_758]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1348,plain,
% 3.01/1.02      ( v1_funct_2(X0_54,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.01/1.02      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top
% 3.01/1.02      | sP0_iProver_split != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_1269,c_733,c_734]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1475,plain,
% 3.01/1.02      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.01/1.02      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.01/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_1469,c_1348]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1894,plain,
% 3.01/1.02      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 3.01/1.02      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_1840,c_1475]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3189,plain,
% 3.01/1.02      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 3.01/1.02      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_3186,c_1894]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4214,plain,
% 3.01/1.02      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 3.01/1.02      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_4211,c_3189]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_18,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.01/1.02      | ~ v2_funct_1(X0)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.01/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_746,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.01/1.02      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/1.02      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55)))
% 3.01/1.02      | ~ v2_funct_1(X0_54)
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1258,plain,
% 3.01/1.02      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.01/1.02      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.01/1.02      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_funct_1(X0_54),k1_zfmisc_1(k2_zfmisc_1(X1_55,X0_55))) = iProver_top
% 3.01/1.02      | v2_funct_1(X0_54) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2647,plain,
% 3.01/1.02      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 3.01/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.01/1.02      | v2_funct_1(sK2) != iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1893,c_1258]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3444,plain,
% 3.01/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_2647,c_38,c_41,c_1895,c_1896]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3450,plain,
% 3.01/1.02      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_3444,c_1257]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_741,negated_conjecture,
% 3.01/1.02      ( v2_funct_1(sK2) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_27]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1263,plain,
% 3.01/1.02      ( v2_funct_1(sK2) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_7,plain,
% 3.01/1.02      ( ~ v2_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_751,plain,
% 3.01/1.02      ( ~ v2_funct_1(X0_54)
% 3.01/1.02      | ~ v1_relat_1(X0_54)
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_7]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1253,plain,
% 3.01/1.02      ( k2_relat_1(k2_funct_1(X0_54)) = k1_relat_1(X0_54)
% 3.01/1.02      | v2_funct_1(X0_54) != iProver_top
% 3.01/1.02      | v1_relat_1(X0_54) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2019,plain,
% 3.01/1.02      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.01/1.02      | v1_relat_1(sK2) != iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1263,c_1253]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_813,plain,
% 3.01/1.02      ( ~ v2_funct_1(sK2)
% 3.01/1.02      | ~ v1_relat_1(sK2)
% 3.01/1.02      | ~ v1_funct_1(sK2)
% 3.01/1.02      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_751]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_748,plain,
% 3.01/1.02      ( ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/1.02      | v1_relat_1(X0_54) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1538,plain,
% 3.01/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.01/1.02      | v1_relat_1(sK2) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_748]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2233,plain,
% 3.01/1.02      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_2019,c_31,c_29,c_27,c_813,c_1538]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3455,plain,
% 3.01/1.02      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_3450,c_2233]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_21,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v2_funct_1(X0)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k2_relset_1(X1,X2,X0) != X2
% 3.01/1.02      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(X2)
% 3.01/1.02      | k1_xboole_0 = X2 ),
% 3.01/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_744,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.01/1.02      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/1.02      | ~ v2_funct_1(X0_54)
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.01/1.02      | k1_xboole_0 = X1_55
% 3.01/1.02      | k5_relat_1(k2_funct_1(X0_54),X0_54) = k6_partfun1(X1_55) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_21]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1260,plain,
% 3.01/1.02      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.01/1.02      | k1_xboole_0 = X1_55
% 3.01/1.02      | k5_relat_1(k2_funct_1(X0_54),X0_54) = k6_partfun1(X1_55)
% 3.01/1.02      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.01/1.02      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/1.02      | v2_funct_1(X0_54) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_744]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3496,plain,
% 3.01/1.02      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 3.01/1.02      | k2_struct_0(sK0) = k1_xboole_0
% 3.01/1.02      | k5_relat_1(k2_funct_1(k2_funct_1(sK2)),k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
% 3.01/1.02      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_3455,c_1260]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_9,plain,
% 3.01/1.02      ( ~ v2_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.01/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_749,plain,
% 3.01/1.02      ( ~ v2_funct_1(X0_54)
% 3.01/1.02      | ~ v1_relat_1(X0_54)
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | k2_funct_1(k2_funct_1(X0_54)) = X0_54 ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1255,plain,
% 3.01/1.02      ( k2_funct_1(k2_funct_1(X0_54)) = X0_54
% 3.01/1.02      | v2_funct_1(X0_54) != iProver_top
% 3.01/1.02      | v1_relat_1(X0_54) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1996,plain,
% 3.01/1.02      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.01/1.02      | v1_relat_1(sK2) != iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1263,c_1255]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_819,plain,
% 3.01/1.02      ( ~ v2_funct_1(sK2)
% 3.01/1.02      | ~ v1_relat_1(sK2)
% 3.01/1.02      | ~ v1_funct_1(sK2)
% 3.01/1.02      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_749]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2227,plain,
% 3.01/1.02      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_1996,c_31,c_29,c_27,c_819,c_1538]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3534,plain,
% 3.01/1.02      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 3.01/1.02      | k2_struct_0(sK0) = k1_xboole_0
% 3.01/1.02      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
% 3.01/1.02      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_3496,c_2227]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_22,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v2_funct_1(X0)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k2_relset_1(X1,X2,X0) != X2
% 3.01/1.02      | k5_relat_1(X0,k2_funct_1(X0)) = k6_partfun1(X1)
% 3.01/1.02      | k1_xboole_0 = X2 ),
% 3.01/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_743,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.01/1.02      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/1.02      | ~ v2_funct_1(X0_54)
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.01/1.02      | k1_xboole_0 = X1_55
% 3.01/1.02      | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_partfun1(X0_55) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_22]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1261,plain,
% 3.01/1.02      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.01/1.02      | k1_xboole_0 = X1_55
% 3.01/1.02      | k5_relat_1(X0_54,k2_funct_1(X0_54)) = k6_partfun1(X0_55)
% 3.01/1.02      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.01/1.02      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/1.02      | v2_funct_1(X0_54) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2859,plain,
% 3.01/1.02      ( k2_relat_1(sK2) = k1_xboole_0
% 3.01/1.02      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0))
% 3.01/1.02      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.01/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.01/1.02      | v2_funct_1(sK2) != iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1893,c_1261]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3683,plain,
% 3.01/1.02      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_partfun1(k2_struct_0(sK0)) ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_3534,c_38,c_41,c_1895,c_1896,c_1897,c_2859]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_8,plain,
% 3.01/1.02      ( ~ v2_funct_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_750,plain,
% 3.01/1.02      ( ~ v2_funct_1(X0_54)
% 3.01/1.02      | ~ v1_relat_1(X0_54)
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | k1_relat_1(k2_funct_1(X0_54)) = k2_relat_1(X0_54) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_8]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1254,plain,
% 3.01/1.02      ( k1_relat_1(k2_funct_1(X0_54)) = k2_relat_1(X0_54)
% 3.01/1.02      | v2_funct_1(X0_54) != iProver_top
% 3.01/1.02      | v1_relat_1(X0_54) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2139,plain,
% 3.01/1.02      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.01/1.02      | v1_relat_1(sK2) != iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1263,c_1254]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_816,plain,
% 3.01/1.02      ( ~ v2_funct_1(sK2)
% 3.01/1.02      | ~ v1_relat_1(sK2)
% 3.01/1.02      | ~ v1_funct_1(sK2)
% 3.01/1.02      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_750]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2320,plain,
% 3.01/1.02      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_2139,c_31,c_29,c_27,c_816,c_1538]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_5,plain,
% 3.01/1.02      ( v2_funct_1(X0)
% 3.01/1.02      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 3.01/1.02      | ~ v1_relat_1(X0)
% 3.01/1.02      | ~ v1_relat_1(X1)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | ~ v1_funct_1(X1)
% 3.01/1.02      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.01/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_753,plain,
% 3.01/1.02      ( v2_funct_1(X0_54)
% 3.01/1.02      | ~ v2_funct_1(k5_relat_1(X1_54,X0_54))
% 3.01/1.02      | ~ v1_relat_1(X0_54)
% 3.01/1.02      | ~ v1_relat_1(X1_54)
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | ~ v1_funct_1(X1_54)
% 3.01/1.02      | k1_relat_1(X0_54) != k2_relat_1(X1_54) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1251,plain,
% 3.01/1.02      ( k1_relat_1(X0_54) != k2_relat_1(X1_54)
% 3.01/1.02      | v2_funct_1(X0_54) = iProver_top
% 3.01/1.02      | v2_funct_1(k5_relat_1(X1_54,X0_54)) != iProver_top
% 3.01/1.02      | v1_relat_1(X0_54) != iProver_top
% 3.01/1.02      | v1_relat_1(X1_54) != iProver_top
% 3.01/1.02      | v1_funct_1(X1_54) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_753]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2324,plain,
% 3.01/1.02      ( k2_relat_1(X0_54) != k2_relat_1(sK2)
% 3.01/1.02      | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.01/1.02      | v1_relat_1(X0_54) != iProver_top
% 3.01/1.02      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_2320,c_1251]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_40,plain,
% 3.01/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1,plain,
% 3.01/1.02      ( ~ v1_relat_1(X0) | ~ v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)) ),
% 3.01/1.02      inference(cnf_transformation,[],[f57]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_757,plain,
% 3.01/1.02      ( ~ v1_relat_1(X0_54)
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | v1_funct_1(k2_funct_1(X0_54)) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_798,plain,
% 3.01/1.02      ( v1_relat_1(X0_54) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(X0_54)) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_800,plain,
% 3.01/1.02      ( v1_relat_1(sK2) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_798]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2,plain,
% 3.01/1.02      ( ~ v1_relat_1(X0) | v1_relat_1(k2_funct_1(X0)) | ~ v1_funct_1(X0) ),
% 3.01/1.02      inference(cnf_transformation,[],[f56]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_756,plain,
% 3.01/1.02      ( ~ v1_relat_1(X0_54)
% 3.01/1.02      | v1_relat_1(k2_funct_1(X0_54))
% 3.01/1.02      | ~ v1_funct_1(X0_54) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_801,plain,
% 3.01/1.02      ( v1_relat_1(X0_54) != iProver_top
% 3.01/1.02      | v1_relat_1(k2_funct_1(X0_54)) = iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_756]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_803,plain,
% 3.01/1.02      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.01/1.02      | v1_relat_1(sK2) != iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_801]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1539,plain,
% 3.01/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.01/1.02      | v1_relat_1(sK2) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_1538]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2961,plain,
% 3.01/1.02      ( v1_funct_1(X0_54) != iProver_top
% 3.01/1.02      | k2_relat_1(X0_54) != k2_relat_1(sK2)
% 3.01/1.02      | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.01/1.02      | v1_relat_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_2324,c_38,c_40,c_800,c_803,c_1539]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2962,plain,
% 3.01/1.02      ( k2_relat_1(X0_54) != k2_relat_1(sK2)
% 3.01/1.02      | v2_funct_1(k5_relat_1(X0_54,k2_funct_1(sK2))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.01/1.02      | v1_relat_1(X0_54) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_2961]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2973,plain,
% 3.01/1.02      ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.01/1.02      | v1_relat_1(sK2) != iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(equality_resolution,[status(thm)],[c_2962]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_771,plain,
% 3.01/1.02      ( k2_relat_1(X0_54) = k2_relat_1(X1_54) | X0_54 != X1_54 ),
% 3.01/1.02      theory(equality) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_784,plain,
% 3.01/1.02      ( k2_relat_1(sK2) = k2_relat_1(sK2) | sK2 != sK2 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_771]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_761,plain,( X0_54 = X0_54 ),theory(equality) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_794,plain,
% 3.01/1.02      ( sK2 = sK2 ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_761]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2964,plain,
% 3.01/1.02      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 3.01/1.02      | v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.01/1.02      | v1_relat_1(sK2) != iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(instantiation,[status(thm)],[c_2962]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3116,plain,
% 3.01/1.02      ( v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_2973,c_38,c_40,c_784,c_794,c_1539,c_2964]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3686,plain,
% 3.01/1.02      ( v2_funct_1(k6_partfun1(k2_struct_0(sK0))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_3683,c_3116]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3,plain,
% 3.01/1.02      ( v2_funct_1(k6_partfun1(X0)) ),
% 3.01/1.02      inference(cnf_transformation,[],[f91]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_755,plain,
% 3.01/1.02      ( v2_funct_1(k6_partfun1(X0_55)) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1249,plain,
% 3.01/1.02      ( v2_funct_1(k6_partfun1(X0_55)) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3852,plain,
% 3.01/1.02      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.01/1.02      inference(forward_subsumption_resolution,[status(thm)],[c_3686,c_1249]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3497,plain,
% 3.01/1.02      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 3.01/1.02      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.01/1.02      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_3455,c_1262]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3520,plain,
% 3.01/1.02      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 3.01/1.02      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 3.01/1.02      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_3497,c_2227]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_19,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.01/1.02      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.01/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.01/1.02      | ~ v2_funct_1(X0)
% 3.01/1.02      | ~ v1_funct_1(X0)
% 3.01/1.02      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.01/1.02      inference(cnf_transformation,[],[f75]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_745,plain,
% 3.01/1.02      ( ~ v1_funct_2(X0_54,X0_55,X1_55)
% 3.01/1.02      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55)
% 3.01/1.02      | ~ m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55)))
% 3.01/1.02      | ~ v2_funct_1(X0_54)
% 3.01/1.02      | ~ v1_funct_1(X0_54)
% 3.01/1.02      | k2_relset_1(X0_55,X1_55,X0_54) != X1_55 ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_19]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1259,plain,
% 3.01/1.02      ( k2_relset_1(X0_55,X1_55,X0_54) != X1_55
% 3.01/1.02      | v1_funct_2(X0_54,X0_55,X1_55) != iProver_top
% 3.01/1.02      | v1_funct_2(k2_funct_1(X0_54),X1_55,X0_55) = iProver_top
% 3.01/1.02      | m1_subset_1(X0_54,k1_zfmisc_1(k2_zfmisc_1(X0_55,X1_55))) != iProver_top
% 3.01/1.02      | v2_funct_1(X0_54) != iProver_top
% 3.01/1.02      | v1_funct_1(X0_54) != iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_745]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_2656,plain,
% 3.01/1.02      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 3.01/1.02      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.01/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.01/1.02      | v2_funct_1(sK2) != iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_1893,c_1259]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3561,plain,
% 3.01/1.02      ( v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.01/1.02      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 3.01/1.02      | k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_3520,c_38,c_40,c_41,c_800,c_1539,c_1895,c_1896,c_2647,
% 3.01/1.02                 c_2656]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_3562,plain,
% 3.01/1.02      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 3.01/1.02      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.02      inference(renaming,[status(thm)],[c_3561]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4216,plain,
% 3.01/1.02      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 3.01/1.02      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_4211,c_3562]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4241,plain,
% 3.01/1.02      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.02      inference(equality_resolution_simp,[status(thm)],[c_4216]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4651,plain,
% 3.01/1.02      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_4214,c_3852,c_4241]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4217,plain,
% 3.01/1.02      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_4211,c_3455]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4458,plain,
% 3.01/1.02      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.01/1.02      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.02      inference(superposition,[status(thm)],[c_4217,c_1262]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4478,plain,
% 3.01/1.02      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 3.01/1.02      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.01/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.01/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.01/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_4458,c_2227]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4533,plain,
% 3.01/1.02      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 3.01/1.02      inference(global_propositional_subsumption,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_4478,c_3852,c_4241]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4655,plain,
% 3.01/1.02      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.01/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.01/1.02      | v1_funct_1(sK2) != iProver_top ),
% 3.01/1.02      inference(light_normalisation,[status(thm)],[c_4651,c_4533]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_737,negated_conjecture,
% 3.01/1.02      ( v1_funct_1(sK2) ),
% 3.01/1.02      inference(subtyping,[status(esa)],[c_31]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_1266,plain,
% 3.01/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 3.01/1.02      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4221,plain,
% 3.01/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_4211,c_1895]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4223,plain,
% 3.01/1.02      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 3.01/1.02      inference(demodulation,[status(thm)],[c_4211,c_1896]) ).
% 3.01/1.02  
% 3.01/1.02  cnf(c_4659,plain,
% 3.01/1.02      ( $false ),
% 3.01/1.02      inference(forward_subsumption_resolution,
% 3.01/1.02                [status(thm)],
% 3.01/1.02                [c_4655,c_1266,c_4221,c_4223]) ).
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.01/1.02  
% 3.01/1.02  ------                               Statistics
% 3.01/1.02  
% 3.01/1.02  ------ General
% 3.01/1.02  
% 3.01/1.02  abstr_ref_over_cycles:                  0
% 3.01/1.02  abstr_ref_under_cycles:                 0
% 3.01/1.02  gc_basic_clause_elim:                   0
% 3.01/1.02  forced_gc_time:                         0
% 3.01/1.02  parsing_time:                           0.01
% 3.01/1.02  unif_index_cands_time:                  0.
% 3.01/1.02  unif_index_add_time:                    0.
% 3.01/1.02  orderings_time:                         0.
% 3.01/1.02  out_proof_time:                         0.023
% 3.01/1.02  total_time:                             0.235
% 3.01/1.02  num_of_symbols:                         63
% 3.01/1.02  num_of_terms:                           4135
% 3.01/1.02  
% 3.01/1.02  ------ Preprocessing
% 3.01/1.02  
% 3.01/1.02  num_of_splits:                          1
% 3.01/1.02  num_of_split_atoms:                     1
% 3.01/1.02  num_of_reused_defs:                     0
% 3.01/1.02  num_eq_ax_congr_red:                    7
% 3.01/1.02  num_of_sem_filtered_clauses:            2
% 3.01/1.02  num_of_subtypes:                        5
% 3.01/1.02  monotx_restored_types:                  1
% 3.01/1.02  sat_num_of_epr_types:                   0
% 3.01/1.02  sat_num_of_non_cyclic_types:            0
% 3.01/1.02  sat_guarded_non_collapsed_types:        1
% 3.01/1.02  num_pure_diseq_elim:                    0
% 3.01/1.02  simp_replaced_by:                       0
% 3.01/1.02  res_preprocessed:                       159
% 3.01/1.02  prep_upred:                             0
% 3.01/1.02  prep_unflattend:                        12
% 3.01/1.02  smt_new_axioms:                         0
% 3.01/1.02  pred_elim_cands:                        5
% 3.01/1.02  pred_elim:                              6
% 3.01/1.02  pred_elim_cl:                           7
% 3.01/1.02  pred_elim_cycles:                       8
% 3.01/1.02  merged_defs:                            0
% 3.01/1.02  merged_defs_ncl:                        0
% 3.01/1.02  bin_hyper_res:                          0
% 3.01/1.02  prep_cycles:                            4
% 3.01/1.02  pred_elim_time:                         0.005
% 3.01/1.02  splitting_time:                         0.
% 3.01/1.02  sem_filter_time:                        0.
% 3.01/1.02  monotx_time:                            0.
% 3.01/1.02  subtype_inf_time:                       0.002
% 3.01/1.02  
% 3.01/1.02  ------ Problem properties
% 3.01/1.02  
% 3.01/1.02  clauses:                                29
% 3.01/1.02  conjectures:                            5
% 3.01/1.02  epr:                                    2
% 3.01/1.02  horn:                                   26
% 3.01/1.02  ground:                                 9
% 3.01/1.02  unary:                                  10
% 3.01/1.02  binary:                                 2
% 3.01/1.02  lits:                                   100
% 3.01/1.02  lits_eq:                                24
% 3.01/1.02  fd_pure:                                0
% 3.01/1.02  fd_pseudo:                              0
% 3.01/1.02  fd_cond:                                2
% 3.01/1.02  fd_pseudo_cond:                         1
% 3.01/1.02  ac_symbols:                             0
% 3.01/1.02  
% 3.01/1.02  ------ Propositional Solver
% 3.01/1.02  
% 3.01/1.02  prop_solver_calls:                      29
% 3.01/1.02  prop_fast_solver_calls:                 1365
% 3.01/1.02  smt_solver_calls:                       0
% 3.01/1.02  smt_fast_solver_calls:                  0
% 3.01/1.02  prop_num_of_clauses:                    1580
% 3.01/1.02  prop_preprocess_simplified:             6038
% 3.01/1.02  prop_fo_subsumed:                       83
% 3.01/1.02  prop_solver_time:                       0.
% 3.01/1.02  smt_solver_time:                        0.
% 3.01/1.02  smt_fast_solver_time:                   0.
% 3.01/1.02  prop_fast_solver_time:                  0.
% 3.01/1.02  prop_unsat_core_time:                   0.
% 3.01/1.02  
% 3.01/1.02  ------ QBF
% 3.01/1.02  
% 3.01/1.02  qbf_q_res:                              0
% 3.01/1.02  qbf_num_tautologies:                    0
% 3.01/1.02  qbf_prep_cycles:                        0
% 3.01/1.02  
% 3.01/1.02  ------ BMC1
% 3.01/1.02  
% 3.01/1.02  bmc1_current_bound:                     -1
% 3.01/1.02  bmc1_last_solved_bound:                 -1
% 3.01/1.02  bmc1_unsat_core_size:                   -1
% 3.01/1.02  bmc1_unsat_core_parents_size:           -1
% 3.01/1.02  bmc1_merge_next_fun:                    0
% 3.01/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.01/1.02  
% 3.01/1.02  ------ Instantiation
% 3.01/1.02  
% 3.01/1.02  inst_num_of_clauses:                    558
% 3.01/1.02  inst_num_in_passive:                    114
% 3.01/1.02  inst_num_in_active:                     304
% 3.01/1.02  inst_num_in_unprocessed:                140
% 3.01/1.02  inst_num_of_loops:                      360
% 3.01/1.02  inst_num_of_learning_restarts:          0
% 3.01/1.02  inst_num_moves_active_passive:          52
% 3.01/1.02  inst_lit_activity:                      0
% 3.01/1.02  inst_lit_activity_moves:                0
% 3.01/1.02  inst_num_tautologies:                   0
% 3.01/1.02  inst_num_prop_implied:                  0
% 3.01/1.02  inst_num_existing_simplified:           0
% 3.01/1.02  inst_num_eq_res_simplified:             0
% 3.01/1.02  inst_num_child_elim:                    0
% 3.01/1.02  inst_num_of_dismatching_blockings:      112
% 3.01/1.02  inst_num_of_non_proper_insts:           525
% 3.01/1.02  inst_num_of_duplicates:                 0
% 3.01/1.02  inst_inst_num_from_inst_to_res:         0
% 3.01/1.02  inst_dismatching_checking_time:         0.
% 3.01/1.02  
% 3.01/1.02  ------ Resolution
% 3.01/1.02  
% 3.01/1.02  res_num_of_clauses:                     0
% 3.01/1.02  res_num_in_passive:                     0
% 3.01/1.02  res_num_in_active:                      0
% 3.01/1.02  res_num_of_loops:                       163
% 3.01/1.02  res_forward_subset_subsumed:            44
% 3.01/1.02  res_backward_subset_subsumed:           0
% 3.01/1.02  res_forward_subsumed:                   0
% 3.01/1.02  res_backward_subsumed:                  0
% 3.01/1.02  res_forward_subsumption_resolution:     1
% 3.01/1.02  res_backward_subsumption_resolution:    0
% 3.01/1.02  res_clause_to_clause_subsumption:       100
% 3.01/1.02  res_orphan_elimination:                 0
% 3.01/1.02  res_tautology_del:                      45
% 3.01/1.02  res_num_eq_res_simplified:              0
% 3.01/1.02  res_num_sel_changes:                    0
% 3.01/1.02  res_moves_from_active_to_pass:          0
% 3.01/1.02  
% 3.01/1.02  ------ Superposition
% 3.01/1.02  
% 3.01/1.02  sup_time_total:                         0.
% 3.01/1.02  sup_time_generating:                    0.
% 3.01/1.02  sup_time_sim_full:                      0.
% 3.01/1.02  sup_time_sim_immed:                     0.
% 3.01/1.02  
% 3.01/1.02  sup_num_of_clauses:                     52
% 3.01/1.02  sup_num_in_active:                      49
% 3.01/1.02  sup_num_in_passive:                     3
% 3.01/1.02  sup_num_of_loops:                       70
% 3.01/1.02  sup_fw_superposition:                   20
% 3.01/1.02  sup_bw_superposition:                   33
% 3.01/1.02  sup_immediate_simplified:               26
% 3.01/1.02  sup_given_eliminated:                   0
% 3.01/1.02  comparisons_done:                       0
% 3.01/1.02  comparisons_avoided:                    0
% 3.01/1.02  
% 3.01/1.02  ------ Simplifications
% 3.01/1.02  
% 3.01/1.02  
% 3.01/1.02  sim_fw_subset_subsumed:                 11
% 3.01/1.02  sim_bw_subset_subsumed:                 1
% 3.01/1.02  sim_fw_subsumed:                        4
% 3.01/1.02  sim_bw_subsumed:                        0
% 3.01/1.02  sim_fw_subsumption_res:                 5
% 3.01/1.02  sim_bw_subsumption_res:                 0
% 3.01/1.02  sim_tautology_del:                      0
% 3.01/1.02  sim_eq_tautology_del:                   6
% 3.01/1.02  sim_eq_res_simp:                        1
% 3.01/1.02  sim_fw_demodulated:                     0
% 3.01/1.02  sim_bw_demodulated:                     22
% 3.01/1.02  sim_light_normalised:                   21
% 3.01/1.02  sim_joinable_taut:                      0
% 3.01/1.02  sim_joinable_simp:                      0
% 3.01/1.02  sim_ac_normalised:                      0
% 3.01/1.02  sim_smt_subsumption:                    0
% 3.01/1.02  
%------------------------------------------------------------------------------
