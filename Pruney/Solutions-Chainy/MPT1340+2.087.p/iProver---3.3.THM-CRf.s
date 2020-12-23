%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:40 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :  204 (4501 expanded)
%              Number of clauses        :  131 (1460 expanded)
%              Number of leaves         :   19 (1253 expanded)
%              Depth                    :   26
%              Number of atoms          :  737 (27736 expanded)
%              Number of equality atoms :  287 (5014 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   18 (   3 average)
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

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
    inference(ennf_transformation,[],[f17])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f46,f45,f44])).

fof(f75,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f67,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f72,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f76,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
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

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

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

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f7])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f74,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

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

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f71,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

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

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f40])).

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
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f78,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f12,axiom,(
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
    inference(ennf_transformation,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f23,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f55,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f56,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f53,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_666,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1121,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_666])).

cnf(c_19,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_30,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_369,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_30])).

cnf(c_370,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_369])).

cnf(c_661,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_370])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_364,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_365,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_364])).

cnf(c_662,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_365])).

cnf(c_1149,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1121,c_661,c_662])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_673,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1115,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_673])).

cnf(c_1507,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1149,c_1115])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_667,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1146,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_667,c_661,c_662])).

cnf(c_1621,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1507,c_1146])).

cnf(c_1624,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1621,c_1149])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_12,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_450,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_15,c_12])).

cnf(c_9,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_454,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_450,c_9])).

cnf(c_659,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53 ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_1126,plain,
    ( k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_2,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_680,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_719,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_763,plain,
    ( k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_659])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_681,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
    | ~ v1_relat_1(X1_52)
    | v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1365,plain,
    ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | v1_relat_1(X0_52)
    | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_1366,plain,
    ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_relat_1(X0_52) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1365])).

cnf(c_3042,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | k1_xboole_0 = X1_53
    | k1_relat_1(X0_52) = X0_53 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1126,c_719,c_763,c_1366])).

cnf(c_3043,plain,
    ( k1_relat_1(X0_52) = X0_53
    | k1_xboole_0 = X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top ),
    inference(renaming,[status(thm)],[c_3042])).

cnf(c_3051,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1624,c_3043])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_665,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1122,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_665])).

cnf(c_1143,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1122,c_661,c_662])).

cnf(c_1625,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1621,c_1143])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_20,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_337,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_20])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_355,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_337,c_29])).

cnf(c_356,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_339,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_337])).

cnf(c_358,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_356,c_29,c_28,c_339])).

cnf(c_663,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(subtyping,[status(esa)],[c_358])).

cnf(c_1135,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_662,c_663])).

cnf(c_1626,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1621,c_1135])).

cnf(c_3433,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3051,c_34,c_1625,c_1626])).

cnf(c_1623,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1621,c_1507])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_669,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1119,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52)
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_2417,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_1119])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_37,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2630,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2417,c_34,c_37,c_1624,c_1625])).

cnf(c_13,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_22,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_376,plain,
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
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_377,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_376])).

cnf(c_660,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_52)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_377])).

cnf(c_683,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_660])).

cnf(c_1124,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_683])).

cnf(c_1289,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1124,c_661,c_662])).

cnf(c_682,plain,
    ( ~ v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_52)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_660])).

cnf(c_1125,plain,
    ( v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_682])).

cnf(c_1210,plain,
    ( v1_funct_2(X0_52,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1125,c_661,c_662])).

cnf(c_1295,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1289,c_1210])).

cnf(c_2254,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1295,c_1621])).

cnf(c_2633,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2630,c_2254])).

cnf(c_3436,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3433,c_2633])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_672,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1116,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_672])).

cnf(c_2345,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_1116])).

cnf(c_2636,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2345,c_34,c_37,c_1624,c_1625])).

cnf(c_2642,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2636,c_1115])).

cnf(c_664,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1123,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_664])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_676,plain,
    ( ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1112,plain,
    ( k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52)
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_676])).

cnf(c_1865,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1123,c_1112])).

cnf(c_732,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_676])).

cnf(c_1484,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1365])).

cnf(c_1513,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_2045,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1865,c_27,c_25,c_23,c_732,c_1484,c_1513])).

cnf(c_2649,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2642,c_2045])).

cnf(c_2727,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2649,c_1119])).

cnf(c_8,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_674,plain,
    ( ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | ~ v1_relat_1(X0_52)
    | k2_funct_1(k2_funct_1(X0_52)) = X0_52 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1114,plain,
    ( k2_funct_1(k2_funct_1(X0_52)) = X0_52
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_674])).

cnf(c_1836,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1123,c_1114])).

cnf(c_738,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_2029,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1836,c_27,c_25,c_23,c_738,c_1484,c_1513])).

cnf(c_2750,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2727,c_2029])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_679,plain,
    ( ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | v2_funct_1(k2_funct_1(X0_52))
    | ~ v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_722,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v2_funct_1(k2_funct_1(X0_52)) = iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_679])).

cnf(c_724,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_722])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_678,plain,
    ( ~ v1_funct_1(X0_52)
    | v1_funct_1(k2_funct_1(X0_52))
    | ~ v2_funct_1(X0_52)
    | ~ v1_relat_1(X0_52) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_725,plain,
    ( v1_funct_1(X0_52) != iProver_top
    | v1_funct_1(k2_funct_1(X0_52)) = iProver_top
    | v2_funct_1(X0_52) != iProver_top
    | v1_relat_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_678])).

cnf(c_727,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_725])).

cnf(c_1485,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1484])).

cnf(c_1514,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1513])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_671,plain,
    ( ~ v1_funct_2(X0_52,X0_53,X1_53)
    | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53)
    | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
    | ~ v1_funct_1(X0_52)
    | ~ v2_funct_1(X0_52)
    | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1117,plain,
    ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
    | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
    | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53) = iProver_top
    | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
    | v1_funct_1(X0_52) != iProver_top
    | v2_funct_1(X0_52) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_671])).

cnf(c_2354,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1623,c_1117])).

cnf(c_2759,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2750,c_34,c_36,c_37,c_724,c_727,c_1485,c_1514,c_1624,c_1625,c_2345,c_2354])).

cnf(c_3437,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_3433,c_2759])).

cnf(c_3462,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(equality_resolution_simp,[status(thm)],[c_3437])).

cnf(c_3465,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3436,c_3462])).

cnf(c_3466,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_3465])).

cnf(c_3442,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3433,c_1624])).

cnf(c_3444,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3433,c_1625])).

cnf(c_3470,plain,
    ( v1_funct_1(sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3466,c_3442,c_3444])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3470,c_34])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 09:35:11 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.73/1.01  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.01  
% 2.73/1.01  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.73/1.01  
% 2.73/1.01  ------  iProver source info
% 2.73/1.01  
% 2.73/1.01  git: date: 2020-06-30 10:37:57 +0100
% 2.73/1.01  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.73/1.01  git: non_committed_changes: false
% 2.73/1.01  git: last_make_outside_of_git: false
% 2.73/1.01  
% 2.73/1.01  ------ 
% 2.73/1.01  
% 2.73/1.01  ------ Input Options
% 2.73/1.01  
% 2.73/1.01  --out_options                           all
% 2.73/1.01  --tptp_safe_out                         true
% 2.73/1.01  --problem_path                          ""
% 2.73/1.01  --include_path                          ""
% 2.73/1.01  --clausifier                            res/vclausify_rel
% 2.73/1.01  --clausifier_options                    --mode clausify
% 2.73/1.01  --stdin                                 false
% 2.73/1.01  --stats_out                             all
% 2.73/1.01  
% 2.73/1.01  ------ General Options
% 2.73/1.01  
% 2.73/1.01  --fof                                   false
% 2.73/1.01  --time_out_real                         305.
% 2.73/1.01  --time_out_virtual                      -1.
% 2.73/1.01  --symbol_type_check                     false
% 2.73/1.01  --clausify_out                          false
% 2.73/1.01  --sig_cnt_out                           false
% 2.73/1.01  --trig_cnt_out                          false
% 2.73/1.01  --trig_cnt_out_tolerance                1.
% 2.73/1.01  --trig_cnt_out_sk_spl                   false
% 2.73/1.01  --abstr_cl_out                          false
% 2.73/1.01  
% 2.73/1.01  ------ Global Options
% 2.73/1.01  
% 2.73/1.01  --schedule                              default
% 2.73/1.01  --add_important_lit                     false
% 2.73/1.01  --prop_solver_per_cl                    1000
% 2.73/1.01  --min_unsat_core                        false
% 2.73/1.01  --soft_assumptions                      false
% 2.73/1.01  --soft_lemma_size                       3
% 2.73/1.01  --prop_impl_unit_size                   0
% 2.73/1.01  --prop_impl_unit                        []
% 2.73/1.01  --share_sel_clauses                     true
% 2.73/1.01  --reset_solvers                         false
% 2.73/1.01  --bc_imp_inh                            [conj_cone]
% 2.73/1.01  --conj_cone_tolerance                   3.
% 2.73/1.01  --extra_neg_conj                        none
% 2.73/1.01  --large_theory_mode                     true
% 2.73/1.01  --prolific_symb_bound                   200
% 2.73/1.01  --lt_threshold                          2000
% 2.73/1.01  --clause_weak_htbl                      true
% 2.73/1.01  --gc_record_bc_elim                     false
% 2.73/1.01  
% 2.73/1.01  ------ Preprocessing Options
% 2.73/1.01  
% 2.73/1.01  --preprocessing_flag                    true
% 2.73/1.01  --time_out_prep_mult                    0.1
% 2.73/1.01  --splitting_mode                        input
% 2.73/1.01  --splitting_grd                         true
% 2.73/1.01  --splitting_cvd                         false
% 2.73/1.01  --splitting_cvd_svl                     false
% 2.73/1.01  --splitting_nvd                         32
% 2.73/1.01  --sub_typing                            true
% 2.73/1.01  --prep_gs_sim                           true
% 2.73/1.01  --prep_unflatten                        true
% 2.73/1.01  --prep_res_sim                          true
% 2.73/1.01  --prep_upred                            true
% 2.73/1.01  --prep_sem_filter                       exhaustive
% 2.73/1.01  --prep_sem_filter_out                   false
% 2.73/1.01  --pred_elim                             true
% 2.73/1.01  --res_sim_input                         true
% 2.73/1.01  --eq_ax_congr_red                       true
% 2.73/1.01  --pure_diseq_elim                       true
% 2.73/1.01  --brand_transform                       false
% 2.73/1.01  --non_eq_to_eq                          false
% 2.73/1.01  --prep_def_merge                        true
% 2.73/1.01  --prep_def_merge_prop_impl              false
% 2.73/1.01  --prep_def_merge_mbd                    true
% 2.73/1.01  --prep_def_merge_tr_red                 false
% 2.73/1.01  --prep_def_merge_tr_cl                  false
% 2.73/1.01  --smt_preprocessing                     true
% 2.73/1.01  --smt_ac_axioms                         fast
% 2.73/1.01  --preprocessed_out                      false
% 2.73/1.01  --preprocessed_stats                    false
% 2.73/1.01  
% 2.73/1.01  ------ Abstraction refinement Options
% 2.73/1.01  
% 2.73/1.01  --abstr_ref                             []
% 2.73/1.01  --abstr_ref_prep                        false
% 2.73/1.01  --abstr_ref_until_sat                   false
% 2.73/1.01  --abstr_ref_sig_restrict                funpre
% 2.73/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.01  --abstr_ref_under                       []
% 2.73/1.01  
% 2.73/1.01  ------ SAT Options
% 2.73/1.01  
% 2.73/1.01  --sat_mode                              false
% 2.73/1.01  --sat_fm_restart_options                ""
% 2.73/1.01  --sat_gr_def                            false
% 2.73/1.01  --sat_epr_types                         true
% 2.73/1.01  --sat_non_cyclic_types                  false
% 2.73/1.01  --sat_finite_models                     false
% 2.73/1.01  --sat_fm_lemmas                         false
% 2.73/1.01  --sat_fm_prep                           false
% 2.73/1.01  --sat_fm_uc_incr                        true
% 2.73/1.01  --sat_out_model                         small
% 2.73/1.01  --sat_out_clauses                       false
% 2.73/1.01  
% 2.73/1.01  ------ QBF Options
% 2.73/1.01  
% 2.73/1.01  --qbf_mode                              false
% 2.73/1.01  --qbf_elim_univ                         false
% 2.73/1.01  --qbf_dom_inst                          none
% 2.73/1.01  --qbf_dom_pre_inst                      false
% 2.73/1.01  --qbf_sk_in                             false
% 2.73/1.01  --qbf_pred_elim                         true
% 2.73/1.01  --qbf_split                             512
% 2.73/1.01  
% 2.73/1.01  ------ BMC1 Options
% 2.73/1.01  
% 2.73/1.01  --bmc1_incremental                      false
% 2.73/1.01  --bmc1_axioms                           reachable_all
% 2.73/1.01  --bmc1_min_bound                        0
% 2.73/1.01  --bmc1_max_bound                        -1
% 2.73/1.01  --bmc1_max_bound_default                -1
% 2.73/1.01  --bmc1_symbol_reachability              true
% 2.73/1.01  --bmc1_property_lemmas                  false
% 2.73/1.01  --bmc1_k_induction                      false
% 2.73/1.01  --bmc1_non_equiv_states                 false
% 2.73/1.01  --bmc1_deadlock                         false
% 2.73/1.01  --bmc1_ucm                              false
% 2.73/1.01  --bmc1_add_unsat_core                   none
% 2.73/1.01  --bmc1_unsat_core_children              false
% 2.73/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.01  --bmc1_out_stat                         full
% 2.73/1.01  --bmc1_ground_init                      false
% 2.73/1.01  --bmc1_pre_inst_next_state              false
% 2.73/1.01  --bmc1_pre_inst_state                   false
% 2.73/1.01  --bmc1_pre_inst_reach_state             false
% 2.73/1.01  --bmc1_out_unsat_core                   false
% 2.73/1.01  --bmc1_aig_witness_out                  false
% 2.73/1.01  --bmc1_verbose                          false
% 2.73/1.01  --bmc1_dump_clauses_tptp                false
% 2.73/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.01  --bmc1_dump_file                        -
% 2.73/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.01  --bmc1_ucm_extend_mode                  1
% 2.73/1.01  --bmc1_ucm_init_mode                    2
% 2.73/1.01  --bmc1_ucm_cone_mode                    none
% 2.73/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.01  --bmc1_ucm_relax_model                  4
% 2.73/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.01  --bmc1_ucm_layered_model                none
% 2.73/1.01  --bmc1_ucm_max_lemma_size               10
% 2.73/1.01  
% 2.73/1.01  ------ AIG Options
% 2.73/1.01  
% 2.73/1.01  --aig_mode                              false
% 2.73/1.01  
% 2.73/1.01  ------ Instantiation Options
% 2.73/1.01  
% 2.73/1.01  --instantiation_flag                    true
% 2.73/1.01  --inst_sos_flag                         false
% 2.73/1.01  --inst_sos_phase                        true
% 2.73/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.01  --inst_lit_sel_side                     num_symb
% 2.73/1.01  --inst_solver_per_active                1400
% 2.73/1.01  --inst_solver_calls_frac                1.
% 2.73/1.01  --inst_passive_queue_type               priority_queues
% 2.73/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.01  --inst_passive_queues_freq              [25;2]
% 2.73/1.01  --inst_dismatching                      true
% 2.73/1.01  --inst_eager_unprocessed_to_passive     true
% 2.73/1.01  --inst_prop_sim_given                   true
% 2.73/1.01  --inst_prop_sim_new                     false
% 2.73/1.01  --inst_subs_new                         false
% 2.73/1.01  --inst_eq_res_simp                      false
% 2.73/1.01  --inst_subs_given                       false
% 2.73/1.01  --inst_orphan_elimination               true
% 2.73/1.01  --inst_learning_loop_flag               true
% 2.73/1.01  --inst_learning_start                   3000
% 2.73/1.01  --inst_learning_factor                  2
% 2.73/1.01  --inst_start_prop_sim_after_learn       3
% 2.73/1.01  --inst_sel_renew                        solver
% 2.73/1.01  --inst_lit_activity_flag                true
% 2.73/1.01  --inst_restr_to_given                   false
% 2.73/1.01  --inst_activity_threshold               500
% 2.73/1.01  --inst_out_proof                        true
% 2.73/1.01  
% 2.73/1.01  ------ Resolution Options
% 2.73/1.01  
% 2.73/1.01  --resolution_flag                       true
% 2.73/1.01  --res_lit_sel                           adaptive
% 2.73/1.01  --res_lit_sel_side                      none
% 2.73/1.01  --res_ordering                          kbo
% 2.73/1.01  --res_to_prop_solver                    active
% 2.73/1.01  --res_prop_simpl_new                    false
% 2.73/1.01  --res_prop_simpl_given                  true
% 2.73/1.01  --res_passive_queue_type                priority_queues
% 2.73/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.01  --res_passive_queues_freq               [15;5]
% 2.73/1.01  --res_forward_subs                      full
% 2.73/1.01  --res_backward_subs                     full
% 2.73/1.01  --res_forward_subs_resolution           true
% 2.73/1.01  --res_backward_subs_resolution          true
% 2.73/1.01  --res_orphan_elimination                true
% 2.73/1.01  --res_time_limit                        2.
% 2.73/1.01  --res_out_proof                         true
% 2.73/1.01  
% 2.73/1.01  ------ Superposition Options
% 2.73/1.01  
% 2.73/1.01  --superposition_flag                    true
% 2.73/1.01  --sup_passive_queue_type                priority_queues
% 2.73/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.01  --demod_completeness_check              fast
% 2.73/1.01  --demod_use_ground                      true
% 2.73/1.01  --sup_to_prop_solver                    passive
% 2.73/1.01  --sup_prop_simpl_new                    true
% 2.73/1.01  --sup_prop_simpl_given                  true
% 2.73/1.01  --sup_fun_splitting                     false
% 2.73/1.01  --sup_smt_interval                      50000
% 2.73/1.01  
% 2.73/1.01  ------ Superposition Simplification Setup
% 2.73/1.01  
% 2.73/1.01  --sup_indices_passive                   []
% 2.73/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.01  --sup_full_bw                           [BwDemod]
% 2.73/1.01  --sup_immed_triv                        [TrivRules]
% 2.73/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.01  --sup_immed_bw_main                     []
% 2.73/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.01  
% 2.73/1.01  ------ Combination Options
% 2.73/1.01  
% 2.73/1.01  --comb_res_mult                         3
% 2.73/1.01  --comb_sup_mult                         2
% 2.73/1.01  --comb_inst_mult                        10
% 2.73/1.01  
% 2.73/1.01  ------ Debug Options
% 2.73/1.01  
% 2.73/1.01  --dbg_backtrace                         false
% 2.73/1.01  --dbg_dump_prop_clauses                 false
% 2.73/1.01  --dbg_dump_prop_clauses_file            -
% 2.73/1.01  --dbg_out_stat                          false
% 2.73/1.01  ------ Parsing...
% 2.73/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.73/1.01  
% 2.73/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.73/1.01  
% 2.73/1.01  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.73/1.01  
% 2.73/1.01  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.73/1.01  ------ Proving...
% 2.73/1.01  ------ Problem Properties 
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  clauses                                 25
% 2.73/1.01  conjectures                             5
% 2.73/1.01  EPR                                     2
% 2.73/1.01  Horn                                    24
% 2.73/1.01  unary                                   9
% 2.73/1.01  binary                                  1
% 2.73/1.01  lits                                    82
% 2.73/1.01  lits eq                                 17
% 2.73/1.01  fd_pure                                 0
% 2.73/1.01  fd_pseudo                               0
% 2.73/1.01  fd_cond                                 0
% 2.73/1.01  fd_pseudo_cond                          1
% 2.73/1.01  AC symbols                              0
% 2.73/1.01  
% 2.73/1.01  ------ Schedule dynamic 5 is on 
% 2.73/1.01  
% 2.73/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  ------ 
% 2.73/1.01  Current options:
% 2.73/1.01  ------ 
% 2.73/1.01  
% 2.73/1.01  ------ Input Options
% 2.73/1.01  
% 2.73/1.01  --out_options                           all
% 2.73/1.01  --tptp_safe_out                         true
% 2.73/1.01  --problem_path                          ""
% 2.73/1.01  --include_path                          ""
% 2.73/1.01  --clausifier                            res/vclausify_rel
% 2.73/1.01  --clausifier_options                    --mode clausify
% 2.73/1.01  --stdin                                 false
% 2.73/1.01  --stats_out                             all
% 2.73/1.01  
% 2.73/1.01  ------ General Options
% 2.73/1.01  
% 2.73/1.01  --fof                                   false
% 2.73/1.01  --time_out_real                         305.
% 2.73/1.01  --time_out_virtual                      -1.
% 2.73/1.01  --symbol_type_check                     false
% 2.73/1.01  --clausify_out                          false
% 2.73/1.01  --sig_cnt_out                           false
% 2.73/1.01  --trig_cnt_out                          false
% 2.73/1.01  --trig_cnt_out_tolerance                1.
% 2.73/1.01  --trig_cnt_out_sk_spl                   false
% 2.73/1.01  --abstr_cl_out                          false
% 2.73/1.01  
% 2.73/1.01  ------ Global Options
% 2.73/1.01  
% 2.73/1.01  --schedule                              default
% 2.73/1.01  --add_important_lit                     false
% 2.73/1.01  --prop_solver_per_cl                    1000
% 2.73/1.01  --min_unsat_core                        false
% 2.73/1.01  --soft_assumptions                      false
% 2.73/1.01  --soft_lemma_size                       3
% 2.73/1.01  --prop_impl_unit_size                   0
% 2.73/1.01  --prop_impl_unit                        []
% 2.73/1.01  --share_sel_clauses                     true
% 2.73/1.01  --reset_solvers                         false
% 2.73/1.01  --bc_imp_inh                            [conj_cone]
% 2.73/1.01  --conj_cone_tolerance                   3.
% 2.73/1.01  --extra_neg_conj                        none
% 2.73/1.01  --large_theory_mode                     true
% 2.73/1.01  --prolific_symb_bound                   200
% 2.73/1.01  --lt_threshold                          2000
% 2.73/1.01  --clause_weak_htbl                      true
% 2.73/1.01  --gc_record_bc_elim                     false
% 2.73/1.01  
% 2.73/1.01  ------ Preprocessing Options
% 2.73/1.01  
% 2.73/1.01  --preprocessing_flag                    true
% 2.73/1.01  --time_out_prep_mult                    0.1
% 2.73/1.01  --splitting_mode                        input
% 2.73/1.01  --splitting_grd                         true
% 2.73/1.01  --splitting_cvd                         false
% 2.73/1.01  --splitting_cvd_svl                     false
% 2.73/1.01  --splitting_nvd                         32
% 2.73/1.01  --sub_typing                            true
% 2.73/1.01  --prep_gs_sim                           true
% 2.73/1.01  --prep_unflatten                        true
% 2.73/1.01  --prep_res_sim                          true
% 2.73/1.01  --prep_upred                            true
% 2.73/1.01  --prep_sem_filter                       exhaustive
% 2.73/1.01  --prep_sem_filter_out                   false
% 2.73/1.01  --pred_elim                             true
% 2.73/1.01  --res_sim_input                         true
% 2.73/1.01  --eq_ax_congr_red                       true
% 2.73/1.01  --pure_diseq_elim                       true
% 2.73/1.01  --brand_transform                       false
% 2.73/1.01  --non_eq_to_eq                          false
% 2.73/1.01  --prep_def_merge                        true
% 2.73/1.01  --prep_def_merge_prop_impl              false
% 2.73/1.01  --prep_def_merge_mbd                    true
% 2.73/1.01  --prep_def_merge_tr_red                 false
% 2.73/1.01  --prep_def_merge_tr_cl                  false
% 2.73/1.01  --smt_preprocessing                     true
% 2.73/1.01  --smt_ac_axioms                         fast
% 2.73/1.01  --preprocessed_out                      false
% 2.73/1.01  --preprocessed_stats                    false
% 2.73/1.01  
% 2.73/1.01  ------ Abstraction refinement Options
% 2.73/1.01  
% 2.73/1.01  --abstr_ref                             []
% 2.73/1.01  --abstr_ref_prep                        false
% 2.73/1.01  --abstr_ref_until_sat                   false
% 2.73/1.01  --abstr_ref_sig_restrict                funpre
% 2.73/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.73/1.01  --abstr_ref_under                       []
% 2.73/1.01  
% 2.73/1.01  ------ SAT Options
% 2.73/1.01  
% 2.73/1.01  --sat_mode                              false
% 2.73/1.01  --sat_fm_restart_options                ""
% 2.73/1.01  --sat_gr_def                            false
% 2.73/1.01  --sat_epr_types                         true
% 2.73/1.01  --sat_non_cyclic_types                  false
% 2.73/1.01  --sat_finite_models                     false
% 2.73/1.01  --sat_fm_lemmas                         false
% 2.73/1.01  --sat_fm_prep                           false
% 2.73/1.01  --sat_fm_uc_incr                        true
% 2.73/1.01  --sat_out_model                         small
% 2.73/1.01  --sat_out_clauses                       false
% 2.73/1.01  
% 2.73/1.01  ------ QBF Options
% 2.73/1.01  
% 2.73/1.01  --qbf_mode                              false
% 2.73/1.01  --qbf_elim_univ                         false
% 2.73/1.01  --qbf_dom_inst                          none
% 2.73/1.01  --qbf_dom_pre_inst                      false
% 2.73/1.01  --qbf_sk_in                             false
% 2.73/1.01  --qbf_pred_elim                         true
% 2.73/1.01  --qbf_split                             512
% 2.73/1.01  
% 2.73/1.01  ------ BMC1 Options
% 2.73/1.01  
% 2.73/1.01  --bmc1_incremental                      false
% 2.73/1.01  --bmc1_axioms                           reachable_all
% 2.73/1.01  --bmc1_min_bound                        0
% 2.73/1.01  --bmc1_max_bound                        -1
% 2.73/1.01  --bmc1_max_bound_default                -1
% 2.73/1.01  --bmc1_symbol_reachability              true
% 2.73/1.01  --bmc1_property_lemmas                  false
% 2.73/1.01  --bmc1_k_induction                      false
% 2.73/1.01  --bmc1_non_equiv_states                 false
% 2.73/1.01  --bmc1_deadlock                         false
% 2.73/1.01  --bmc1_ucm                              false
% 2.73/1.01  --bmc1_add_unsat_core                   none
% 2.73/1.01  --bmc1_unsat_core_children              false
% 2.73/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.73/1.01  --bmc1_out_stat                         full
% 2.73/1.01  --bmc1_ground_init                      false
% 2.73/1.01  --bmc1_pre_inst_next_state              false
% 2.73/1.01  --bmc1_pre_inst_state                   false
% 2.73/1.01  --bmc1_pre_inst_reach_state             false
% 2.73/1.01  --bmc1_out_unsat_core                   false
% 2.73/1.01  --bmc1_aig_witness_out                  false
% 2.73/1.01  --bmc1_verbose                          false
% 2.73/1.01  --bmc1_dump_clauses_tptp                false
% 2.73/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.73/1.01  --bmc1_dump_file                        -
% 2.73/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.73/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.73/1.01  --bmc1_ucm_extend_mode                  1
% 2.73/1.01  --bmc1_ucm_init_mode                    2
% 2.73/1.01  --bmc1_ucm_cone_mode                    none
% 2.73/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.73/1.01  --bmc1_ucm_relax_model                  4
% 2.73/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.73/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.73/1.01  --bmc1_ucm_layered_model                none
% 2.73/1.01  --bmc1_ucm_max_lemma_size               10
% 2.73/1.01  
% 2.73/1.01  ------ AIG Options
% 2.73/1.01  
% 2.73/1.01  --aig_mode                              false
% 2.73/1.01  
% 2.73/1.01  ------ Instantiation Options
% 2.73/1.01  
% 2.73/1.01  --instantiation_flag                    true
% 2.73/1.01  --inst_sos_flag                         false
% 2.73/1.01  --inst_sos_phase                        true
% 2.73/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.73/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.73/1.01  --inst_lit_sel_side                     none
% 2.73/1.01  --inst_solver_per_active                1400
% 2.73/1.01  --inst_solver_calls_frac                1.
% 2.73/1.01  --inst_passive_queue_type               priority_queues
% 2.73/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.73/1.01  --inst_passive_queues_freq              [25;2]
% 2.73/1.01  --inst_dismatching                      true
% 2.73/1.01  --inst_eager_unprocessed_to_passive     true
% 2.73/1.01  --inst_prop_sim_given                   true
% 2.73/1.01  --inst_prop_sim_new                     false
% 2.73/1.01  --inst_subs_new                         false
% 2.73/1.01  --inst_eq_res_simp                      false
% 2.73/1.01  --inst_subs_given                       false
% 2.73/1.01  --inst_orphan_elimination               true
% 2.73/1.01  --inst_learning_loop_flag               true
% 2.73/1.01  --inst_learning_start                   3000
% 2.73/1.01  --inst_learning_factor                  2
% 2.73/1.01  --inst_start_prop_sim_after_learn       3
% 2.73/1.01  --inst_sel_renew                        solver
% 2.73/1.01  --inst_lit_activity_flag                true
% 2.73/1.01  --inst_restr_to_given                   false
% 2.73/1.01  --inst_activity_threshold               500
% 2.73/1.01  --inst_out_proof                        true
% 2.73/1.01  
% 2.73/1.01  ------ Resolution Options
% 2.73/1.01  
% 2.73/1.01  --resolution_flag                       false
% 2.73/1.01  --res_lit_sel                           adaptive
% 2.73/1.01  --res_lit_sel_side                      none
% 2.73/1.01  --res_ordering                          kbo
% 2.73/1.01  --res_to_prop_solver                    active
% 2.73/1.01  --res_prop_simpl_new                    false
% 2.73/1.01  --res_prop_simpl_given                  true
% 2.73/1.01  --res_passive_queue_type                priority_queues
% 2.73/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.73/1.01  --res_passive_queues_freq               [15;5]
% 2.73/1.01  --res_forward_subs                      full
% 2.73/1.01  --res_backward_subs                     full
% 2.73/1.01  --res_forward_subs_resolution           true
% 2.73/1.01  --res_backward_subs_resolution          true
% 2.73/1.01  --res_orphan_elimination                true
% 2.73/1.01  --res_time_limit                        2.
% 2.73/1.01  --res_out_proof                         true
% 2.73/1.01  
% 2.73/1.01  ------ Superposition Options
% 2.73/1.01  
% 2.73/1.01  --superposition_flag                    true
% 2.73/1.01  --sup_passive_queue_type                priority_queues
% 2.73/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.73/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.73/1.01  --demod_completeness_check              fast
% 2.73/1.01  --demod_use_ground                      true
% 2.73/1.01  --sup_to_prop_solver                    passive
% 2.73/1.01  --sup_prop_simpl_new                    true
% 2.73/1.01  --sup_prop_simpl_given                  true
% 2.73/1.01  --sup_fun_splitting                     false
% 2.73/1.01  --sup_smt_interval                      50000
% 2.73/1.01  
% 2.73/1.01  ------ Superposition Simplification Setup
% 2.73/1.01  
% 2.73/1.01  --sup_indices_passive                   []
% 2.73/1.01  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.01  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.73/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.73/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.01  --sup_full_bw                           [BwDemod]
% 2.73/1.01  --sup_immed_triv                        [TrivRules]
% 2.73/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.73/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.01  --sup_immed_bw_main                     []
% 2.73/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.73/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.73/1.01  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.73/1.01  
% 2.73/1.01  ------ Combination Options
% 2.73/1.01  
% 2.73/1.01  --comb_res_mult                         3
% 2.73/1.01  --comb_sup_mult                         2
% 2.73/1.01  --comb_inst_mult                        10
% 2.73/1.01  
% 2.73/1.01  ------ Debug Options
% 2.73/1.01  
% 2.73/1.01  --dbg_backtrace                         false
% 2.73/1.01  --dbg_dump_prop_clauses                 false
% 2.73/1.01  --dbg_dump_prop_clauses_file            -
% 2.73/1.01  --dbg_out_stat                          false
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  ------ Proving...
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  % SZS status Theorem for theBenchmark.p
% 2.73/1.01  
% 2.73/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.73/1.01  
% 2.73/1.01  fof(f16,conjecture,(
% 2.73/1.01    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f17,negated_conjecture,(
% 2.73/1.01    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.73/1.01    inference(negated_conjecture,[],[f16])).
% 2.73/1.01  
% 2.73/1.01  fof(f41,plain,(
% 2.73/1.01    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.73/1.01    inference(ennf_transformation,[],[f17])).
% 2.73/1.01  
% 2.73/1.01  fof(f42,plain,(
% 2.73/1.01    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.73/1.01    inference(flattening,[],[f41])).
% 2.73/1.01  
% 2.73/1.01  fof(f46,plain,(
% 2.73/1.01    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.73/1.01    introduced(choice_axiom,[])).
% 2.73/1.01  
% 2.73/1.01  fof(f45,plain,(
% 2.73/1.01    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.73/1.01    introduced(choice_axiom,[])).
% 2.73/1.01  
% 2.73/1.01  fof(f44,plain,(
% 2.73/1.01    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.73/1.01    introduced(choice_axiom,[])).
% 2.73/1.01  
% 2.73/1.01  fof(f47,plain,(
% 2.73/1.01    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.73/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f42,f46,f45,f44])).
% 2.73/1.01  
% 2.73/1.01  fof(f75,plain,(
% 2.73/1.01    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.73/1.01    inference(cnf_transformation,[],[f47])).
% 2.73/1.01  
% 2.73/1.01  fof(f13,axiom,(
% 2.73/1.01    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f36,plain,(
% 2.73/1.01    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.73/1.01    inference(ennf_transformation,[],[f13])).
% 2.73/1.01  
% 2.73/1.01  fof(f67,plain,(
% 2.73/1.01    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f36])).
% 2.73/1.01  
% 2.73/1.01  fof(f70,plain,(
% 2.73/1.01    l1_struct_0(sK0)),
% 2.73/1.01    inference(cnf_transformation,[],[f47])).
% 2.73/1.01  
% 2.73/1.01  fof(f72,plain,(
% 2.73/1.01    l1_struct_0(sK1)),
% 2.73/1.01    inference(cnf_transformation,[],[f47])).
% 2.73/1.01  
% 2.73/1.01  fof(f8,axiom,(
% 2.73/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f27,plain,(
% 2.73/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.01    inference(ennf_transformation,[],[f8])).
% 2.73/1.01  
% 2.73/1.01  fof(f58,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/1.01    inference(cnf_transformation,[],[f27])).
% 2.73/1.01  
% 2.73/1.01  fof(f76,plain,(
% 2.73/1.01    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.73/1.01    inference(cnf_transformation,[],[f47])).
% 2.73/1.01  
% 2.73/1.01  fof(f11,axiom,(
% 2.73/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f32,plain,(
% 2.73/1.01    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.73/1.01    inference(ennf_transformation,[],[f11])).
% 2.73/1.01  
% 2.73/1.01  fof(f33,plain,(
% 2.73/1.01    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.73/1.01    inference(flattening,[],[f32])).
% 2.73/1.01  
% 2.73/1.01  fof(f62,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f33])).
% 2.73/1.01  
% 2.73/1.01  fof(f9,axiom,(
% 2.73/1.01    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f28,plain,(
% 2.73/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.73/1.01    inference(ennf_transformation,[],[f9])).
% 2.73/1.01  
% 2.73/1.01  fof(f29,plain,(
% 2.73/1.01    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.73/1.01    inference(flattening,[],[f28])).
% 2.73/1.01  
% 2.73/1.01  fof(f43,plain,(
% 2.73/1.01    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.73/1.01    inference(nnf_transformation,[],[f29])).
% 2.73/1.01  
% 2.73/1.01  fof(f59,plain,(
% 2.73/1.01    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f43])).
% 2.73/1.01  
% 2.73/1.01  fof(f7,axiom,(
% 2.73/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f18,plain,(
% 2.73/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.73/1.01    inference(pure_predicate_removal,[],[f7])).
% 2.73/1.01  
% 2.73/1.01  fof(f26,plain,(
% 2.73/1.01    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.73/1.01    inference(ennf_transformation,[],[f18])).
% 2.73/1.01  
% 2.73/1.01  fof(f57,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.73/1.01    inference(cnf_transformation,[],[f26])).
% 2.73/1.01  
% 2.73/1.01  fof(f3,axiom,(
% 2.73/1.01    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f50,plain,(
% 2.73/1.01    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.73/1.01    inference(cnf_transformation,[],[f3])).
% 2.73/1.01  
% 2.73/1.01  fof(f2,axiom,(
% 2.73/1.01    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f19,plain,(
% 2.73/1.01    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.73/1.01    inference(ennf_transformation,[],[f2])).
% 2.73/1.01  
% 2.73/1.01  fof(f49,plain,(
% 2.73/1.01    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f19])).
% 2.73/1.01  
% 2.73/1.01  fof(f73,plain,(
% 2.73/1.01    v1_funct_1(sK2)),
% 2.73/1.01    inference(cnf_transformation,[],[f47])).
% 2.73/1.01  
% 2.73/1.01  fof(f74,plain,(
% 2.73/1.01    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.73/1.01    inference(cnf_transformation,[],[f47])).
% 2.73/1.01  
% 2.73/1.01  fof(f1,axiom,(
% 2.73/1.01    v1_xboole_0(k1_xboole_0)),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f48,plain,(
% 2.73/1.01    v1_xboole_0(k1_xboole_0)),
% 2.73/1.01    inference(cnf_transformation,[],[f1])).
% 2.73/1.01  
% 2.73/1.01  fof(f14,axiom,(
% 2.73/1.01    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f37,plain,(
% 2.73/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.73/1.01    inference(ennf_transformation,[],[f14])).
% 2.73/1.01  
% 2.73/1.01  fof(f38,plain,(
% 2.73/1.01    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.73/1.01    inference(flattening,[],[f37])).
% 2.73/1.01  
% 2.73/1.01  fof(f68,plain,(
% 2.73/1.01    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f38])).
% 2.73/1.01  
% 2.73/1.01  fof(f71,plain,(
% 2.73/1.01    ~v2_struct_0(sK1)),
% 2.73/1.01    inference(cnf_transformation,[],[f47])).
% 2.73/1.01  
% 2.73/1.01  fof(f15,axiom,(
% 2.73/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f39,plain,(
% 2.73/1.01    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.73/1.01    inference(ennf_transformation,[],[f15])).
% 2.73/1.01  
% 2.73/1.01  fof(f40,plain,(
% 2.73/1.01    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.73/1.01    inference(flattening,[],[f39])).
% 2.73/1.01  
% 2.73/1.01  fof(f69,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f40])).
% 2.73/1.01  
% 2.73/1.01  fof(f77,plain,(
% 2.73/1.01    v2_funct_1(sK2)),
% 2.73/1.01    inference(cnf_transformation,[],[f47])).
% 2.73/1.01  
% 2.73/1.01  fof(f10,axiom,(
% 2.73/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f30,plain,(
% 2.73/1.01    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.73/1.01    inference(ennf_transformation,[],[f10])).
% 2.73/1.01  
% 2.73/1.01  fof(f31,plain,(
% 2.73/1.01    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.73/1.01    inference(flattening,[],[f30])).
% 2.73/1.01  
% 2.73/1.01  fof(f61,plain,(
% 2.73/1.01    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f31])).
% 2.73/1.01  
% 2.73/1.01  fof(f78,plain,(
% 2.73/1.01    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.73/1.01    inference(cnf_transformation,[],[f47])).
% 2.73/1.01  
% 2.73/1.01  fof(f12,axiom,(
% 2.73/1.01    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f34,plain,(
% 2.73/1.01    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.73/1.01    inference(ennf_transformation,[],[f12])).
% 2.73/1.01  
% 2.73/1.01  fof(f35,plain,(
% 2.73/1.01    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.73/1.01    inference(flattening,[],[f34])).
% 2.73/1.01  
% 2.73/1.01  fof(f66,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f35])).
% 2.73/1.01  
% 2.73/1.01  fof(f5,axiom,(
% 2.73/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f22,plain,(
% 2.73/1.01    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.73/1.01    inference(ennf_transformation,[],[f5])).
% 2.73/1.01  
% 2.73/1.01  fof(f23,plain,(
% 2.73/1.01    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.73/1.01    inference(flattening,[],[f22])).
% 2.73/1.01  
% 2.73/1.01  fof(f55,plain,(
% 2.73/1.01    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f23])).
% 2.73/1.01  
% 2.73/1.01  fof(f6,axiom,(
% 2.73/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f24,plain,(
% 2.73/1.01    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.73/1.01    inference(ennf_transformation,[],[f6])).
% 2.73/1.01  
% 2.73/1.01  fof(f25,plain,(
% 2.73/1.01    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.73/1.01    inference(flattening,[],[f24])).
% 2.73/1.01  
% 2.73/1.01  fof(f56,plain,(
% 2.73/1.01    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f25])).
% 2.73/1.01  
% 2.73/1.01  fof(f4,axiom,(
% 2.73/1.01    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.73/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.73/1.01  
% 2.73/1.01  fof(f20,plain,(
% 2.73/1.01    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.73/1.01    inference(ennf_transformation,[],[f4])).
% 2.73/1.01  
% 2.73/1.01  fof(f21,plain,(
% 2.73/1.01    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.73/1.01    inference(flattening,[],[f20])).
% 2.73/1.01  
% 2.73/1.01  fof(f53,plain,(
% 2.73/1.01    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f21])).
% 2.73/1.01  
% 2.73/1.01  fof(f52,plain,(
% 2.73/1.01    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f21])).
% 2.73/1.01  
% 2.73/1.01  fof(f65,plain,(
% 2.73/1.01    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.73/1.01    inference(cnf_transformation,[],[f35])).
% 2.73/1.01  
% 2.73/1.01  cnf(c_25,negated_conjecture,
% 2.73/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.73/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_666,negated_conjecture,
% 2.73/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_25]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1121,plain,
% 2.73/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_666]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_19,plain,
% 2.73/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.73/1.01      inference(cnf_transformation,[],[f67]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_30,negated_conjecture,
% 2.73/1.01      ( l1_struct_0(sK0) ),
% 2.73/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_369,plain,
% 2.73/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.73/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_30]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_370,plain,
% 2.73/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.73/1.01      inference(unflattening,[status(thm)],[c_369]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_661,plain,
% 2.73/1.01      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_370]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_28,negated_conjecture,
% 2.73/1.01      ( l1_struct_0(sK1) ),
% 2.73/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_364,plain,
% 2.73/1.01      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.73/1.01      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_365,plain,
% 2.73/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.73/1.01      inference(unflattening,[status(thm)],[c_364]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_662,plain,
% 2.73/1.01      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_365]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1149,plain,
% 2.73/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.73/1.01      inference(light_normalisation,[status(thm)],[c_1121,c_661,c_662]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_10,plain,
% 2.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.73/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_673,plain,
% 2.73/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.73/1.01      | k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_10]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1115,plain,
% 2.73/1.01      ( k2_relset_1(X0_53,X1_53,X0_52) = k2_relat_1(X0_52)
% 2.73/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_673]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1507,plain,
% 2.73/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.73/1.01      inference(superposition,[status(thm)],[c_1149,c_1115]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_24,negated_conjecture,
% 2.73/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.73/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_667,negated_conjecture,
% 2.73/1.01      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_24]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1146,plain,
% 2.73/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.73/1.01      inference(light_normalisation,[status(thm)],[c_667,c_661,c_662]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1621,plain,
% 2.73/1.01      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.73/1.01      inference(demodulation,[status(thm)],[c_1507,c_1146]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1624,plain,
% 2.73/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.73/1.01      inference(demodulation,[status(thm)],[c_1621,c_1149]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_15,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.01      | v1_partfun1(X0,X1)
% 2.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.01      | ~ v1_funct_1(X0)
% 2.73/1.01      | k1_xboole_0 = X2 ),
% 2.73/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_12,plain,
% 2.73/1.01      ( ~ v1_partfun1(X0,X1)
% 2.73/1.01      | ~ v4_relat_1(X0,X1)
% 2.73/1.01      | ~ v1_relat_1(X0)
% 2.73/1.01      | k1_relat_1(X0) = X1 ),
% 2.73/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_450,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.01      | ~ v4_relat_1(X0,X1)
% 2.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.01      | ~ v1_funct_1(X0)
% 2.73/1.01      | ~ v1_relat_1(X0)
% 2.73/1.01      | k1_relat_1(X0) = X1
% 2.73/1.01      | k1_xboole_0 = X2 ),
% 2.73/1.01      inference(resolution,[status(thm)],[c_15,c_12]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_9,plain,
% 2.73/1.01      ( v4_relat_1(X0,X1)
% 2.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.73/1.01      inference(cnf_transformation,[],[f57]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_454,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.01      | ~ v1_funct_1(X0)
% 2.73/1.01      | ~ v1_relat_1(X0)
% 2.73/1.01      | k1_relat_1(X0) = X1
% 2.73/1.01      | k1_xboole_0 = X2 ),
% 2.73/1.01      inference(global_propositional_subsumption,
% 2.73/1.01                [status(thm)],
% 2.73/1.01                [c_450,c_9]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_659,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.73/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.73/1.01      | ~ v1_funct_1(X0_52)
% 2.73/1.01      | ~ v1_relat_1(X0_52)
% 2.73/1.01      | k1_relat_1(X0_52) = X0_53
% 2.73/1.01      | k1_xboole_0 = X1_53 ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_454]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1126,plain,
% 2.73/1.01      ( k1_relat_1(X0_52) = X0_53
% 2.73/1.01      | k1_xboole_0 = X1_53
% 2.73/1.01      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.73/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.73/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2,plain,
% 2.73/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.73/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_680,plain,
% 2.73/1.01      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_2]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_719,plain,
% 2.73/1.01      ( v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) = iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_763,plain,
% 2.73/1.01      ( k1_relat_1(X0_52) = X0_53
% 2.73/1.01      | k1_xboole_0 = X1_53
% 2.73/1.01      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.73/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.73/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_659]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1,plain,
% 2.73/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.73/1.01      | ~ v1_relat_1(X1)
% 2.73/1.01      | v1_relat_1(X0) ),
% 2.73/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_681,plain,
% 2.73/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(X1_52))
% 2.73/1.01      | ~ v1_relat_1(X1_52)
% 2.73/1.01      | v1_relat_1(X0_52) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_1]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1365,plain,
% 2.73/1.01      ( ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.73/1.01      | v1_relat_1(X0_52)
% 2.73/1.01      | ~ v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_681]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1366,plain,
% 2.73/1.01      ( m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.73/1.01      | v1_relat_1(X0_52) = iProver_top
% 2.73/1.01      | v1_relat_1(k2_zfmisc_1(X0_53,X1_53)) != iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_1365]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3042,plain,
% 2.73/1.01      ( v1_funct_1(X0_52) != iProver_top
% 2.73/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.73/1.01      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.73/1.01      | k1_xboole_0 = X1_53
% 2.73/1.01      | k1_relat_1(X0_52) = X0_53 ),
% 2.73/1.01      inference(global_propositional_subsumption,
% 2.73/1.01                [status(thm)],
% 2.73/1.01                [c_1126,c_719,c_763,c_1366]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3043,plain,
% 2.73/1.01      ( k1_relat_1(X0_52) = X0_53
% 2.73/1.01      | k1_xboole_0 = X1_53
% 2.73/1.01      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.73/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.73/1.01      | v1_funct_1(X0_52) != iProver_top ),
% 2.73/1.01      inference(renaming,[status(thm)],[c_3042]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3051,plain,
% 2.73/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.73/1.01      | k2_relat_1(sK2) = k1_xboole_0
% 2.73/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.73/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.01      inference(superposition,[status(thm)],[c_1624,c_3043]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_27,negated_conjecture,
% 2.73/1.01      ( v1_funct_1(sK2) ),
% 2.73/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_34,plain,
% 2.73/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_26,negated_conjecture,
% 2.73/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.73/1.01      inference(cnf_transformation,[],[f74]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_665,negated_conjecture,
% 2.73/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_26]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1122,plain,
% 2.73/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_665]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1143,plain,
% 2.73/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.73/1.01      inference(light_normalisation,[status(thm)],[c_1122,c_661,c_662]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1625,plain,
% 2.73/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.73/1.01      inference(demodulation,[status(thm)],[c_1621,c_1143]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_0,plain,
% 2.73/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.73/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_20,plain,
% 2.73/1.01      ( v2_struct_0(X0)
% 2.73/1.01      | ~ l1_struct_0(X0)
% 2.73/1.01      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 2.73/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_337,plain,
% 2.73/1.01      ( v2_struct_0(X0)
% 2.73/1.01      | ~ l1_struct_0(X0)
% 2.73/1.01      | u1_struct_0(X0) != k1_xboole_0 ),
% 2.73/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_20]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_29,negated_conjecture,
% 2.73/1.01      ( ~ v2_struct_0(sK1) ),
% 2.73/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_355,plain,
% 2.73/1.01      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 2.73/1.01      inference(resolution_lifted,[status(thm)],[c_337,c_29]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_356,plain,
% 2.73/1.01      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.73/1.01      inference(unflattening,[status(thm)],[c_355]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_339,plain,
% 2.73/1.01      ( v2_struct_0(sK1)
% 2.73/1.01      | ~ l1_struct_0(sK1)
% 2.73/1.01      | u1_struct_0(sK1) != k1_xboole_0 ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_337]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_358,plain,
% 2.73/1.01      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.73/1.01      inference(global_propositional_subsumption,
% 2.73/1.01                [status(thm)],
% 2.73/1.01                [c_356,c_29,c_28,c_339]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_663,plain,
% 2.73/1.01      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_358]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1135,plain,
% 2.73/1.01      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 2.73/1.01      inference(demodulation,[status(thm)],[c_662,c_663]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1626,plain,
% 2.73/1.01      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 2.73/1.01      inference(demodulation,[status(thm)],[c_1621,c_1135]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3433,plain,
% 2.73/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.73/1.01      inference(global_propositional_subsumption,
% 2.73/1.01                [status(thm)],
% 2.73/1.01                [c_3051,c_34,c_1625,c_1626]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1623,plain,
% 2.73/1.01      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.73/1.01      inference(demodulation,[status(thm)],[c_1621,c_1507]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_21,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.01      | ~ v1_funct_1(X0)
% 2.73/1.01      | ~ v2_funct_1(X0)
% 2.73/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.73/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.73/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_669,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.73/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.73/1.01      | ~ v1_funct_1(X0_52)
% 2.73/1.01      | ~ v2_funct_1(X0_52)
% 2.73/1.01      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.73/1.01      | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_21]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1119,plain,
% 2.73/1.01      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.73/1.01      | k2_tops_2(X0_53,X1_53,X0_52) = k2_funct_1(X0_52)
% 2.73/1.01      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.73/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.73/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v2_funct_1(X0_52) != iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2417,plain,
% 2.73/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.73/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.73/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.73/1.01      | v1_funct_1(sK2) != iProver_top
% 2.73/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.73/1.01      inference(superposition,[status(thm)],[c_1623,c_1119]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_23,negated_conjecture,
% 2.73/1.01      ( v2_funct_1(sK2) ),
% 2.73/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_37,plain,
% 2.73/1.01      ( v2_funct_1(sK2) = iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2630,plain,
% 2.73/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.73/1.01      inference(global_propositional_subsumption,
% 2.73/1.01                [status(thm)],
% 2.73/1.01                [c_2417,c_34,c_37,c_1624,c_1625]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_13,plain,
% 2.73/1.01      ( r2_funct_2(X0,X1,X2,X2)
% 2.73/1.01      | ~ v1_funct_2(X3,X0,X1)
% 2.73/1.01      | ~ v1_funct_2(X2,X0,X1)
% 2.73/1.01      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.73/1.01      | ~ v1_funct_1(X3)
% 2.73/1.01      | ~ v1_funct_1(X2) ),
% 2.73/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_22,negated_conjecture,
% 2.73/1.01      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.73/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_376,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.01      | ~ v1_funct_2(X3,X1,X2)
% 2.73/1.01      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.01      | ~ v1_funct_1(X0)
% 2.73/1.01      | ~ v1_funct_1(X3)
% 2.73/1.01      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X3
% 2.73/1.01      | u1_struct_0(sK1) != X2
% 2.73/1.01      | u1_struct_0(sK0) != X1
% 2.73/1.01      | sK2 != X3 ),
% 2.73/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_377,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.73/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.73/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.73/1.01      | ~ v1_funct_1(X0)
% 2.73/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.73/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.73/1.01      inference(unflattening,[status(thm)],[c_376]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_660,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.73/1.01      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.73/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.73/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.73/1.01      | ~ v1_funct_1(X0_52)
% 2.73/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.73/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_377]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_683,plain,
% 2.73/1.01      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.73/1.01      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.73/1.01      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.73/1.01      | sP0_iProver_split
% 2.73/1.01      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.73/1.01      inference(splitting,
% 2.73/1.01                [splitting(split),new_symbols(definition,[])],
% 2.73/1.01                [c_660]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1124,plain,
% 2.73/1.01      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.73/1.01      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.73/1.01      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.73/1.01      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 2.73/1.01      | sP0_iProver_split = iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_683]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1289,plain,
% 2.73/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.73/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.73/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.73/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 2.73/1.01      | sP0_iProver_split = iProver_top ),
% 2.73/1.01      inference(light_normalisation,[status(thm)],[c_1124,c_661,c_662]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_682,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.73/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.73/1.01      | ~ v1_funct_1(X0_52)
% 2.73/1.01      | ~ sP0_iProver_split ),
% 2.73/1.01      inference(splitting,
% 2.73/1.01                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 2.73/1.01                [c_660]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1125,plain,
% 2.73/1.01      ( v1_funct_2(X0_52,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.73/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.73/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.73/1.01      | sP0_iProver_split != iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_682]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1210,plain,
% 2.73/1.01      ( v1_funct_2(X0_52,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.73/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.73/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.73/1.01      | sP0_iProver_split != iProver_top ),
% 2.73/1.01      inference(light_normalisation,[status(thm)],[c_1125,c_661,c_662]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1295,plain,
% 2.73/1.01      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.73/1.01      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.73/1.01      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.73/1.01      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.73/1.01      inference(forward_subsumption_resolution,
% 2.73/1.01                [status(thm)],
% 2.73/1.01                [c_1289,c_1210]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2254,plain,
% 2.73/1.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.73/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.73/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.73/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.73/1.01      inference(light_normalisation,[status(thm)],[c_1295,c_1621]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2633,plain,
% 2.73/1.01      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.73/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.73/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.73/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.73/1.01      inference(demodulation,[status(thm)],[c_2630,c_2254]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3436,plain,
% 2.73/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.73/1.01      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.73/1.01      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.73/1.01      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.73/1.01      inference(demodulation,[status(thm)],[c_3433,c_2633]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_16,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.01      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.73/1.01      | ~ v1_funct_1(X0)
% 2.73/1.01      | ~ v2_funct_1(X0)
% 2.73/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.73/1.01      inference(cnf_transformation,[],[f66]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_672,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.73/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.73/1.01      | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53)))
% 2.73/1.01      | ~ v1_funct_1(X0_52)
% 2.73/1.01      | ~ v2_funct_1(X0_52)
% 2.73/1.01      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_16]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1116,plain,
% 2.73/1.01      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.73/1.01      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.73/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.73/1.01      | m1_subset_1(k2_funct_1(X0_52),k1_zfmisc_1(k2_zfmisc_1(X1_53,X0_53))) = iProver_top
% 2.73/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v2_funct_1(X0_52) != iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_672]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2345,plain,
% 2.73/1.01      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.73/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 2.73/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.73/1.01      | v1_funct_1(sK2) != iProver_top
% 2.73/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.73/1.01      inference(superposition,[status(thm)],[c_1623,c_1116]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2636,plain,
% 2.73/1.01      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.73/1.01      inference(global_propositional_subsumption,
% 2.73/1.01                [status(thm)],
% 2.73/1.01                [c_2345,c_34,c_37,c_1624,c_1625]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2642,plain,
% 2.73/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.73/1.01      inference(superposition,[status(thm)],[c_2636,c_1115]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_664,negated_conjecture,
% 2.73/1.01      ( v1_funct_1(sK2) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_27]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1123,plain,
% 2.73/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_664]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_6,plain,
% 2.73/1.01      ( ~ v1_funct_1(X0)
% 2.73/1.01      | ~ v2_funct_1(X0)
% 2.73/1.01      | ~ v1_relat_1(X0)
% 2.73/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.73/1.01      inference(cnf_transformation,[],[f55]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_676,plain,
% 2.73/1.01      ( ~ v1_funct_1(X0_52)
% 2.73/1.01      | ~ v2_funct_1(X0_52)
% 2.73/1.01      | ~ v1_relat_1(X0_52)
% 2.73/1.01      | k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_6]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1112,plain,
% 2.73/1.01      ( k2_relat_1(k2_funct_1(X0_52)) = k1_relat_1(X0_52)
% 2.73/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v2_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_676]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1865,plain,
% 2.73/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.73/1.01      | v2_funct_1(sK2) != iProver_top
% 2.73/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.73/1.01      inference(superposition,[status(thm)],[c_1123,c_1112]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_732,plain,
% 2.73/1.01      ( ~ v1_funct_1(sK2)
% 2.73/1.01      | ~ v2_funct_1(sK2)
% 2.73/1.01      | ~ v1_relat_1(sK2)
% 2.73/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_676]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1484,plain,
% 2.73/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.73/1.01      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.73/1.01      | v1_relat_1(sK2) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_1365]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1513,plain,
% 2.73/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_680]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2045,plain,
% 2.73/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.73/1.01      inference(global_propositional_subsumption,
% 2.73/1.01                [status(thm)],
% 2.73/1.01                [c_1865,c_27,c_25,c_23,c_732,c_1484,c_1513]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2649,plain,
% 2.73/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.73/1.01      inference(light_normalisation,[status(thm)],[c_2642,c_2045]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2727,plain,
% 2.73/1.01      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.73/1.01      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.73/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.73/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.73/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.73/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.73/1.01      inference(superposition,[status(thm)],[c_2649,c_1119]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_8,plain,
% 2.73/1.01      ( ~ v1_funct_1(X0)
% 2.73/1.01      | ~ v2_funct_1(X0)
% 2.73/1.01      | ~ v1_relat_1(X0)
% 2.73/1.01      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.73/1.01      inference(cnf_transformation,[],[f56]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_674,plain,
% 2.73/1.01      ( ~ v1_funct_1(X0_52)
% 2.73/1.01      | ~ v2_funct_1(X0_52)
% 2.73/1.01      | ~ v1_relat_1(X0_52)
% 2.73/1.01      | k2_funct_1(k2_funct_1(X0_52)) = X0_52 ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_8]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1114,plain,
% 2.73/1.01      ( k2_funct_1(k2_funct_1(X0_52)) = X0_52
% 2.73/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v2_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_674]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1836,plain,
% 2.73/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.73/1.01      | v2_funct_1(sK2) != iProver_top
% 2.73/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.73/1.01      inference(superposition,[status(thm)],[c_1123,c_1114]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_738,plain,
% 2.73/1.01      ( ~ v1_funct_1(sK2)
% 2.73/1.01      | ~ v2_funct_1(sK2)
% 2.73/1.01      | ~ v1_relat_1(sK2)
% 2.73/1.01      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_674]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2029,plain,
% 2.73/1.01      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.73/1.01      inference(global_propositional_subsumption,
% 2.73/1.01                [status(thm)],
% 2.73/1.01                [c_1836,c_27,c_25,c_23,c_738,c_1484,c_1513]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2750,plain,
% 2.73/1.01      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.73/1.01      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.73/1.01      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.73/1.01      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.73/1.01      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.73/1.01      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.73/1.01      inference(light_normalisation,[status(thm)],[c_2727,c_2029]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_36,plain,
% 2.73/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3,plain,
% 2.73/1.01      ( ~ v1_funct_1(X0)
% 2.73/1.01      | ~ v2_funct_1(X0)
% 2.73/1.01      | v2_funct_1(k2_funct_1(X0))
% 2.73/1.01      | ~ v1_relat_1(X0) ),
% 2.73/1.01      inference(cnf_transformation,[],[f53]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_679,plain,
% 2.73/1.01      ( ~ v1_funct_1(X0_52)
% 2.73/1.01      | ~ v2_funct_1(X0_52)
% 2.73/1.01      | v2_funct_1(k2_funct_1(X0_52))
% 2.73/1.01      | ~ v1_relat_1(X0_52) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_3]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_722,plain,
% 2.73/1.01      ( v1_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v2_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v2_funct_1(k2_funct_1(X0_52)) = iProver_top
% 2.73/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_679]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_724,plain,
% 2.73/1.01      ( v1_funct_1(sK2) != iProver_top
% 2.73/1.01      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.73/1.01      | v2_funct_1(sK2) != iProver_top
% 2.73/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_722]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_4,plain,
% 2.73/1.01      ( ~ v1_funct_1(X0)
% 2.73/1.01      | v1_funct_1(k2_funct_1(X0))
% 2.73/1.01      | ~ v2_funct_1(X0)
% 2.73/1.01      | ~ v1_relat_1(X0) ),
% 2.73/1.01      inference(cnf_transformation,[],[f52]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_678,plain,
% 2.73/1.01      ( ~ v1_funct_1(X0_52)
% 2.73/1.01      | v1_funct_1(k2_funct_1(X0_52))
% 2.73/1.01      | ~ v2_funct_1(X0_52)
% 2.73/1.01      | ~ v1_relat_1(X0_52) ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_4]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_725,plain,
% 2.73/1.01      ( v1_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v1_funct_1(k2_funct_1(X0_52)) = iProver_top
% 2.73/1.01      | v2_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v1_relat_1(X0_52) != iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_678]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_727,plain,
% 2.73/1.01      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.73/1.01      | v1_funct_1(sK2) != iProver_top
% 2.73/1.01      | v2_funct_1(sK2) != iProver_top
% 2.73/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.73/1.01      inference(instantiation,[status(thm)],[c_725]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1485,plain,
% 2.73/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.73/1.01      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.73/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_1484]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1514,plain,
% 2.73/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_1513]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_17,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.73/1.01      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.73/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.73/1.01      | ~ v1_funct_1(X0)
% 2.73/1.01      | ~ v2_funct_1(X0)
% 2.73/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.73/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_671,plain,
% 2.73/1.01      ( ~ v1_funct_2(X0_52,X0_53,X1_53)
% 2.73/1.01      | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53)
% 2.73/1.01      | ~ m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53)))
% 2.73/1.01      | ~ v1_funct_1(X0_52)
% 2.73/1.01      | ~ v2_funct_1(X0_52)
% 2.73/1.01      | k2_relset_1(X0_53,X1_53,X0_52) != X1_53 ),
% 2.73/1.01      inference(subtyping,[status(esa)],[c_17]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_1117,plain,
% 2.73/1.01      ( k2_relset_1(X0_53,X1_53,X0_52) != X1_53
% 2.73/1.01      | v1_funct_2(X0_52,X0_53,X1_53) != iProver_top
% 2.73/1.01      | v1_funct_2(k2_funct_1(X0_52),X1_53,X0_53) = iProver_top
% 2.73/1.01      | m1_subset_1(X0_52,k1_zfmisc_1(k2_zfmisc_1(X0_53,X1_53))) != iProver_top
% 2.73/1.01      | v1_funct_1(X0_52) != iProver_top
% 2.73/1.01      | v2_funct_1(X0_52) != iProver_top ),
% 2.73/1.01      inference(predicate_to_equality,[status(thm)],[c_671]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2354,plain,
% 2.73/1.01      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 2.73/1.01      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.73/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.73/1.01      | v1_funct_1(sK2) != iProver_top
% 2.73/1.01      | v2_funct_1(sK2) != iProver_top ),
% 2.73/1.01      inference(superposition,[status(thm)],[c_1623,c_1117]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_2759,plain,
% 2.73/1.01      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.73/1.01      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.73/1.01      inference(global_propositional_subsumption,
% 2.73/1.01                [status(thm)],
% 2.73/1.01                [c_2750,c_34,c_36,c_37,c_724,c_727,c_1485,c_1514,c_1624,
% 2.73/1.01                 c_1625,c_2345,c_2354]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3437,plain,
% 2.73/1.01      ( k1_relat_1(sK2) != k1_relat_1(sK2)
% 2.73/1.01      | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.73/1.01      inference(demodulation,[status(thm)],[c_3433,c_2759]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3462,plain,
% 2.73/1.01      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.73/1.01      inference(equality_resolution_simp,[status(thm)],[c_3437]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3465,plain,
% 2.73/1.01      ( sK2 != sK2
% 2.73/1.01      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.73/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.73/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.01      inference(light_normalisation,[status(thm)],[c_3436,c_3462]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3466,plain,
% 2.73/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.73/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.73/1.01      | v1_funct_1(sK2) != iProver_top ),
% 2.73/1.01      inference(equality_resolution_simp,[status(thm)],[c_3465]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3442,plain,
% 2.73/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.73/1.01      inference(demodulation,[status(thm)],[c_3433,c_1624]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3444,plain,
% 2.73/1.01      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.73/1.01      inference(demodulation,[status(thm)],[c_3433,c_1625]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(c_3470,plain,
% 2.73/1.01      ( v1_funct_1(sK2) != iProver_top ),
% 2.73/1.01      inference(forward_subsumption_resolution,
% 2.73/1.01                [status(thm)],
% 2.73/1.01                [c_3466,c_3442,c_3444]) ).
% 2.73/1.01  
% 2.73/1.01  cnf(contradiction,plain,
% 2.73/1.01      ( $false ),
% 2.73/1.01      inference(minisat,[status(thm)],[c_3470,c_34]) ).
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.73/1.01  
% 2.73/1.01  ------                               Statistics
% 2.73/1.01  
% 2.73/1.01  ------ General
% 2.73/1.01  
% 2.73/1.01  abstr_ref_over_cycles:                  0
% 2.73/1.01  abstr_ref_under_cycles:                 0
% 2.73/1.01  gc_basic_clause_elim:                   0
% 2.73/1.01  forced_gc_time:                         0
% 2.73/1.01  parsing_time:                           0.009
% 2.73/1.01  unif_index_cands_time:                  0.
% 2.73/1.01  unif_index_add_time:                    0.
% 2.73/1.01  orderings_time:                         0.
% 2.73/1.01  out_proof_time:                         0.011
% 2.73/1.01  total_time:                             0.167
% 2.73/1.01  num_of_symbols:                         57
% 2.73/1.01  num_of_terms:                           3111
% 2.73/1.01  
% 2.73/1.01  ------ Preprocessing
% 2.73/1.01  
% 2.73/1.01  num_of_splits:                          1
% 2.73/1.01  num_of_split_atoms:                     1
% 2.73/1.01  num_of_reused_defs:                     0
% 2.73/1.01  num_eq_ax_congr_red:                    4
% 2.73/1.01  num_of_sem_filtered_clauses:            2
% 2.73/1.01  num_of_subtypes:                        4
% 2.73/1.01  monotx_restored_types:                  1
% 2.73/1.01  sat_num_of_epr_types:                   0
% 2.73/1.01  sat_num_of_non_cyclic_types:            0
% 2.73/1.01  sat_guarded_non_collapsed_types:        1
% 2.73/1.01  num_pure_diseq_elim:                    0
% 2.73/1.01  simp_replaced_by:                       0
% 2.73/1.01  res_preprocessed:                       139
% 2.73/1.01  prep_upred:                             0
% 2.73/1.01  prep_unflattend:                        12
% 2.73/1.01  smt_new_axioms:                         0
% 2.73/1.01  pred_elim_cands:                        5
% 2.73/1.01  pred_elim:                              6
% 2.73/1.01  pred_elim_cl:                           7
% 2.73/1.01  pred_elim_cycles:                       9
% 2.73/1.01  merged_defs:                            0
% 2.73/1.01  merged_defs_ncl:                        0
% 2.73/1.01  bin_hyper_res:                          0
% 2.73/1.01  prep_cycles:                            4
% 2.73/1.01  pred_elim_time:                         0.028
% 2.73/1.01  splitting_time:                         0.
% 2.73/1.01  sem_filter_time:                        0.
% 2.73/1.01  monotx_time:                            0.
% 2.73/1.01  subtype_inf_time:                       0.002
% 2.73/1.01  
% 2.73/1.01  ------ Problem properties
% 2.73/1.01  
% 2.73/1.01  clauses:                                25
% 2.73/1.01  conjectures:                            5
% 2.73/1.01  epr:                                    2
% 2.73/1.01  horn:                                   24
% 2.73/1.01  ground:                                 9
% 2.73/1.01  unary:                                  9
% 2.73/1.01  binary:                                 1
% 2.73/1.01  lits:                                   82
% 2.73/1.01  lits_eq:                                17
% 2.73/1.01  fd_pure:                                0
% 2.73/1.01  fd_pseudo:                              0
% 2.73/1.01  fd_cond:                                0
% 2.73/1.01  fd_pseudo_cond:                         1
% 2.73/1.01  ac_symbols:                             0
% 2.73/1.01  
% 2.73/1.01  ------ Propositional Solver
% 2.73/1.01  
% 2.73/1.01  prop_solver_calls:                      29
% 2.73/1.01  prop_fast_solver_calls:                 1122
% 2.73/1.01  smt_solver_calls:                       0
% 2.73/1.01  smt_fast_solver_calls:                  0
% 2.73/1.01  prop_num_of_clauses:                    1191
% 2.73/1.01  prop_preprocess_simplified:             4544
% 2.73/1.01  prop_fo_subsumed:                       57
% 2.73/1.01  prop_solver_time:                       0.
% 2.73/1.01  smt_solver_time:                        0.
% 2.73/1.01  smt_fast_solver_time:                   0.
% 2.73/1.01  prop_fast_solver_time:                  0.
% 2.73/1.01  prop_unsat_core_time:                   0.
% 2.73/1.01  
% 2.73/1.01  ------ QBF
% 2.73/1.01  
% 2.73/1.01  qbf_q_res:                              0
% 2.73/1.01  qbf_num_tautologies:                    0
% 2.73/1.01  qbf_prep_cycles:                        0
% 2.73/1.01  
% 2.73/1.01  ------ BMC1
% 2.73/1.01  
% 2.73/1.01  bmc1_current_bound:                     -1
% 2.73/1.01  bmc1_last_solved_bound:                 -1
% 2.73/1.01  bmc1_unsat_core_size:                   -1
% 2.73/1.01  bmc1_unsat_core_parents_size:           -1
% 2.73/1.01  bmc1_merge_next_fun:                    0
% 2.73/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.73/1.01  
% 2.73/1.01  ------ Instantiation
% 2.73/1.01  
% 2.73/1.01  inst_num_of_clauses:                    381
% 2.73/1.01  inst_num_in_passive:                    146
% 2.73/1.01  inst_num_in_active:                     209
% 2.73/1.01  inst_num_in_unprocessed:                26
% 2.73/1.01  inst_num_of_loops:                      260
% 2.73/1.01  inst_num_of_learning_restarts:          0
% 2.73/1.01  inst_num_moves_active_passive:          46
% 2.73/1.01  inst_lit_activity:                      0
% 2.73/1.01  inst_lit_activity_moves:                0
% 2.73/1.01  inst_num_tautologies:                   0
% 2.73/1.01  inst_num_prop_implied:                  0
% 2.73/1.01  inst_num_existing_simplified:           0
% 2.73/1.01  inst_num_eq_res_simplified:             0
% 2.73/1.01  inst_num_child_elim:                    0
% 2.73/1.01  inst_num_of_dismatching_blockings:      86
% 2.73/1.01  inst_num_of_non_proper_insts:           363
% 2.73/1.01  inst_num_of_duplicates:                 0
% 2.73/1.01  inst_inst_num_from_inst_to_res:         0
% 2.73/1.01  inst_dismatching_checking_time:         0.
% 2.73/1.01  
% 2.73/1.01  ------ Resolution
% 2.73/1.01  
% 2.73/1.01  res_num_of_clauses:                     0
% 2.73/1.01  res_num_in_passive:                     0
% 2.73/1.01  res_num_in_active:                      0
% 2.73/1.01  res_num_of_loops:                       143
% 2.73/1.01  res_forward_subset_subsumed:            36
% 2.73/1.01  res_backward_subset_subsumed:           0
% 2.73/1.01  res_forward_subsumed:                   0
% 2.73/1.01  res_backward_subsumed:                  0
% 2.73/1.01  res_forward_subsumption_resolution:     1
% 2.73/1.01  res_backward_subsumption_resolution:    0
% 2.73/1.01  res_clause_to_clause_subsumption:       159
% 2.73/1.01  res_orphan_elimination:                 0
% 2.73/1.01  res_tautology_del:                      33
% 2.73/1.01  res_num_eq_res_simplified:              0
% 2.73/1.01  res_num_sel_changes:                    0
% 2.73/1.01  res_moves_from_active_to_pass:          0
% 2.73/1.01  
% 2.73/1.01  ------ Superposition
% 2.73/1.01  
% 2.73/1.01  sup_time_total:                         0.
% 2.73/1.01  sup_time_generating:                    0.
% 2.73/1.01  sup_time_sim_full:                      0.
% 2.73/1.01  sup_time_sim_immed:                     0.
% 2.73/1.01  
% 2.73/1.01  sup_num_of_clauses:                     47
% 2.73/1.01  sup_num_in_active:                      33
% 2.73/1.01  sup_num_in_passive:                     14
% 2.73/1.01  sup_num_of_loops:                       50
% 2.73/1.01  sup_fw_superposition:                   32
% 2.73/1.01  sup_bw_superposition:                   14
% 2.73/1.01  sup_immediate_simplified:               24
% 2.73/1.01  sup_given_eliminated:                   0
% 2.73/1.01  comparisons_done:                       0
% 2.73/1.01  comparisons_avoided:                    0
% 2.73/1.01  
% 2.73/1.01  ------ Simplifications
% 2.73/1.01  
% 2.73/1.01  
% 2.73/1.01  sim_fw_subset_subsumed:                 3
% 2.73/1.01  sim_bw_subset_subsumed:                 0
% 2.73/1.01  sim_fw_subsumed:                        3
% 2.73/1.01  sim_bw_subsumed:                        0
% 2.73/1.01  sim_fw_subsumption_res:                 3
% 2.73/1.01  sim_bw_subsumption_res:                 0
% 2.73/1.01  sim_tautology_del:                      0
% 2.73/1.01  sim_eq_tautology_del:                   15
% 2.73/1.01  sim_eq_res_simp:                        2
% 2.73/1.01  sim_fw_demodulated:                     0
% 2.73/1.01  sim_bw_demodulated:                     18
% 2.73/1.01  sim_light_normalised:                   27
% 2.73/1.01  sim_joinable_taut:                      0
% 2.73/1.01  sim_joinable_simp:                      0
% 2.73/1.01  sim_ac_normalised:                      0
% 2.73/1.01  sim_smt_subsumption:                    0
% 2.73/1.01  
%------------------------------------------------------------------------------
