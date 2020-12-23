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
% DateTime   : Thu Dec  3 12:17:24 EST 2020

% Result     : Theorem 2.56s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :  214 (10942 expanded)
%              Number of clauses        :  143 (3994 expanded)
%              Number of leaves         :   19 (2871 expanded)
%              Depth                    :   26
%              Number of atoms          :  808 (64272 expanded)
%              Number of equality atoms :  345 (11607 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f39,plain,(
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
    inference(ennf_transformation,[],[f15])).

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
    inference(flattening,[],[f39])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f45,f44,f43])).

fof(f68,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f62,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f66,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f63,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f67,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f4])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f35])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f73,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f9,axiom,(
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

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f48,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f49,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f76,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f58])).

fof(f74,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_25,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_689,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1103,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_689])).

cnf(c_15,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_697,plain,
    ( ~ l1_struct_0(X0_53)
    | u1_struct_0(X0_53) = k2_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1096,plain,
    ( u1_struct_0(X0_53) = k2_struct_0(X0_53)
    | l1_struct_0(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_697])).

cnf(c_1376,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1103,c_1096])).

cnf(c_22,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_692,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1100,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_692])).

cnf(c_1571,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1376,c_1100])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_688,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1104,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_688])).

cnf(c_1377,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1104,c_1096])).

cnf(c_21,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_693,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_1573,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1376,c_693])).

cnf(c_1643,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1377,c_1573])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_701,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1092,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_701])).

cnf(c_1428,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1100,c_1092])).

cnf(c_1719,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1428,c_1376,c_1377])).

cnf(c_1721,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1643,c_1719])).

cnf(c_1796,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1571,c_1377,c_1721])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_16,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_26,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_301,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_302,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_301])).

cnf(c_43,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_304,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_302,c_26,c_25,c_43])).

cnf(c_314,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_304])).

cnf(c_315,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_4,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_9,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_337,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_4,c_9])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_337,c_9,c_4,c_3])).

cnf(c_342,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_341])).

cnf(c_381,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_315,c_342])).

cnf(c_687,plain,
    ( ~ v1_funct_2(X0_51,X0_52,k2_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0_51)
    | k1_relat_1(X0_51) = X0_52 ),
    inference(subtyping,[status(esa)],[c_381])).

cnf(c_1105,plain,
    ( k1_relat_1(X0_51) = X0_52
    | v1_funct_2(X0_51,X0_52,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_687])).

cnf(c_2298,plain,
    ( k1_relat_1(X0_51) = X0_52
    | v1_funct_2(X0_51,X0_52,k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1105,c_1721])).

cnf(c_2307,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_52))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_2298])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_31,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_23,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_691,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1101,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_691])).

cnf(c_1572,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1376,c_1101])).

cnf(c_1645,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1572,c_1377])).

cnf(c_1724,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1721,c_1645])).

cnf(c_3129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_52))) != iProver_top
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2307,c_31,c_1724])).

cnf(c_3130,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_52))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3129])).

cnf(c_3137,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1796,c_3130])).

cnf(c_1723,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1721,c_1719])).

cnf(c_3258,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3137,c_1723])).

cnf(c_1725,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1721,c_1376])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_695,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X0_53)
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51))
    | k2_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51) != k2_struct_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1098,plain,
    ( k2_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51) != k2_struct_0(X1_53)
    | v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(X1_53) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_695])).

cnf(c_2381,plain,
    ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
    | v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_1098])).

cnf(c_2444,plain,
    ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2381,c_1377])).

cnf(c_28,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2829,plain,
    ( l1_struct_0(X0_53) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2444,c_28])).

cnf(c_2830,plain,
    ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2829])).

cnf(c_2843,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_struct_0(sK1)
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1725,c_2830])).

cnf(c_2851,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
    | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2843,c_1721,c_1725])).

cnf(c_30,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3957,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2851,c_30])).

cnf(c_3958,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
    | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3957])).

cnf(c_3963,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
    | v1_funct_2(X0_51,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),X0_51)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3958,c_3137])).

cnf(c_4354,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3258,c_3963])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_696,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1097,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51)
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_696])).

cnf(c_2250,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_1097])).

cnf(c_20,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_34,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2553,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2250,c_31,c_34,c_1724,c_1796])).

cnf(c_3257,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3137,c_2553])).

cnf(c_4360,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4354,c_3257])).

cnf(c_3259,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3137,c_1724])).

cnf(c_3260,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3137,c_1796])).

cnf(c_4413,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4360,c_31,c_34,c_3259,c_3260])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_700,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1093,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_700])).

cnf(c_2249,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_1093])).

cnf(c_2702,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2249,c_31,c_34,c_1724,c_1796])).

cnf(c_2707,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2702,c_1092])).

cnf(c_702,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1091,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_702])).

cnf(c_1423,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1100,c_1091])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_705,plain,
    ( ~ v1_relat_1(X0_51)
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1088,plain,
    ( k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51)
    | v1_relat_1(X0_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_705])).

cnf(c_1492,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_1088])).

cnf(c_741,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_705])).

cnf(c_1284,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_702])).

cnf(c_2102,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1492,c_24,c_22,c_20,c_741,c_1284])).

cnf(c_2712,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2707,c_2102])).

cnf(c_3090,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2712,c_1097])).

cnf(c_2,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f49])).

cnf(c_703,plain,
    ( ~ v1_relat_1(X0_51)
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_funct_1(k2_funct_1(X0_51)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1090,plain,
    ( k2_funct_1(k2_funct_1(X0_51)) = X0_51
    | v1_relat_1(X0_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_703])).

cnf(c_1491,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1423,c_1090])).

cnf(c_747,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_703])).

cnf(c_2048,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1491,c_24,c_22,c_20,c_747,c_1284])).

cnf(c_3113,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3090,c_2048])).

cnf(c_32,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_33,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_765,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_697])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_698,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_funct_1(X0_51))
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1313,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_1314,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1313])).

cnf(c_712,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_1335,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_52
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_52 ),
    inference(instantiation,[status(thm)],[c_712])).

cnf(c_1448,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1335])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_699,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1094,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_699])).

cnf(c_2251,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1723,c_1094])).

cnf(c_3537,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3113,c_25,c_31,c_32,c_33,c_34,c_765,c_693,c_1314,c_1448,c_1724,c_1796,c_2249,c_2251,c_3137])).

cnf(c_3541,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3537,c_3137])).

cnf(c_4418,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_4413,c_3541])).

cnf(c_10,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_19,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_474,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_19])).

cnf(c_475,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_474])).

cnf(c_686,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_475])).

cnf(c_1106,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_686])).

cnf(c_1570,plain,
    ( k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1376,c_1106])).

cnf(c_2185,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1570,c_1377,c_1721])).

cnf(c_2556,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2553,c_2185])).

cnf(c_3842,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2556,c_3137])).

cnf(c_4420,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4418,c_3842])).

cnf(c_707,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_736,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_707])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4420,c_3260,c_3259,c_736,c_31])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:18:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.56/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.02  
% 2.56/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.56/1.02  
% 2.56/1.02  ------  iProver source info
% 2.56/1.02  
% 2.56/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.56/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.56/1.02  git: non_committed_changes: false
% 2.56/1.02  git: last_make_outside_of_git: false
% 2.56/1.02  
% 2.56/1.02  ------ 
% 2.56/1.02  
% 2.56/1.02  ------ Input Options
% 2.56/1.02  
% 2.56/1.02  --out_options                           all
% 2.56/1.02  --tptp_safe_out                         true
% 2.56/1.02  --problem_path                          ""
% 2.56/1.02  --include_path                          ""
% 2.56/1.02  --clausifier                            res/vclausify_rel
% 2.56/1.02  --clausifier_options                    --mode clausify
% 2.56/1.02  --stdin                                 false
% 2.56/1.02  --stats_out                             all
% 2.56/1.02  
% 2.56/1.02  ------ General Options
% 2.56/1.02  
% 2.56/1.02  --fof                                   false
% 2.56/1.02  --time_out_real                         305.
% 2.56/1.02  --time_out_virtual                      -1.
% 2.56/1.02  --symbol_type_check                     false
% 2.56/1.02  --clausify_out                          false
% 2.56/1.02  --sig_cnt_out                           false
% 2.56/1.02  --trig_cnt_out                          false
% 2.56/1.02  --trig_cnt_out_tolerance                1.
% 2.56/1.02  --trig_cnt_out_sk_spl                   false
% 2.56/1.02  --abstr_cl_out                          false
% 2.56/1.02  
% 2.56/1.02  ------ Global Options
% 2.56/1.02  
% 2.56/1.02  --schedule                              default
% 2.56/1.02  --add_important_lit                     false
% 2.56/1.02  --prop_solver_per_cl                    1000
% 2.56/1.02  --min_unsat_core                        false
% 2.56/1.02  --soft_assumptions                      false
% 2.56/1.02  --soft_lemma_size                       3
% 2.56/1.02  --prop_impl_unit_size                   0
% 2.56/1.02  --prop_impl_unit                        []
% 2.56/1.02  --share_sel_clauses                     true
% 2.56/1.02  --reset_solvers                         false
% 2.56/1.02  --bc_imp_inh                            [conj_cone]
% 2.56/1.02  --conj_cone_tolerance                   3.
% 2.56/1.02  --extra_neg_conj                        none
% 2.56/1.02  --large_theory_mode                     true
% 2.56/1.02  --prolific_symb_bound                   200
% 2.56/1.02  --lt_threshold                          2000
% 2.56/1.02  --clause_weak_htbl                      true
% 2.56/1.02  --gc_record_bc_elim                     false
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing Options
% 2.56/1.02  
% 2.56/1.02  --preprocessing_flag                    true
% 2.56/1.02  --time_out_prep_mult                    0.1
% 2.56/1.02  --splitting_mode                        input
% 2.56/1.02  --splitting_grd                         true
% 2.56/1.02  --splitting_cvd                         false
% 2.56/1.02  --splitting_cvd_svl                     false
% 2.56/1.02  --splitting_nvd                         32
% 2.56/1.02  --sub_typing                            true
% 2.56/1.02  --prep_gs_sim                           true
% 2.56/1.02  --prep_unflatten                        true
% 2.56/1.02  --prep_res_sim                          true
% 2.56/1.02  --prep_upred                            true
% 2.56/1.02  --prep_sem_filter                       exhaustive
% 2.56/1.02  --prep_sem_filter_out                   false
% 2.56/1.02  --pred_elim                             true
% 2.56/1.02  --res_sim_input                         true
% 2.56/1.02  --eq_ax_congr_red                       true
% 2.56/1.02  --pure_diseq_elim                       true
% 2.56/1.02  --brand_transform                       false
% 2.56/1.02  --non_eq_to_eq                          false
% 2.56/1.02  --prep_def_merge                        true
% 2.56/1.02  --prep_def_merge_prop_impl              false
% 2.56/1.02  --prep_def_merge_mbd                    true
% 2.56/1.02  --prep_def_merge_tr_red                 false
% 2.56/1.02  --prep_def_merge_tr_cl                  false
% 2.56/1.02  --smt_preprocessing                     true
% 2.56/1.02  --smt_ac_axioms                         fast
% 2.56/1.02  --preprocessed_out                      false
% 2.56/1.02  --preprocessed_stats                    false
% 2.56/1.02  
% 2.56/1.02  ------ Abstraction refinement Options
% 2.56/1.02  
% 2.56/1.02  --abstr_ref                             []
% 2.56/1.02  --abstr_ref_prep                        false
% 2.56/1.02  --abstr_ref_until_sat                   false
% 2.56/1.02  --abstr_ref_sig_restrict                funpre
% 2.56/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/1.02  --abstr_ref_under                       []
% 2.56/1.02  
% 2.56/1.02  ------ SAT Options
% 2.56/1.02  
% 2.56/1.02  --sat_mode                              false
% 2.56/1.02  --sat_fm_restart_options                ""
% 2.56/1.02  --sat_gr_def                            false
% 2.56/1.02  --sat_epr_types                         true
% 2.56/1.02  --sat_non_cyclic_types                  false
% 2.56/1.02  --sat_finite_models                     false
% 2.56/1.02  --sat_fm_lemmas                         false
% 2.56/1.02  --sat_fm_prep                           false
% 2.56/1.02  --sat_fm_uc_incr                        true
% 2.56/1.02  --sat_out_model                         small
% 2.56/1.02  --sat_out_clauses                       false
% 2.56/1.02  
% 2.56/1.02  ------ QBF Options
% 2.56/1.02  
% 2.56/1.02  --qbf_mode                              false
% 2.56/1.02  --qbf_elim_univ                         false
% 2.56/1.02  --qbf_dom_inst                          none
% 2.56/1.02  --qbf_dom_pre_inst                      false
% 2.56/1.02  --qbf_sk_in                             false
% 2.56/1.02  --qbf_pred_elim                         true
% 2.56/1.02  --qbf_split                             512
% 2.56/1.02  
% 2.56/1.02  ------ BMC1 Options
% 2.56/1.02  
% 2.56/1.02  --bmc1_incremental                      false
% 2.56/1.02  --bmc1_axioms                           reachable_all
% 2.56/1.02  --bmc1_min_bound                        0
% 2.56/1.02  --bmc1_max_bound                        -1
% 2.56/1.02  --bmc1_max_bound_default                -1
% 2.56/1.02  --bmc1_symbol_reachability              true
% 2.56/1.02  --bmc1_property_lemmas                  false
% 2.56/1.02  --bmc1_k_induction                      false
% 2.56/1.02  --bmc1_non_equiv_states                 false
% 2.56/1.02  --bmc1_deadlock                         false
% 2.56/1.02  --bmc1_ucm                              false
% 2.56/1.02  --bmc1_add_unsat_core                   none
% 2.56/1.02  --bmc1_unsat_core_children              false
% 2.56/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/1.02  --bmc1_out_stat                         full
% 2.56/1.02  --bmc1_ground_init                      false
% 2.56/1.02  --bmc1_pre_inst_next_state              false
% 2.56/1.02  --bmc1_pre_inst_state                   false
% 2.56/1.02  --bmc1_pre_inst_reach_state             false
% 2.56/1.02  --bmc1_out_unsat_core                   false
% 2.56/1.02  --bmc1_aig_witness_out                  false
% 2.56/1.02  --bmc1_verbose                          false
% 2.56/1.02  --bmc1_dump_clauses_tptp                false
% 2.56/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.56/1.02  --bmc1_dump_file                        -
% 2.56/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.56/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.56/1.02  --bmc1_ucm_extend_mode                  1
% 2.56/1.02  --bmc1_ucm_init_mode                    2
% 2.56/1.02  --bmc1_ucm_cone_mode                    none
% 2.56/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.56/1.02  --bmc1_ucm_relax_model                  4
% 2.56/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.56/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/1.02  --bmc1_ucm_layered_model                none
% 2.56/1.02  --bmc1_ucm_max_lemma_size               10
% 2.56/1.02  
% 2.56/1.02  ------ AIG Options
% 2.56/1.02  
% 2.56/1.02  --aig_mode                              false
% 2.56/1.02  
% 2.56/1.02  ------ Instantiation Options
% 2.56/1.02  
% 2.56/1.02  --instantiation_flag                    true
% 2.56/1.02  --inst_sos_flag                         false
% 2.56/1.02  --inst_sos_phase                        true
% 2.56/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/1.02  --inst_lit_sel_side                     num_symb
% 2.56/1.02  --inst_solver_per_active                1400
% 2.56/1.02  --inst_solver_calls_frac                1.
% 2.56/1.02  --inst_passive_queue_type               priority_queues
% 2.56/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/1.02  --inst_passive_queues_freq              [25;2]
% 2.56/1.02  --inst_dismatching                      true
% 2.56/1.02  --inst_eager_unprocessed_to_passive     true
% 2.56/1.02  --inst_prop_sim_given                   true
% 2.56/1.02  --inst_prop_sim_new                     false
% 2.56/1.02  --inst_subs_new                         false
% 2.56/1.02  --inst_eq_res_simp                      false
% 2.56/1.02  --inst_subs_given                       false
% 2.56/1.02  --inst_orphan_elimination               true
% 2.56/1.02  --inst_learning_loop_flag               true
% 2.56/1.02  --inst_learning_start                   3000
% 2.56/1.02  --inst_learning_factor                  2
% 2.56/1.02  --inst_start_prop_sim_after_learn       3
% 2.56/1.02  --inst_sel_renew                        solver
% 2.56/1.02  --inst_lit_activity_flag                true
% 2.56/1.02  --inst_restr_to_given                   false
% 2.56/1.02  --inst_activity_threshold               500
% 2.56/1.02  --inst_out_proof                        true
% 2.56/1.02  
% 2.56/1.02  ------ Resolution Options
% 2.56/1.02  
% 2.56/1.02  --resolution_flag                       true
% 2.56/1.02  --res_lit_sel                           adaptive
% 2.56/1.02  --res_lit_sel_side                      none
% 2.56/1.02  --res_ordering                          kbo
% 2.56/1.02  --res_to_prop_solver                    active
% 2.56/1.02  --res_prop_simpl_new                    false
% 2.56/1.02  --res_prop_simpl_given                  true
% 2.56/1.02  --res_passive_queue_type                priority_queues
% 2.56/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/1.02  --res_passive_queues_freq               [15;5]
% 2.56/1.02  --res_forward_subs                      full
% 2.56/1.02  --res_backward_subs                     full
% 2.56/1.02  --res_forward_subs_resolution           true
% 2.56/1.02  --res_backward_subs_resolution          true
% 2.56/1.02  --res_orphan_elimination                true
% 2.56/1.02  --res_time_limit                        2.
% 2.56/1.02  --res_out_proof                         true
% 2.56/1.02  
% 2.56/1.02  ------ Superposition Options
% 2.56/1.02  
% 2.56/1.02  --superposition_flag                    true
% 2.56/1.02  --sup_passive_queue_type                priority_queues
% 2.56/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.56/1.02  --demod_completeness_check              fast
% 2.56/1.02  --demod_use_ground                      true
% 2.56/1.02  --sup_to_prop_solver                    passive
% 2.56/1.02  --sup_prop_simpl_new                    true
% 2.56/1.02  --sup_prop_simpl_given                  true
% 2.56/1.02  --sup_fun_splitting                     false
% 2.56/1.02  --sup_smt_interval                      50000
% 2.56/1.02  
% 2.56/1.02  ------ Superposition Simplification Setup
% 2.56/1.02  
% 2.56/1.02  --sup_indices_passive                   []
% 2.56/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.02  --sup_full_bw                           [BwDemod]
% 2.56/1.02  --sup_immed_triv                        [TrivRules]
% 2.56/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.02  --sup_immed_bw_main                     []
% 2.56/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.02  
% 2.56/1.02  ------ Combination Options
% 2.56/1.02  
% 2.56/1.02  --comb_res_mult                         3
% 2.56/1.02  --comb_sup_mult                         2
% 2.56/1.02  --comb_inst_mult                        10
% 2.56/1.02  
% 2.56/1.02  ------ Debug Options
% 2.56/1.02  
% 2.56/1.02  --dbg_backtrace                         false
% 2.56/1.02  --dbg_dump_prop_clauses                 false
% 2.56/1.02  --dbg_dump_prop_clauses_file            -
% 2.56/1.02  --dbg_out_stat                          false
% 2.56/1.02  ------ Parsing...
% 2.56/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.56/1.02  ------ Proving...
% 2.56/1.02  ------ Problem Properties 
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  clauses                                 20
% 2.56/1.02  conjectures                             7
% 2.56/1.02  EPR                                     4
% 2.56/1.02  Horn                                    20
% 2.56/1.02  unary                                   7
% 2.56/1.02  binary                                  3
% 2.56/1.02  lits                                    66
% 2.56/1.02  lits eq                                 14
% 2.56/1.02  fd_pure                                 0
% 2.56/1.02  fd_pseudo                               0
% 2.56/1.02  fd_cond                                 0
% 2.56/1.02  fd_pseudo_cond                          1
% 2.56/1.02  AC symbols                              0
% 2.56/1.02  
% 2.56/1.02  ------ Schedule dynamic 5 is on 
% 2.56/1.02  
% 2.56/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  ------ 
% 2.56/1.02  Current options:
% 2.56/1.02  ------ 
% 2.56/1.02  
% 2.56/1.02  ------ Input Options
% 2.56/1.02  
% 2.56/1.02  --out_options                           all
% 2.56/1.02  --tptp_safe_out                         true
% 2.56/1.02  --problem_path                          ""
% 2.56/1.02  --include_path                          ""
% 2.56/1.02  --clausifier                            res/vclausify_rel
% 2.56/1.02  --clausifier_options                    --mode clausify
% 2.56/1.02  --stdin                                 false
% 2.56/1.02  --stats_out                             all
% 2.56/1.02  
% 2.56/1.02  ------ General Options
% 2.56/1.02  
% 2.56/1.02  --fof                                   false
% 2.56/1.02  --time_out_real                         305.
% 2.56/1.02  --time_out_virtual                      -1.
% 2.56/1.02  --symbol_type_check                     false
% 2.56/1.02  --clausify_out                          false
% 2.56/1.02  --sig_cnt_out                           false
% 2.56/1.02  --trig_cnt_out                          false
% 2.56/1.02  --trig_cnt_out_tolerance                1.
% 2.56/1.02  --trig_cnt_out_sk_spl                   false
% 2.56/1.02  --abstr_cl_out                          false
% 2.56/1.02  
% 2.56/1.02  ------ Global Options
% 2.56/1.02  
% 2.56/1.02  --schedule                              default
% 2.56/1.02  --add_important_lit                     false
% 2.56/1.02  --prop_solver_per_cl                    1000
% 2.56/1.02  --min_unsat_core                        false
% 2.56/1.02  --soft_assumptions                      false
% 2.56/1.02  --soft_lemma_size                       3
% 2.56/1.02  --prop_impl_unit_size                   0
% 2.56/1.02  --prop_impl_unit                        []
% 2.56/1.02  --share_sel_clauses                     true
% 2.56/1.02  --reset_solvers                         false
% 2.56/1.02  --bc_imp_inh                            [conj_cone]
% 2.56/1.02  --conj_cone_tolerance                   3.
% 2.56/1.02  --extra_neg_conj                        none
% 2.56/1.02  --large_theory_mode                     true
% 2.56/1.02  --prolific_symb_bound                   200
% 2.56/1.02  --lt_threshold                          2000
% 2.56/1.02  --clause_weak_htbl                      true
% 2.56/1.02  --gc_record_bc_elim                     false
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing Options
% 2.56/1.02  
% 2.56/1.02  --preprocessing_flag                    true
% 2.56/1.02  --time_out_prep_mult                    0.1
% 2.56/1.02  --splitting_mode                        input
% 2.56/1.02  --splitting_grd                         true
% 2.56/1.02  --splitting_cvd                         false
% 2.56/1.02  --splitting_cvd_svl                     false
% 2.56/1.02  --splitting_nvd                         32
% 2.56/1.02  --sub_typing                            true
% 2.56/1.02  --prep_gs_sim                           true
% 2.56/1.02  --prep_unflatten                        true
% 2.56/1.02  --prep_res_sim                          true
% 2.56/1.02  --prep_upred                            true
% 2.56/1.02  --prep_sem_filter                       exhaustive
% 2.56/1.02  --prep_sem_filter_out                   false
% 2.56/1.02  --pred_elim                             true
% 2.56/1.02  --res_sim_input                         true
% 2.56/1.02  --eq_ax_congr_red                       true
% 2.56/1.02  --pure_diseq_elim                       true
% 2.56/1.02  --brand_transform                       false
% 2.56/1.02  --non_eq_to_eq                          false
% 2.56/1.02  --prep_def_merge                        true
% 2.56/1.02  --prep_def_merge_prop_impl              false
% 2.56/1.02  --prep_def_merge_mbd                    true
% 2.56/1.02  --prep_def_merge_tr_red                 false
% 2.56/1.02  --prep_def_merge_tr_cl                  false
% 2.56/1.02  --smt_preprocessing                     true
% 2.56/1.02  --smt_ac_axioms                         fast
% 2.56/1.02  --preprocessed_out                      false
% 2.56/1.02  --preprocessed_stats                    false
% 2.56/1.02  
% 2.56/1.02  ------ Abstraction refinement Options
% 2.56/1.02  
% 2.56/1.02  --abstr_ref                             []
% 2.56/1.02  --abstr_ref_prep                        false
% 2.56/1.02  --abstr_ref_until_sat                   false
% 2.56/1.02  --abstr_ref_sig_restrict                funpre
% 2.56/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.56/1.02  --abstr_ref_under                       []
% 2.56/1.02  
% 2.56/1.02  ------ SAT Options
% 2.56/1.02  
% 2.56/1.02  --sat_mode                              false
% 2.56/1.02  --sat_fm_restart_options                ""
% 2.56/1.02  --sat_gr_def                            false
% 2.56/1.02  --sat_epr_types                         true
% 2.56/1.02  --sat_non_cyclic_types                  false
% 2.56/1.02  --sat_finite_models                     false
% 2.56/1.02  --sat_fm_lemmas                         false
% 2.56/1.02  --sat_fm_prep                           false
% 2.56/1.02  --sat_fm_uc_incr                        true
% 2.56/1.02  --sat_out_model                         small
% 2.56/1.02  --sat_out_clauses                       false
% 2.56/1.02  
% 2.56/1.02  ------ QBF Options
% 2.56/1.02  
% 2.56/1.02  --qbf_mode                              false
% 2.56/1.02  --qbf_elim_univ                         false
% 2.56/1.02  --qbf_dom_inst                          none
% 2.56/1.02  --qbf_dom_pre_inst                      false
% 2.56/1.02  --qbf_sk_in                             false
% 2.56/1.02  --qbf_pred_elim                         true
% 2.56/1.02  --qbf_split                             512
% 2.56/1.02  
% 2.56/1.02  ------ BMC1 Options
% 2.56/1.02  
% 2.56/1.02  --bmc1_incremental                      false
% 2.56/1.02  --bmc1_axioms                           reachable_all
% 2.56/1.02  --bmc1_min_bound                        0
% 2.56/1.02  --bmc1_max_bound                        -1
% 2.56/1.02  --bmc1_max_bound_default                -1
% 2.56/1.02  --bmc1_symbol_reachability              true
% 2.56/1.02  --bmc1_property_lemmas                  false
% 2.56/1.02  --bmc1_k_induction                      false
% 2.56/1.02  --bmc1_non_equiv_states                 false
% 2.56/1.02  --bmc1_deadlock                         false
% 2.56/1.02  --bmc1_ucm                              false
% 2.56/1.02  --bmc1_add_unsat_core                   none
% 2.56/1.02  --bmc1_unsat_core_children              false
% 2.56/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.56/1.02  --bmc1_out_stat                         full
% 2.56/1.02  --bmc1_ground_init                      false
% 2.56/1.02  --bmc1_pre_inst_next_state              false
% 2.56/1.02  --bmc1_pre_inst_state                   false
% 2.56/1.02  --bmc1_pre_inst_reach_state             false
% 2.56/1.02  --bmc1_out_unsat_core                   false
% 2.56/1.02  --bmc1_aig_witness_out                  false
% 2.56/1.02  --bmc1_verbose                          false
% 2.56/1.02  --bmc1_dump_clauses_tptp                false
% 2.56/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.56/1.02  --bmc1_dump_file                        -
% 2.56/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.56/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.56/1.02  --bmc1_ucm_extend_mode                  1
% 2.56/1.02  --bmc1_ucm_init_mode                    2
% 2.56/1.02  --bmc1_ucm_cone_mode                    none
% 2.56/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.56/1.02  --bmc1_ucm_relax_model                  4
% 2.56/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.56/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.56/1.02  --bmc1_ucm_layered_model                none
% 2.56/1.02  --bmc1_ucm_max_lemma_size               10
% 2.56/1.02  
% 2.56/1.02  ------ AIG Options
% 2.56/1.02  
% 2.56/1.02  --aig_mode                              false
% 2.56/1.02  
% 2.56/1.02  ------ Instantiation Options
% 2.56/1.02  
% 2.56/1.02  --instantiation_flag                    true
% 2.56/1.02  --inst_sos_flag                         false
% 2.56/1.02  --inst_sos_phase                        true
% 2.56/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.56/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.56/1.02  --inst_lit_sel_side                     none
% 2.56/1.02  --inst_solver_per_active                1400
% 2.56/1.02  --inst_solver_calls_frac                1.
% 2.56/1.02  --inst_passive_queue_type               priority_queues
% 2.56/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.56/1.02  --inst_passive_queues_freq              [25;2]
% 2.56/1.02  --inst_dismatching                      true
% 2.56/1.02  --inst_eager_unprocessed_to_passive     true
% 2.56/1.02  --inst_prop_sim_given                   true
% 2.56/1.02  --inst_prop_sim_new                     false
% 2.56/1.02  --inst_subs_new                         false
% 2.56/1.02  --inst_eq_res_simp                      false
% 2.56/1.02  --inst_subs_given                       false
% 2.56/1.02  --inst_orphan_elimination               true
% 2.56/1.02  --inst_learning_loop_flag               true
% 2.56/1.02  --inst_learning_start                   3000
% 2.56/1.02  --inst_learning_factor                  2
% 2.56/1.02  --inst_start_prop_sim_after_learn       3
% 2.56/1.02  --inst_sel_renew                        solver
% 2.56/1.02  --inst_lit_activity_flag                true
% 2.56/1.02  --inst_restr_to_given                   false
% 2.56/1.02  --inst_activity_threshold               500
% 2.56/1.02  --inst_out_proof                        true
% 2.56/1.02  
% 2.56/1.02  ------ Resolution Options
% 2.56/1.02  
% 2.56/1.02  --resolution_flag                       false
% 2.56/1.02  --res_lit_sel                           adaptive
% 2.56/1.02  --res_lit_sel_side                      none
% 2.56/1.02  --res_ordering                          kbo
% 2.56/1.02  --res_to_prop_solver                    active
% 2.56/1.02  --res_prop_simpl_new                    false
% 2.56/1.02  --res_prop_simpl_given                  true
% 2.56/1.02  --res_passive_queue_type                priority_queues
% 2.56/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.56/1.02  --res_passive_queues_freq               [15;5]
% 2.56/1.02  --res_forward_subs                      full
% 2.56/1.02  --res_backward_subs                     full
% 2.56/1.02  --res_forward_subs_resolution           true
% 2.56/1.02  --res_backward_subs_resolution          true
% 2.56/1.02  --res_orphan_elimination                true
% 2.56/1.02  --res_time_limit                        2.
% 2.56/1.02  --res_out_proof                         true
% 2.56/1.02  
% 2.56/1.02  ------ Superposition Options
% 2.56/1.02  
% 2.56/1.02  --superposition_flag                    true
% 2.56/1.02  --sup_passive_queue_type                priority_queues
% 2.56/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.56/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.56/1.02  --demod_completeness_check              fast
% 2.56/1.02  --demod_use_ground                      true
% 2.56/1.02  --sup_to_prop_solver                    passive
% 2.56/1.02  --sup_prop_simpl_new                    true
% 2.56/1.02  --sup_prop_simpl_given                  true
% 2.56/1.02  --sup_fun_splitting                     false
% 2.56/1.02  --sup_smt_interval                      50000
% 2.56/1.02  
% 2.56/1.02  ------ Superposition Simplification Setup
% 2.56/1.02  
% 2.56/1.02  --sup_indices_passive                   []
% 2.56/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.56/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.56/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.02  --sup_full_bw                           [BwDemod]
% 2.56/1.02  --sup_immed_triv                        [TrivRules]
% 2.56/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.56/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.02  --sup_immed_bw_main                     []
% 2.56/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.56/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.56/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.56/1.02  
% 2.56/1.02  ------ Combination Options
% 2.56/1.02  
% 2.56/1.02  --comb_res_mult                         3
% 2.56/1.02  --comb_sup_mult                         2
% 2.56/1.02  --comb_inst_mult                        10
% 2.56/1.02  
% 2.56/1.02  ------ Debug Options
% 2.56/1.02  
% 2.56/1.02  --dbg_backtrace                         false
% 2.56/1.02  --dbg_dump_prop_clauses                 false
% 2.56/1.02  --dbg_dump_prop_clauses_file            -
% 2.56/1.02  --dbg_out_stat                          false
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  ------ Proving...
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  % SZS status Theorem for theBenchmark.p
% 2.56/1.02  
% 2.56/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.56/1.02  
% 2.56/1.02  fof(f14,conjecture,(
% 2.56/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f15,negated_conjecture,(
% 2.56/1.02    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.56/1.02    inference(negated_conjecture,[],[f14])).
% 2.56/1.02  
% 2.56/1.02  fof(f39,plain,(
% 2.56/1.02    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.56/1.02    inference(ennf_transformation,[],[f15])).
% 2.56/1.02  
% 2.56/1.02  fof(f40,plain,(
% 2.56/1.02    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.56/1.02    inference(flattening,[],[f39])).
% 2.56/1.02  
% 2.56/1.02  fof(f45,plain,(
% 2.56/1.02    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.56/1.02    introduced(choice_axiom,[])).
% 2.56/1.02  
% 2.56/1.02  fof(f44,plain,(
% 2.56/1.02    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.56/1.02    introduced(choice_axiom,[])).
% 2.56/1.02  
% 2.56/1.02  fof(f43,plain,(
% 2.56/1.02    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.56/1.02    introduced(choice_axiom,[])).
% 2.56/1.02  
% 2.56/1.02  fof(f46,plain,(
% 2.56/1.02    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.56/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f45,f44,f43])).
% 2.56/1.02  
% 2.56/1.02  fof(f68,plain,(
% 2.56/1.02    l1_struct_0(sK1)),
% 2.56/1.02    inference(cnf_transformation,[],[f46])).
% 2.56/1.02  
% 2.56/1.02  fof(f10,axiom,(
% 2.56/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f32,plain,(
% 2.56/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.56/1.02    inference(ennf_transformation,[],[f10])).
% 2.56/1.02  
% 2.56/1.02  fof(f62,plain,(
% 2.56/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f32])).
% 2.56/1.02  
% 2.56/1.02  fof(f71,plain,(
% 2.56/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.56/1.02    inference(cnf_transformation,[],[f46])).
% 2.56/1.02  
% 2.56/1.02  fof(f66,plain,(
% 2.56/1.02    l1_struct_0(sK0)),
% 2.56/1.02    inference(cnf_transformation,[],[f46])).
% 2.56/1.02  
% 2.56/1.02  fof(f72,plain,(
% 2.56/1.02    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.56/1.02    inference(cnf_transformation,[],[f46])).
% 2.56/1.02  
% 2.56/1.02  fof(f5,axiom,(
% 2.56/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f23,plain,(
% 2.56/1.02    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.02    inference(ennf_transformation,[],[f5])).
% 2.56/1.02  
% 2.56/1.02  fof(f52,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.02    inference(cnf_transformation,[],[f23])).
% 2.56/1.02  
% 2.56/1.02  fof(f6,axiom,(
% 2.56/1.02    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f24,plain,(
% 2.56/1.02    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.56/1.02    inference(ennf_transformation,[],[f6])).
% 2.56/1.02  
% 2.56/1.02  fof(f25,plain,(
% 2.56/1.02    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.56/1.02    inference(flattening,[],[f24])).
% 2.56/1.02  
% 2.56/1.02  fof(f54,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f25])).
% 2.56/1.02  
% 2.56/1.02  fof(f11,axiom,(
% 2.56/1.02    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f33,plain,(
% 2.56/1.02    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.56/1.02    inference(ennf_transformation,[],[f11])).
% 2.56/1.02  
% 2.56/1.02  fof(f34,plain,(
% 2.56/1.02    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.56/1.02    inference(flattening,[],[f33])).
% 2.56/1.02  
% 2.56/1.02  fof(f63,plain,(
% 2.56/1.02    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f34])).
% 2.56/1.02  
% 2.56/1.02  fof(f67,plain,(
% 2.56/1.02    ~v2_struct_0(sK1)),
% 2.56/1.02    inference(cnf_transformation,[],[f46])).
% 2.56/1.02  
% 2.56/1.02  fof(f4,axiom,(
% 2.56/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f16,plain,(
% 2.56/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.56/1.02    inference(pure_predicate_removal,[],[f4])).
% 2.56/1.02  
% 2.56/1.02  fof(f22,plain,(
% 2.56/1.02    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.02    inference(ennf_transformation,[],[f16])).
% 2.56/1.02  
% 2.56/1.02  fof(f51,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.02    inference(cnf_transformation,[],[f22])).
% 2.56/1.02  
% 2.56/1.02  fof(f7,axiom,(
% 2.56/1.02    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f26,plain,(
% 2.56/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.56/1.02    inference(ennf_transformation,[],[f7])).
% 2.56/1.02  
% 2.56/1.02  fof(f27,plain,(
% 2.56/1.02    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.56/1.02    inference(flattening,[],[f26])).
% 2.56/1.02  
% 2.56/1.02  fof(f41,plain,(
% 2.56/1.02    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.56/1.02    inference(nnf_transformation,[],[f27])).
% 2.56/1.02  
% 2.56/1.02  fof(f55,plain,(
% 2.56/1.02    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f41])).
% 2.56/1.02  
% 2.56/1.02  fof(f3,axiom,(
% 2.56/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f21,plain,(
% 2.56/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.56/1.02    inference(ennf_transformation,[],[f3])).
% 2.56/1.02  
% 2.56/1.02  fof(f50,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.56/1.02    inference(cnf_transformation,[],[f21])).
% 2.56/1.02  
% 2.56/1.02  fof(f69,plain,(
% 2.56/1.02    v1_funct_1(sK2)),
% 2.56/1.02    inference(cnf_transformation,[],[f46])).
% 2.56/1.02  
% 2.56/1.02  fof(f70,plain,(
% 2.56/1.02    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.56/1.02    inference(cnf_transformation,[],[f46])).
% 2.56/1.02  
% 2.56/1.02  fof(f13,axiom,(
% 2.56/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f37,plain,(
% 2.56/1.02    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.56/1.02    inference(ennf_transformation,[],[f13])).
% 2.56/1.02  
% 2.56/1.02  fof(f38,plain,(
% 2.56/1.02    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.56/1.02    inference(flattening,[],[f37])).
% 2.56/1.02  
% 2.56/1.02  fof(f65,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f38])).
% 2.56/1.02  
% 2.56/1.02  fof(f12,axiom,(
% 2.56/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f35,plain,(
% 2.56/1.02    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.56/1.02    inference(ennf_transformation,[],[f12])).
% 2.56/1.02  
% 2.56/1.02  fof(f36,plain,(
% 2.56/1.02    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.56/1.02    inference(flattening,[],[f35])).
% 2.56/1.02  
% 2.56/1.02  fof(f64,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f36])).
% 2.56/1.02  
% 2.56/1.02  fof(f73,plain,(
% 2.56/1.02    v2_funct_1(sK2)),
% 2.56/1.02    inference(cnf_transformation,[],[f46])).
% 2.56/1.02  
% 2.56/1.02  fof(f9,axiom,(
% 2.56/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f30,plain,(
% 2.56/1.02    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.56/1.02    inference(ennf_transformation,[],[f9])).
% 2.56/1.02  
% 2.56/1.02  fof(f31,plain,(
% 2.56/1.02    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.56/1.02    inference(flattening,[],[f30])).
% 2.56/1.02  
% 2.56/1.02  fof(f61,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f31])).
% 2.56/1.02  
% 2.56/1.02  fof(f1,axiom,(
% 2.56/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f17,plain,(
% 2.56/1.02    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.56/1.02    inference(ennf_transformation,[],[f1])).
% 2.56/1.02  
% 2.56/1.02  fof(f18,plain,(
% 2.56/1.02    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.56/1.02    inference(flattening,[],[f17])).
% 2.56/1.02  
% 2.56/1.02  fof(f48,plain,(
% 2.56/1.02    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f18])).
% 2.56/1.02  
% 2.56/1.02  fof(f2,axiom,(
% 2.56/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f19,plain,(
% 2.56/1.02    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.56/1.02    inference(ennf_transformation,[],[f2])).
% 2.56/1.02  
% 2.56/1.02  fof(f20,plain,(
% 2.56/1.02    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.56/1.02    inference(flattening,[],[f19])).
% 2.56/1.02  
% 2.56/1.02  fof(f49,plain,(
% 2.56/1.02    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f20])).
% 2.56/1.02  
% 2.56/1.02  fof(f59,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f31])).
% 2.56/1.02  
% 2.56/1.02  fof(f60,plain,(
% 2.56/1.02    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f31])).
% 2.56/1.02  
% 2.56/1.02  fof(f8,axiom,(
% 2.56/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.56/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.56/1.02  
% 2.56/1.02  fof(f28,plain,(
% 2.56/1.02    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.56/1.02    inference(ennf_transformation,[],[f8])).
% 2.56/1.02  
% 2.56/1.02  fof(f29,plain,(
% 2.56/1.02    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.56/1.02    inference(flattening,[],[f28])).
% 2.56/1.02  
% 2.56/1.02  fof(f42,plain,(
% 2.56/1.02    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.56/1.02    inference(nnf_transformation,[],[f29])).
% 2.56/1.02  
% 2.56/1.02  fof(f58,plain,(
% 2.56/1.02    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.56/1.02    inference(cnf_transformation,[],[f42])).
% 2.56/1.02  
% 2.56/1.02  fof(f76,plain,(
% 2.56/1.02    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.56/1.02    inference(equality_resolution,[],[f58])).
% 2.56/1.02  
% 2.56/1.02  fof(f74,plain,(
% 2.56/1.02    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.56/1.02    inference(cnf_transformation,[],[f46])).
% 2.56/1.02  
% 2.56/1.02  cnf(c_25,negated_conjecture,
% 2.56/1.02      ( l1_struct_0(sK1) ),
% 2.56/1.02      inference(cnf_transformation,[],[f68]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_689,negated_conjecture,
% 2.56/1.02      ( l1_struct_0(sK1) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_25]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1103,plain,
% 2.56/1.02      ( l1_struct_0(sK1) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_689]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_15,plain,
% 2.56/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f62]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_697,plain,
% 2.56/1.02      ( ~ l1_struct_0(X0_53) | u1_struct_0(X0_53) = k2_struct_0(X0_53) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_15]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1096,plain,
% 2.56/1.02      ( u1_struct_0(X0_53) = k2_struct_0(X0_53)
% 2.56/1.02      | l1_struct_0(X0_53) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_697]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1376,plain,
% 2.56/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1103,c_1096]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_22,negated_conjecture,
% 2.56/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.56/1.02      inference(cnf_transformation,[],[f71]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_692,negated_conjecture,
% 2.56/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_22]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1100,plain,
% 2.56/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_692]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1571,plain,
% 2.56/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_1376,c_1100]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_27,negated_conjecture,
% 2.56/1.02      ( l1_struct_0(sK0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f66]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_688,negated_conjecture,
% 2.56/1.02      ( l1_struct_0(sK0) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_27]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1104,plain,
% 2.56/1.02      ( l1_struct_0(sK0) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_688]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1377,plain,
% 2.56/1.02      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1104,c_1096]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_21,negated_conjecture,
% 2.56/1.02      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.56/1.02      inference(cnf_transformation,[],[f72]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_693,negated_conjecture,
% 2.56/1.02      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_21]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1573,plain,
% 2.56/1.02      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_1376,c_693]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1643,plain,
% 2.56/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_1377,c_1573]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_5,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_701,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.56/1.02      | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_5]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1092,plain,
% 2.56/1.02      ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_701]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1428,plain,
% 2.56/1.02      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1100,c_1092]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1719,plain,
% 2.56/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_1428,c_1376,c_1377]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1721,plain,
% 2.56/1.02      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_1643,c_1719]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1796,plain,
% 2.56/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_1571,c_1377,c_1721]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_6,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.02      | v1_partfun1(X0,X1)
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | v1_xboole_0(X2)
% 2.56/1.02      | ~ v1_funct_1(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_16,plain,
% 2.56/1.02      ( v2_struct_0(X0)
% 2.56/1.02      | ~ l1_struct_0(X0)
% 2.56/1.02      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.56/1.02      inference(cnf_transformation,[],[f63]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_26,negated_conjecture,
% 2.56/1.02      ( ~ v2_struct_0(sK1) ),
% 2.56/1.02      inference(cnf_transformation,[],[f67]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_301,plain,
% 2.56/1.02      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.56/1.02      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_302,plain,
% 2.56/1.02      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.56/1.02      inference(unflattening,[status(thm)],[c_301]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_43,plain,
% 2.56/1.02      ( v2_struct_0(sK1)
% 2.56/1.02      | ~ l1_struct_0(sK1)
% 2.56/1.02      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_16]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_304,plain,
% 2.56/1.02      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_302,c_26,c_25,c_43]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_314,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.02      | v1_partfun1(X0,X1)
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | ~ v1_funct_1(X0)
% 2.56/1.02      | k2_struct_0(sK1) != X2 ),
% 2.56/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_304]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_315,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.56/1.02      | v1_partfun1(X0,X1)
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.56/1.02      | ~ v1_funct_1(X0) ),
% 2.56/1.02      inference(unflattening,[status(thm)],[c_314]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4,plain,
% 2.56/1.02      ( v4_relat_1(X0,X1)
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.56/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_9,plain,
% 2.56/1.02      ( ~ v1_partfun1(X0,X1)
% 2.56/1.02      | ~ v4_relat_1(X0,X1)
% 2.56/1.02      | ~ v1_relat_1(X0)
% 2.56/1.02      | k1_relat_1(X0) = X1 ),
% 2.56/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_337,plain,
% 2.56/1.02      ( ~ v1_partfun1(X0,X1)
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | ~ v1_relat_1(X0)
% 2.56/1.02      | k1_relat_1(X0) = X1 ),
% 2.56/1.02      inference(resolution,[status(thm)],[c_4,c_9]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | v1_relat_1(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_341,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | ~ v1_partfun1(X0,X1)
% 2.56/1.02      | k1_relat_1(X0) = X1 ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_337,c_9,c_4,c_3]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_342,plain,
% 2.56/1.02      ( ~ v1_partfun1(X0,X1)
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | k1_relat_1(X0) = X1 ),
% 2.56/1.02      inference(renaming,[status(thm)],[c_341]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_381,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.56/1.02      | ~ v1_funct_1(X0)
% 2.56/1.02      | k1_relat_1(X0) = X1 ),
% 2.56/1.02      inference(resolution,[status(thm)],[c_315,c_342]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_687,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0_51,X0_52,k2_struct_0(sK1))
% 2.56/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.56/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1))))
% 2.56/1.02      | ~ v1_funct_1(X0_51)
% 2.56/1.02      | k1_relat_1(X0_51) = X0_52 ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_381]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1105,plain,
% 2.56/1.02      ( k1_relat_1(X0_51) = X0_52
% 2.56/1.02      | v1_funct_2(X0_51,X0_52,k2_struct_0(sK1)) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_687]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2298,plain,
% 2.56/1.02      ( k1_relat_1(X0_51) = X0_52
% 2.56/1.02      | v1_funct_2(X0_51,X0_52,k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_1105,c_1721]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2307,plain,
% 2.56/1.02      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.56/1.02      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_52))) != iProver_top
% 2.56/1.02      | v1_funct_1(sK2) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1796,c_2298]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_24,negated_conjecture,
% 2.56/1.02      ( v1_funct_1(sK2) ),
% 2.56/1.02      inference(cnf_transformation,[],[f69]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_31,plain,
% 2.56/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_23,negated_conjecture,
% 2.56/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.56/1.02      inference(cnf_transformation,[],[f70]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_691,negated_conjecture,
% 2.56/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_23]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1101,plain,
% 2.56/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_691]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1572,plain,
% 2.56/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_1376,c_1101]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1645,plain,
% 2.56/1.02      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_1572,c_1377]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1724,plain,
% 2.56/1.02      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_1721,c_1645]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3129,plain,
% 2.56/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_52))) != iProver_top
% 2.56/1.02      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_2307,c_31,c_1724]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3130,plain,
% 2.56/1.02      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.56/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_52))) != iProver_top ),
% 2.56/1.02      inference(renaming,[status(thm)],[c_3129]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3137,plain,
% 2.56/1.02      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1796,c_3130]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1723,plain,
% 2.56/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_1721,c_1719]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3258,plain,
% 2.56/1.02      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_3137,c_1723]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1725,plain,
% 2.56/1.02      ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_1721,c_1376]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_18,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.56/1.02      | ~ l1_struct_0(X1)
% 2.56/1.02      | ~ l1_struct_0(X2)
% 2.56/1.02      | ~ v1_funct_1(X0)
% 2.56/1.02      | ~ v2_funct_1(X0)
% 2.56/1.02      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 2.56/1.02      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 2.56/1.02      inference(cnf_transformation,[],[f65]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_695,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 2.56/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 2.56/1.02      | ~ l1_struct_0(X1_53)
% 2.56/1.02      | ~ l1_struct_0(X0_53)
% 2.56/1.02      | ~ v1_funct_1(X0_51)
% 2.56/1.02      | ~ v2_funct_1(X0_51)
% 2.56/1.02      | v2_funct_1(k2_tops_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51))
% 2.56/1.02      | k2_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51) != k2_struct_0(X1_53) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1098,plain,
% 2.56/1.02      ( k2_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51) != k2_struct_0(X1_53)
% 2.56/1.02      | v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 2.56/1.02      | l1_struct_0(X0_53) != iProver_top
% 2.56/1.02      | l1_struct_0(X1_53) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_tops_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51)) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_695]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2381,plain,
% 2.56/1.02      ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
% 2.56/1.02      | v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.56/1.02      | l1_struct_0(X0_53) != iProver_top
% 2.56/1.02      | l1_struct_0(sK0) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1377,c_1098]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2444,plain,
% 2.56/1.02      ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
% 2.56/1.02      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.56/1.02      | l1_struct_0(X0_53) != iProver_top
% 2.56/1.02      | l1_struct_0(sK0) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_2381,c_1377]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_28,plain,
% 2.56/1.02      ( l1_struct_0(sK0) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2829,plain,
% 2.56/1.02      ( l1_struct_0(X0_53) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.56/1.02      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.56/1.02      | k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_2444,c_28]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2830,plain,
% 2.56/1.02      ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
% 2.56/1.02      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 2.56/1.02      | l1_struct_0(X0_53) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
% 2.56/1.02      inference(renaming,[status(thm)],[c_2829]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2843,plain,
% 2.56/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_struct_0(sK1)
% 2.56/1.02      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.02      | l1_struct_0(sK1) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0_51)) = iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1725,c_2830]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2851,plain,
% 2.56/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
% 2.56/1.02      | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | l1_struct_0(sK1) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_2843,c_1721,c_1725]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_30,plain,
% 2.56/1.02      ( l1_struct_0(sK1) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3957,plain,
% 2.56/1.02      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_2851,c_30]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3958,plain,
% 2.56/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
% 2.56/1.02      | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
% 2.56/1.02      inference(renaming,[status(thm)],[c_3957]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3963,plain,
% 2.56/1.02      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
% 2.56/1.02      | v1_funct_2(X0_51,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),X0_51)) = iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_3958,c_3137]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4354,plain,
% 2.56/1.02      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_1(sK2) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) = iProver_top
% 2.56/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_3258,c_3963]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_17,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | ~ v1_funct_1(X0)
% 2.56/1.02      | ~ v2_funct_1(X0)
% 2.56/1.02      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.56/1.02      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.56/1.02      inference(cnf_transformation,[],[f64]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_696,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.56/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.56/1.02      | ~ v1_funct_1(X0_51)
% 2.56/1.02      | ~ v2_funct_1(X0_51)
% 2.56/1.02      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.56/1.02      | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1097,plain,
% 2.56/1.02      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.56/1.02      | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51)
% 2.56/1.02      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_696]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2250,plain,
% 2.56/1.02      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.56/1.02      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_1(sK2) != iProver_top
% 2.56/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1723,c_1097]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_20,negated_conjecture,
% 2.56/1.02      ( v2_funct_1(sK2) ),
% 2.56/1.02      inference(cnf_transformation,[],[f73]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_34,plain,
% 2.56/1.02      ( v2_funct_1(sK2) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2553,plain,
% 2.56/1.02      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_2250,c_31,c_34,c_1724,c_1796]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3257,plain,
% 2.56/1.02      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_3137,c_2553]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4360,plain,
% 2.56/1.02      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_1(sK2) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.56/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_4354,c_3257]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3259,plain,
% 2.56/1.02      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_3137,c_1724]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3260,plain,
% 2.56/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_3137,c_1796]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4413,plain,
% 2.56/1.02      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_4360,c_31,c_34,c_3259,c_3260]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_12,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.56/1.02      | ~ v1_funct_1(X0)
% 2.56/1.02      | ~ v2_funct_1(X0)
% 2.56/1.02      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.56/1.02      inference(cnf_transformation,[],[f61]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_700,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.56/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.56/1.02      | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
% 2.56/1.02      | ~ v1_funct_1(X0_51)
% 2.56/1.02      | ~ v2_funct_1(X0_51)
% 2.56/1.02      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_12]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1093,plain,
% 2.56/1.02      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.56/1.02      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.56/1.02      | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_700]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2249,plain,
% 2.56/1.02      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 2.56/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_1(sK2) != iProver_top
% 2.56/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1723,c_1093]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2702,plain,
% 2.56/1.02      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_2249,c_31,c_34,c_1724,c_1796]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2707,plain,
% 2.56/1.02      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_2702,c_1092]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_702,plain,
% 2.56/1.02      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.56/1.02      | v1_relat_1(X0_51) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1091,plain,
% 2.56/1.02      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.56/1.02      | v1_relat_1(X0_51) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_702]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1423,plain,
% 2.56/1.02      ( v1_relat_1(sK2) = iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1100,c_1091]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_0,plain,
% 2.56/1.02      ( ~ v1_relat_1(X0)
% 2.56/1.02      | ~ v1_funct_1(X0)
% 2.56/1.02      | ~ v2_funct_1(X0)
% 2.56/1.02      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.56/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_705,plain,
% 2.56/1.02      ( ~ v1_relat_1(X0_51)
% 2.56/1.02      | ~ v1_funct_1(X0_51)
% 2.56/1.02      | ~ v2_funct_1(X0_51)
% 2.56/1.02      | k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1088,plain,
% 2.56/1.02      ( k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51)
% 2.56/1.02      | v1_relat_1(X0_51) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_705]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1492,plain,
% 2.56/1.02      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.56/1.02      | v1_funct_1(sK2) != iProver_top
% 2.56/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1423,c_1088]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_741,plain,
% 2.56/1.02      ( ~ v1_relat_1(sK2)
% 2.56/1.02      | ~ v1_funct_1(sK2)
% 2.56/1.02      | ~ v2_funct_1(sK2)
% 2.56/1.02      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_705]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1284,plain,
% 2.56/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.56/1.02      | v1_relat_1(sK2) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_702]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2102,plain,
% 2.56/1.02      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_1492,c_24,c_22,c_20,c_741,c_1284]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2712,plain,
% 2.56/1.02      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_2707,c_2102]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3090,plain,
% 2.56/1.02      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.56/1.02      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.56/1.02      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.56/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.56/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_2712,c_1097]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2,plain,
% 2.56/1.02      ( ~ v1_relat_1(X0)
% 2.56/1.02      | ~ v1_funct_1(X0)
% 2.56/1.02      | ~ v2_funct_1(X0)
% 2.56/1.02      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.56/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_703,plain,
% 2.56/1.02      ( ~ v1_relat_1(X0_51)
% 2.56/1.02      | ~ v1_funct_1(X0_51)
% 2.56/1.02      | ~ v2_funct_1(X0_51)
% 2.56/1.02      | k2_funct_1(k2_funct_1(X0_51)) = X0_51 ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1090,plain,
% 2.56/1.02      ( k2_funct_1(k2_funct_1(X0_51)) = X0_51
% 2.56/1.02      | v1_relat_1(X0_51) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_703]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1491,plain,
% 2.56/1.02      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.56/1.02      | v1_funct_1(sK2) != iProver_top
% 2.56/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1423,c_1090]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_747,plain,
% 2.56/1.02      ( ~ v1_relat_1(sK2)
% 2.56/1.02      | ~ v1_funct_1(sK2)
% 2.56/1.02      | ~ v2_funct_1(sK2)
% 2.56/1.02      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_703]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2048,plain,
% 2.56/1.02      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_1491,c_24,c_22,c_20,c_747,c_1284]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3113,plain,
% 2.56/1.02      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 2.56/1.02      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.56/1.02      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 2.56/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 2.56/1.02      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.56/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_3090,c_2048]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_32,plain,
% 2.56/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_33,plain,
% 2.56/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_765,plain,
% 2.56/1.02      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_697]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_14,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | ~ v1_funct_1(X0)
% 2.56/1.02      | v1_funct_1(k2_funct_1(X0))
% 2.56/1.02      | ~ v2_funct_1(X0)
% 2.56/1.02      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.56/1.02      inference(cnf_transformation,[],[f59]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_698,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.56/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.56/1.02      | ~ v1_funct_1(X0_51)
% 2.56/1.02      | v1_funct_1(k2_funct_1(X0_51))
% 2.56/1.02      | ~ v2_funct_1(X0_51)
% 2.56/1.02      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_14]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1313,plain,
% 2.56/1.02      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.56/1.02      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.56/1.02      | v1_funct_1(k2_funct_1(sK2))
% 2.56/1.02      | ~ v1_funct_1(sK2)
% 2.56/1.02      | ~ v2_funct_1(sK2)
% 2.56/1.02      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_698]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1314,plain,
% 2.56/1.02      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.56/1.02      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.56/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.02      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.56/1.02      | v1_funct_1(sK2) != iProver_top
% 2.56/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_1313]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_712,plain,
% 2.56/1.02      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 2.56/1.02      theory(equality) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1335,plain,
% 2.56/1.02      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_52
% 2.56/1.02      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.56/1.02      | u1_struct_0(sK1) != X0_52 ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_712]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1448,plain,
% 2.56/1.02      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.56/1.02      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.56/1.02      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_1335]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_13,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.02      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | ~ v1_funct_1(X0)
% 2.56/1.02      | ~ v2_funct_1(X0)
% 2.56/1.02      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.56/1.02      inference(cnf_transformation,[],[f60]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_699,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.56/1.02      | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52)
% 2.56/1.02      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.56/1.02      | ~ v1_funct_1(X0_51)
% 2.56/1.02      | ~ v2_funct_1(X0_51)
% 2.56/1.02      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_13]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1094,plain,
% 2.56/1.02      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.56/1.02      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.56/1.02      | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52) = iProver_top
% 2.56/1.02      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.56/1.02      | v1_funct_1(X0_51) != iProver_top
% 2.56/1.02      | v2_funct_1(X0_51) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_699]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2251,plain,
% 2.56/1.02      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 2.56/1.02      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_1(sK2) != iProver_top
% 2.56/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_1723,c_1094]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3537,plain,
% 2.56/1.02      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.56/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.56/1.02      inference(global_propositional_subsumption,
% 2.56/1.02                [status(thm)],
% 2.56/1.02                [c_3113,c_25,c_31,c_32,c_33,c_34,c_765,c_693,c_1314,
% 2.56/1.02                 c_1448,c_1724,c_1796,c_2249,c_2251,c_3137]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3541,plain,
% 2.56/1.02      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.56/1.02      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_3537,c_3137]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4418,plain,
% 2.56/1.02      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.56/1.02      inference(superposition,[status(thm)],[c_4413,c_3541]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_10,plain,
% 2.56/1.02      ( r2_funct_2(X0,X1,X2,X2)
% 2.56/1.02      | ~ v1_funct_2(X2,X0,X1)
% 2.56/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.56/1.02      | ~ v1_funct_1(X2) ),
% 2.56/1.02      inference(cnf_transformation,[],[f76]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_19,negated_conjecture,
% 2.56/1.02      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.56/1.02      inference(cnf_transformation,[],[f74]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_474,plain,
% 2.56/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.56/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.56/1.02      | ~ v1_funct_1(X0)
% 2.56/1.02      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.56/1.02      | u1_struct_0(sK1) != X2
% 2.56/1.02      | u1_struct_0(sK0) != X1
% 2.56/1.02      | sK2 != X0 ),
% 2.56/1.02      inference(resolution_lifted,[status(thm)],[c_10,c_19]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_475,plain,
% 2.56/1.02      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.56/1.02      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.56/1.02      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.56/1.02      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.56/1.02      inference(unflattening,[status(thm)],[c_474]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_686,plain,
% 2.56/1.02      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.56/1.02      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.56/1.02      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.56/1.02      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.56/1.02      inference(subtyping,[status(esa)],[c_475]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1106,plain,
% 2.56/1.02      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.56/1.02      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.56/1.02      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.56/1.02      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.56/1.02      inference(predicate_to_equality,[status(thm)],[c_686]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_1570,plain,
% 2.56/1.02      ( k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.56/1.02      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.56/1.02      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.56/1.02      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_1376,c_1106]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2185,plain,
% 2.56/1.02      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.56/1.02      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_1570,c_1377,c_1721]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_2556,plain,
% 2.56/1.02      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.56/1.02      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_2553,c_2185]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_3842,plain,
% 2.56/1.02      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.56/1.02      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.56/1.02      inference(light_normalisation,[status(thm)],[c_2556,c_3137]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_4420,plain,
% 2.56/1.02      ( sK2 != sK2
% 2.56/1.02      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.56/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.56/1.02      | v1_funct_1(sK2) != iProver_top ),
% 2.56/1.02      inference(demodulation,[status(thm)],[c_4418,c_3842]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_707,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.56/1.02  
% 2.56/1.02  cnf(c_736,plain,
% 2.56/1.02      ( sK2 = sK2 ),
% 2.56/1.02      inference(instantiation,[status(thm)],[c_707]) ).
% 2.56/1.02  
% 2.56/1.02  cnf(contradiction,plain,
% 2.56/1.02      ( $false ),
% 2.56/1.02      inference(minisat,[status(thm)],[c_4420,c_3260,c_3259,c_736,c_31]) ).
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 2.56/1.02  
% 2.56/1.02  ------                               Statistics
% 2.56/1.02  
% 2.56/1.02  ------ General
% 2.56/1.02  
% 2.56/1.02  abstr_ref_over_cycles:                  0
% 2.56/1.02  abstr_ref_under_cycles:                 0
% 2.56/1.02  gc_basic_clause_elim:                   0
% 2.56/1.02  forced_gc_time:                         0
% 2.56/1.02  parsing_time:                           0.011
% 2.56/1.02  unif_index_cands_time:                  0.
% 2.56/1.02  unif_index_add_time:                    0.
% 2.56/1.02  orderings_time:                         0.
% 2.56/1.02  out_proof_time:                         0.014
% 2.56/1.02  total_time:                             0.185
% 2.56/1.02  num_of_symbols:                         56
% 2.56/1.02  num_of_terms:                           4079
% 2.56/1.02  
% 2.56/1.02  ------ Preprocessing
% 2.56/1.02  
% 2.56/1.02  num_of_splits:                          0
% 2.56/1.02  num_of_split_atoms:                     0
% 2.56/1.02  num_of_reused_defs:                     0
% 2.56/1.02  num_eq_ax_congr_red:                    8
% 2.56/1.02  num_of_sem_filtered_clauses:            1
% 2.56/1.02  num_of_subtypes:                        5
% 2.56/1.02  monotx_restored_types:                  1
% 2.56/1.02  sat_num_of_epr_types:                   0
% 2.56/1.02  sat_num_of_non_cyclic_types:            0
% 2.56/1.02  sat_guarded_non_collapsed_types:        1
% 2.56/1.02  num_pure_diseq_elim:                    0
% 2.56/1.02  simp_replaced_by:                       0
% 2.56/1.02  res_preprocessed:                       122
% 2.56/1.02  prep_upred:                             0
% 2.56/1.02  prep_unflattend:                        13
% 2.56/1.02  smt_new_axioms:                         0
% 2.56/1.02  pred_elim_cands:                        6
% 2.56/1.02  pred_elim:                              5
% 2.56/1.02  pred_elim_cl:                           7
% 2.56/1.02  pred_elim_cycles:                       8
% 2.56/1.02  merged_defs:                            0
% 2.56/1.02  merged_defs_ncl:                        0
% 2.56/1.02  bin_hyper_res:                          0
% 2.56/1.02  prep_cycles:                            4
% 2.56/1.02  pred_elim_time:                         0.006
% 2.56/1.02  splitting_time:                         0.
% 2.56/1.02  sem_filter_time:                        0.
% 2.56/1.02  monotx_time:                            0.
% 2.56/1.02  subtype_inf_time:                       0.001
% 2.56/1.02  
% 2.56/1.02  ------ Problem properties
% 2.56/1.02  
% 2.56/1.02  clauses:                                20
% 2.56/1.02  conjectures:                            7
% 2.56/1.02  epr:                                    4
% 2.56/1.02  horn:                                   20
% 2.56/1.02  ground:                                 8
% 2.56/1.02  unary:                                  7
% 2.56/1.02  binary:                                 3
% 2.56/1.02  lits:                                   66
% 2.56/1.02  lits_eq:                                14
% 2.56/1.02  fd_pure:                                0
% 2.56/1.02  fd_pseudo:                              0
% 2.56/1.02  fd_cond:                                0
% 2.56/1.02  fd_pseudo_cond:                         1
% 2.56/1.02  ac_symbols:                             0
% 2.56/1.02  
% 2.56/1.02  ------ Propositional Solver
% 2.56/1.02  
% 2.56/1.02  prop_solver_calls:                      30
% 2.56/1.02  prop_fast_solver_calls:                 1172
% 2.56/1.02  smt_solver_calls:                       0
% 2.56/1.02  smt_fast_solver_calls:                  0
% 2.56/1.02  prop_num_of_clauses:                    1503
% 2.56/1.02  prop_preprocess_simplified:             4877
% 2.56/1.02  prop_fo_subsumed:                       46
% 2.56/1.02  prop_solver_time:                       0.
% 2.56/1.02  smt_solver_time:                        0.
% 2.56/1.02  smt_fast_solver_time:                   0.
% 2.56/1.02  prop_fast_solver_time:                  0.
% 2.56/1.02  prop_unsat_core_time:                   0.
% 2.56/1.02  
% 2.56/1.02  ------ QBF
% 2.56/1.02  
% 2.56/1.02  qbf_q_res:                              0
% 2.56/1.02  qbf_num_tautologies:                    0
% 2.56/1.02  qbf_prep_cycles:                        0
% 2.56/1.02  
% 2.56/1.02  ------ BMC1
% 2.56/1.02  
% 2.56/1.02  bmc1_current_bound:                     -1
% 2.56/1.02  bmc1_last_solved_bound:                 -1
% 2.56/1.02  bmc1_unsat_core_size:                   -1
% 2.56/1.02  bmc1_unsat_core_parents_size:           -1
% 2.56/1.02  bmc1_merge_next_fun:                    0
% 2.56/1.02  bmc1_unsat_core_clauses_time:           0.
% 2.56/1.02  
% 2.56/1.02  ------ Instantiation
% 2.56/1.02  
% 2.56/1.02  inst_num_of_clauses:                    535
% 2.56/1.02  inst_num_in_passive:                    14
% 2.56/1.02  inst_num_in_active:                     310
% 2.56/1.02  inst_num_in_unprocessed:                211
% 2.56/1.02  inst_num_of_loops:                      330
% 2.56/1.02  inst_num_of_learning_restarts:          0
% 2.56/1.02  inst_num_moves_active_passive:          15
% 2.56/1.02  inst_lit_activity:                      0
% 2.56/1.02  inst_lit_activity_moves:                0
% 2.56/1.02  inst_num_tautologies:                   0
% 2.56/1.02  inst_num_prop_implied:                  0
% 2.56/1.02  inst_num_existing_simplified:           0
% 2.56/1.02  inst_num_eq_res_simplified:             0
% 2.56/1.02  inst_num_child_elim:                    0
% 2.56/1.02  inst_num_of_dismatching_blockings:      118
% 2.56/1.02  inst_num_of_non_proper_insts:           500
% 2.56/1.02  inst_num_of_duplicates:                 0
% 2.56/1.02  inst_inst_num_from_inst_to_res:         0
% 2.56/1.02  inst_dismatching_checking_time:         0.
% 2.56/1.02  
% 2.56/1.02  ------ Resolution
% 2.56/1.02  
% 2.56/1.02  res_num_of_clauses:                     0
% 2.56/1.02  res_num_in_passive:                     0
% 2.56/1.02  res_num_in_active:                      0
% 2.56/1.02  res_num_of_loops:                       126
% 2.56/1.02  res_forward_subset_subsumed:            58
% 2.56/1.02  res_backward_subset_subsumed:           0
% 2.56/1.02  res_forward_subsumed:                   0
% 2.56/1.02  res_backward_subsumed:                  0
% 2.56/1.02  res_forward_subsumption_resolution:     1
% 2.56/1.02  res_backward_subsumption_resolution:    0
% 2.56/1.02  res_clause_to_clause_subsumption:       92
% 2.56/1.02  res_orphan_elimination:                 0
% 2.56/1.02  res_tautology_del:                      62
% 2.56/1.02  res_num_eq_res_simplified:              0
% 2.56/1.02  res_num_sel_changes:                    0
% 2.56/1.02  res_moves_from_active_to_pass:          0
% 2.56/1.02  
% 2.56/1.02  ------ Superposition
% 2.56/1.02  
% 2.56/1.02  sup_time_total:                         0.
% 2.56/1.02  sup_time_generating:                    0.
% 2.56/1.02  sup_time_sim_full:                      0.
% 2.56/1.02  sup_time_sim_immed:                     0.
% 2.56/1.02  
% 2.56/1.02  sup_num_of_clauses:                     45
% 2.56/1.02  sup_num_in_active:                      42
% 2.56/1.02  sup_num_in_passive:                     3
% 2.56/1.02  sup_num_of_loops:                       65
% 2.56/1.02  sup_fw_superposition:                   23
% 2.56/1.02  sup_bw_superposition:                   35
% 2.56/1.02  sup_immediate_simplified:               38
% 2.56/1.02  sup_given_eliminated:                   0
% 2.56/1.02  comparisons_done:                       0
% 2.56/1.02  comparisons_avoided:                    0
% 2.56/1.02  
% 2.56/1.02  ------ Simplifications
% 2.56/1.02  
% 2.56/1.02  
% 2.56/1.02  sim_fw_subset_subsumed:                 5
% 2.56/1.02  sim_bw_subset_subsumed:                 3
% 2.56/1.02  sim_fw_subsumed:                        10
% 2.56/1.02  sim_bw_subsumed:                        0
% 2.56/1.02  sim_fw_subsumption_res:                 0
% 2.56/1.02  sim_bw_subsumption_res:                 0
% 2.56/1.02  sim_tautology_del:                      0
% 2.56/1.02  sim_eq_tautology_del:                   5
% 2.56/1.02  sim_eq_res_simp:                        0
% 2.56/1.02  sim_fw_demodulated:                     0
% 2.56/1.02  sim_bw_demodulated:                     21
% 2.56/1.02  sim_light_normalised:                   42
% 2.56/1.02  sim_joinable_taut:                      0
% 2.56/1.02  sim_joinable_simp:                      0
% 2.56/1.02  sim_ac_normalised:                      0
% 2.56/1.02  sim_smt_subsumption:                    0
% 2.56/1.02  
%------------------------------------------------------------------------------
