%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:23 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :  189 (9482 expanded)
%              Number of clauses        :  118 (3000 expanded)
%              Number of leaves         :   18 (2668 expanded)
%              Depth                    :   29
%              Number of atoms          :  683 (58633 expanded)
%              Number of equality atoms :  244 (10295 expanded)
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

fof(f73,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f65,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f68,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

fof(f70,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f74,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f26])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f69,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f46])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f8,axiom,(
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
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f72,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f46])).

fof(f10,axiom,(
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
    inference(ennf_transformation,[],[f10])).

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

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f75,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f46])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f51,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f37])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f52,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f49,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f48,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f9,axiom,(
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

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

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
    inference(flattening,[],[f30])).

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
    inference(nnf_transformation,[],[f31])).

fof(f61,plain,(
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

fof(f78,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f61])).

fof(f76,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_607,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1016,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_18,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_348,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_349,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_348])).

cnf(c_602,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_349])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_343,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

cnf(c_344,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_343])).

cnf(c_603,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_344])).

cnf(c_1036,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1016,c_602,c_603])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_613,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1011,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_613])).

cnf(c_1299,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1036,c_1011])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_608,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1033,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_608,c_602,c_603])).

cnf(c_1430,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1299,c_1033])).

cnf(c_1434,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1430,c_1036])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_19,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_330,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_28])).

cnf(c_331,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_42,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_333,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_331,c_28,c_27,c_42])).

cnf(c_355,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_333])).

cnf(c_356,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_7,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_12,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_378,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_7,c_12])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_382,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | k1_relat_1(X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_378,c_12,c_7,c_6])).

cnf(c_383,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relat_1(X0) = X1 ),
    inference(renaming,[status(thm)],[c_382])).

cnf(c_422,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_356,c_383])).

cnf(c_601,plain,
    ( ~ v1_funct_2(X0_51,X0_52,k2_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0_51)
    | k1_relat_1(X0_51) = X0_52 ),
    inference(subtyping,[status(esa)],[c_422])).

cnf(c_1020,plain,
    ( k1_relat_1(X0_51) = X0_52
    | v1_funct_2(X0_51,X0_52,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_601])).

cnf(c_2038,plain,
    ( k1_relat_1(X0_51) = X0_52
    | v1_funct_2(X0_51,X0_52,k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1020,c_1430])).

cnf(c_2047,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_52))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1434,c_2038])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_606,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1017,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_606])).

cnf(c_1030,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1017,c_602,c_603])).

cnf(c_1435,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1430,c_1030])).

cnf(c_2129,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_52))) != iProver_top
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2047,c_33,c_1435])).

cnf(c_2130,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_52))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2129])).

cnf(c_2137,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1434,c_2130])).

cnf(c_1432,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1430,c_1299])).

cnf(c_2141,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2137,c_1432])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_612,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1012,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_2595,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2141,c_1012])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_36,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2140,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2137,c_1434])).

cnf(c_2142,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2137,c_1435])).

cnf(c_2972,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2595,c_33,c_36,c_2140,c_2142])).

cnf(c_2977,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_2972,c_1011])).

cnf(c_614,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1010,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_614])).

cnf(c_1288,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1036,c_1010])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_617,plain,
    ( ~ v1_relat_1(X0_51)
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1007,plain,
    ( k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51)
    | v1_relat_1(X0_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_1651,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_1007])).

cnf(c_667,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_1203,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_614])).

cnf(c_1969,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1651,c_26,c_24,c_22,c_667,c_1203])).

cnf(c_2982,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2977,c_1969])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_610,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1014,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51)
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_3329,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2982,c_1014])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_615,plain,
    ( ~ v1_relat_1(X0_51)
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_funct_1(k2_funct_1(X0_51)) = X0_51 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1009,plain,
    ( k2_funct_1(k2_funct_1(X0_51)) = X0_51
    | v1_relat_1(X0_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_1750,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1288,c_1009])).

cnf(c_673,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_1962,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1750,c_26,c_24,c_22,c_673,c_1203])).

cnf(c_3342,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3329,c_1962])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_620,plain,
    ( ~ v1_relat_1(X0_51)
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | v2_funct_1(k2_funct_1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_657,plain,
    ( v1_relat_1(X0_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_funct_1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_659,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_657])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_619,plain,
    ( ~ v1_relat_1(X0_51)
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_funct_1(X0_51))
    | ~ v2_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_660,plain,
    ( v1_relat_1(X0_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v1_funct_1(k2_funct_1(X0_51)) = iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_662,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_1204,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1203])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f63])).

cnf(c_611,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1013,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_2597,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2141,c_1013])).

cnf(c_3417,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3342,c_33,c_35,c_36,c_659,c_662,c_1204,c_2140,c_2142,c_2595,c_2597])).

cnf(c_13,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_21,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_452,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_21])).

cnf(c_453,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_452])).

cnf(c_600,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_453])).

cnf(c_1021,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_600])).

cnf(c_1149,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1021,c_602,c_603])).

cnf(c_1433,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1430,c_1149])).

cnf(c_2139,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2137,c_1433])).

cnf(c_1909,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1432,c_1014])).

cnf(c_2905,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1909,c_33,c_36,c_1434,c_1435])).

cnf(c_2907,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_2905,c_2137])).

cnf(c_2910,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2139,c_2907])).

cnf(c_3420,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3417,c_2910])).

cnf(c_622,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_653,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_622])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3420,c_2142,c_2140,c_653,c_33])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:33:46 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.33/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.33/0.99  
% 2.33/0.99  ------  iProver source info
% 2.33/0.99  
% 2.33/0.99  git: date: 2020-06-30 10:37:57 +0100
% 2.33/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.33/0.99  git: non_committed_changes: false
% 2.33/0.99  git: last_make_outside_of_git: false
% 2.33/0.99  
% 2.33/0.99  ------ 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options
% 2.33/0.99  
% 2.33/0.99  --out_options                           all
% 2.33/0.99  --tptp_safe_out                         true
% 2.33/0.99  --problem_path                          ""
% 2.33/0.99  --include_path                          ""
% 2.33/0.99  --clausifier                            res/vclausify_rel
% 2.33/0.99  --clausifier_options                    --mode clausify
% 2.33/0.99  --stdin                                 false
% 2.33/0.99  --stats_out                             all
% 2.33/0.99  
% 2.33/0.99  ------ General Options
% 2.33/0.99  
% 2.33/0.99  --fof                                   false
% 2.33/0.99  --time_out_real                         305.
% 2.33/0.99  --time_out_virtual                      -1.
% 2.33/0.99  --symbol_type_check                     false
% 2.33/0.99  --clausify_out                          false
% 2.33/0.99  --sig_cnt_out                           false
% 2.33/0.99  --trig_cnt_out                          false
% 2.33/0.99  --trig_cnt_out_tolerance                1.
% 2.33/0.99  --trig_cnt_out_sk_spl                   false
% 2.33/0.99  --abstr_cl_out                          false
% 2.33/0.99  
% 2.33/0.99  ------ Global Options
% 2.33/0.99  
% 2.33/0.99  --schedule                              default
% 2.33/0.99  --add_important_lit                     false
% 2.33/0.99  --prop_solver_per_cl                    1000
% 2.33/0.99  --min_unsat_core                        false
% 2.33/0.99  --soft_assumptions                      false
% 2.33/0.99  --soft_lemma_size                       3
% 2.33/0.99  --prop_impl_unit_size                   0
% 2.33/0.99  --prop_impl_unit                        []
% 2.33/0.99  --share_sel_clauses                     true
% 2.33/0.99  --reset_solvers                         false
% 2.33/0.99  --bc_imp_inh                            [conj_cone]
% 2.33/0.99  --conj_cone_tolerance                   3.
% 2.33/0.99  --extra_neg_conj                        none
% 2.33/0.99  --large_theory_mode                     true
% 2.33/0.99  --prolific_symb_bound                   200
% 2.33/0.99  --lt_threshold                          2000
% 2.33/0.99  --clause_weak_htbl                      true
% 2.33/0.99  --gc_record_bc_elim                     false
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing Options
% 2.33/0.99  
% 2.33/0.99  --preprocessing_flag                    true
% 2.33/0.99  --time_out_prep_mult                    0.1
% 2.33/0.99  --splitting_mode                        input
% 2.33/0.99  --splitting_grd                         true
% 2.33/0.99  --splitting_cvd                         false
% 2.33/0.99  --splitting_cvd_svl                     false
% 2.33/0.99  --splitting_nvd                         32
% 2.33/0.99  --sub_typing                            true
% 2.33/0.99  --prep_gs_sim                           true
% 2.33/0.99  --prep_unflatten                        true
% 2.33/0.99  --prep_res_sim                          true
% 2.33/0.99  --prep_upred                            true
% 2.33/0.99  --prep_sem_filter                       exhaustive
% 2.33/0.99  --prep_sem_filter_out                   false
% 2.33/0.99  --pred_elim                             true
% 2.33/0.99  --res_sim_input                         true
% 2.33/0.99  --eq_ax_congr_red                       true
% 2.33/0.99  --pure_diseq_elim                       true
% 2.33/0.99  --brand_transform                       false
% 2.33/0.99  --non_eq_to_eq                          false
% 2.33/0.99  --prep_def_merge                        true
% 2.33/0.99  --prep_def_merge_prop_impl              false
% 2.33/0.99  --prep_def_merge_mbd                    true
% 2.33/0.99  --prep_def_merge_tr_red                 false
% 2.33/0.99  --prep_def_merge_tr_cl                  false
% 2.33/0.99  --smt_preprocessing                     true
% 2.33/0.99  --smt_ac_axioms                         fast
% 2.33/0.99  --preprocessed_out                      false
% 2.33/0.99  --preprocessed_stats                    false
% 2.33/0.99  
% 2.33/0.99  ------ Abstraction refinement Options
% 2.33/0.99  
% 2.33/0.99  --abstr_ref                             []
% 2.33/0.99  --abstr_ref_prep                        false
% 2.33/0.99  --abstr_ref_until_sat                   false
% 2.33/0.99  --abstr_ref_sig_restrict                funpre
% 2.33/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.99  --abstr_ref_under                       []
% 2.33/0.99  
% 2.33/0.99  ------ SAT Options
% 2.33/0.99  
% 2.33/0.99  --sat_mode                              false
% 2.33/0.99  --sat_fm_restart_options                ""
% 2.33/0.99  --sat_gr_def                            false
% 2.33/0.99  --sat_epr_types                         true
% 2.33/0.99  --sat_non_cyclic_types                  false
% 2.33/0.99  --sat_finite_models                     false
% 2.33/0.99  --sat_fm_lemmas                         false
% 2.33/0.99  --sat_fm_prep                           false
% 2.33/0.99  --sat_fm_uc_incr                        true
% 2.33/0.99  --sat_out_model                         small
% 2.33/0.99  --sat_out_clauses                       false
% 2.33/0.99  
% 2.33/0.99  ------ QBF Options
% 2.33/0.99  
% 2.33/0.99  --qbf_mode                              false
% 2.33/0.99  --qbf_elim_univ                         false
% 2.33/0.99  --qbf_dom_inst                          none
% 2.33/0.99  --qbf_dom_pre_inst                      false
% 2.33/0.99  --qbf_sk_in                             false
% 2.33/0.99  --qbf_pred_elim                         true
% 2.33/0.99  --qbf_split                             512
% 2.33/0.99  
% 2.33/0.99  ------ BMC1 Options
% 2.33/0.99  
% 2.33/0.99  --bmc1_incremental                      false
% 2.33/0.99  --bmc1_axioms                           reachable_all
% 2.33/0.99  --bmc1_min_bound                        0
% 2.33/0.99  --bmc1_max_bound                        -1
% 2.33/0.99  --bmc1_max_bound_default                -1
% 2.33/0.99  --bmc1_symbol_reachability              true
% 2.33/0.99  --bmc1_property_lemmas                  false
% 2.33/0.99  --bmc1_k_induction                      false
% 2.33/0.99  --bmc1_non_equiv_states                 false
% 2.33/0.99  --bmc1_deadlock                         false
% 2.33/0.99  --bmc1_ucm                              false
% 2.33/0.99  --bmc1_add_unsat_core                   none
% 2.33/0.99  --bmc1_unsat_core_children              false
% 2.33/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.99  --bmc1_out_stat                         full
% 2.33/0.99  --bmc1_ground_init                      false
% 2.33/0.99  --bmc1_pre_inst_next_state              false
% 2.33/0.99  --bmc1_pre_inst_state                   false
% 2.33/0.99  --bmc1_pre_inst_reach_state             false
% 2.33/0.99  --bmc1_out_unsat_core                   false
% 2.33/0.99  --bmc1_aig_witness_out                  false
% 2.33/0.99  --bmc1_verbose                          false
% 2.33/0.99  --bmc1_dump_clauses_tptp                false
% 2.33/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.99  --bmc1_dump_file                        -
% 2.33/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.99  --bmc1_ucm_extend_mode                  1
% 2.33/0.99  --bmc1_ucm_init_mode                    2
% 2.33/0.99  --bmc1_ucm_cone_mode                    none
% 2.33/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.99  --bmc1_ucm_relax_model                  4
% 2.33/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.99  --bmc1_ucm_layered_model                none
% 2.33/0.99  --bmc1_ucm_max_lemma_size               10
% 2.33/0.99  
% 2.33/0.99  ------ AIG Options
% 2.33/0.99  
% 2.33/0.99  --aig_mode                              false
% 2.33/0.99  
% 2.33/0.99  ------ Instantiation Options
% 2.33/0.99  
% 2.33/0.99  --instantiation_flag                    true
% 2.33/0.99  --inst_sos_flag                         false
% 2.33/0.99  --inst_sos_phase                        true
% 2.33/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel_side                     num_symb
% 2.33/0.99  --inst_solver_per_active                1400
% 2.33/0.99  --inst_solver_calls_frac                1.
% 2.33/0.99  --inst_passive_queue_type               priority_queues
% 2.33/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.99  --inst_passive_queues_freq              [25;2]
% 2.33/0.99  --inst_dismatching                      true
% 2.33/0.99  --inst_eager_unprocessed_to_passive     true
% 2.33/0.99  --inst_prop_sim_given                   true
% 2.33/0.99  --inst_prop_sim_new                     false
% 2.33/0.99  --inst_subs_new                         false
% 2.33/0.99  --inst_eq_res_simp                      false
% 2.33/0.99  --inst_subs_given                       false
% 2.33/0.99  --inst_orphan_elimination               true
% 2.33/0.99  --inst_learning_loop_flag               true
% 2.33/0.99  --inst_learning_start                   3000
% 2.33/0.99  --inst_learning_factor                  2
% 2.33/0.99  --inst_start_prop_sim_after_learn       3
% 2.33/0.99  --inst_sel_renew                        solver
% 2.33/0.99  --inst_lit_activity_flag                true
% 2.33/0.99  --inst_restr_to_given                   false
% 2.33/0.99  --inst_activity_threshold               500
% 2.33/0.99  --inst_out_proof                        true
% 2.33/0.99  
% 2.33/0.99  ------ Resolution Options
% 2.33/0.99  
% 2.33/0.99  --resolution_flag                       true
% 2.33/0.99  --res_lit_sel                           adaptive
% 2.33/0.99  --res_lit_sel_side                      none
% 2.33/0.99  --res_ordering                          kbo
% 2.33/0.99  --res_to_prop_solver                    active
% 2.33/0.99  --res_prop_simpl_new                    false
% 2.33/0.99  --res_prop_simpl_given                  true
% 2.33/0.99  --res_passive_queue_type                priority_queues
% 2.33/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.99  --res_passive_queues_freq               [15;5]
% 2.33/0.99  --res_forward_subs                      full
% 2.33/0.99  --res_backward_subs                     full
% 2.33/0.99  --res_forward_subs_resolution           true
% 2.33/0.99  --res_backward_subs_resolution          true
% 2.33/0.99  --res_orphan_elimination                true
% 2.33/0.99  --res_time_limit                        2.
% 2.33/0.99  --res_out_proof                         true
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Options
% 2.33/0.99  
% 2.33/0.99  --superposition_flag                    true
% 2.33/0.99  --sup_passive_queue_type                priority_queues
% 2.33/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.99  --demod_completeness_check              fast
% 2.33/0.99  --demod_use_ground                      true
% 2.33/0.99  --sup_to_prop_solver                    passive
% 2.33/0.99  --sup_prop_simpl_new                    true
% 2.33/0.99  --sup_prop_simpl_given                  true
% 2.33/0.99  --sup_fun_splitting                     false
% 2.33/0.99  --sup_smt_interval                      50000
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Simplification Setup
% 2.33/0.99  
% 2.33/0.99  --sup_indices_passive                   []
% 2.33/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_full_bw                           [BwDemod]
% 2.33/0.99  --sup_immed_triv                        [TrivRules]
% 2.33/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_immed_bw_main                     []
% 2.33/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  
% 2.33/0.99  ------ Combination Options
% 2.33/0.99  
% 2.33/0.99  --comb_res_mult                         3
% 2.33/0.99  --comb_sup_mult                         2
% 2.33/0.99  --comb_inst_mult                        10
% 2.33/0.99  
% 2.33/0.99  ------ Debug Options
% 2.33/0.99  
% 2.33/0.99  --dbg_backtrace                         false
% 2.33/0.99  --dbg_dump_prop_clauses                 false
% 2.33/0.99  --dbg_dump_prop_clauses_file            -
% 2.33/0.99  --dbg_out_stat                          false
% 2.33/0.99  ------ Parsing...
% 2.33/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.33/0.99  ------ Proving...
% 2.33/0.99  ------ Problem Properties 
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  clauses                                 21
% 2.33/0.99  conjectures                             5
% 2.33/0.99  EPR                                     2
% 2.33/0.99  Horn                                    21
% 2.33/0.99  unary                                   7
% 2.33/0.99  binary                                  2
% 2.33/0.99  lits                                    66
% 2.33/0.99  lits eq                                 13
% 2.33/0.99  fd_pure                                 0
% 2.33/0.99  fd_pseudo                               0
% 2.33/0.99  fd_cond                                 0
% 2.33/0.99  fd_pseudo_cond                          1
% 2.33/0.99  AC symbols                              0
% 2.33/0.99  
% 2.33/0.99  ------ Schedule dynamic 5 is on 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  ------ 
% 2.33/0.99  Current options:
% 2.33/0.99  ------ 
% 2.33/0.99  
% 2.33/0.99  ------ Input Options
% 2.33/0.99  
% 2.33/0.99  --out_options                           all
% 2.33/0.99  --tptp_safe_out                         true
% 2.33/0.99  --problem_path                          ""
% 2.33/0.99  --include_path                          ""
% 2.33/0.99  --clausifier                            res/vclausify_rel
% 2.33/0.99  --clausifier_options                    --mode clausify
% 2.33/0.99  --stdin                                 false
% 2.33/0.99  --stats_out                             all
% 2.33/0.99  
% 2.33/0.99  ------ General Options
% 2.33/0.99  
% 2.33/0.99  --fof                                   false
% 2.33/0.99  --time_out_real                         305.
% 2.33/0.99  --time_out_virtual                      -1.
% 2.33/0.99  --symbol_type_check                     false
% 2.33/0.99  --clausify_out                          false
% 2.33/0.99  --sig_cnt_out                           false
% 2.33/0.99  --trig_cnt_out                          false
% 2.33/0.99  --trig_cnt_out_tolerance                1.
% 2.33/0.99  --trig_cnt_out_sk_spl                   false
% 2.33/0.99  --abstr_cl_out                          false
% 2.33/0.99  
% 2.33/0.99  ------ Global Options
% 2.33/0.99  
% 2.33/0.99  --schedule                              default
% 2.33/0.99  --add_important_lit                     false
% 2.33/0.99  --prop_solver_per_cl                    1000
% 2.33/0.99  --min_unsat_core                        false
% 2.33/0.99  --soft_assumptions                      false
% 2.33/0.99  --soft_lemma_size                       3
% 2.33/0.99  --prop_impl_unit_size                   0
% 2.33/0.99  --prop_impl_unit                        []
% 2.33/0.99  --share_sel_clauses                     true
% 2.33/0.99  --reset_solvers                         false
% 2.33/0.99  --bc_imp_inh                            [conj_cone]
% 2.33/0.99  --conj_cone_tolerance                   3.
% 2.33/0.99  --extra_neg_conj                        none
% 2.33/0.99  --large_theory_mode                     true
% 2.33/0.99  --prolific_symb_bound                   200
% 2.33/0.99  --lt_threshold                          2000
% 2.33/0.99  --clause_weak_htbl                      true
% 2.33/0.99  --gc_record_bc_elim                     false
% 2.33/0.99  
% 2.33/0.99  ------ Preprocessing Options
% 2.33/0.99  
% 2.33/0.99  --preprocessing_flag                    true
% 2.33/0.99  --time_out_prep_mult                    0.1
% 2.33/0.99  --splitting_mode                        input
% 2.33/0.99  --splitting_grd                         true
% 2.33/0.99  --splitting_cvd                         false
% 2.33/0.99  --splitting_cvd_svl                     false
% 2.33/0.99  --splitting_nvd                         32
% 2.33/0.99  --sub_typing                            true
% 2.33/0.99  --prep_gs_sim                           true
% 2.33/0.99  --prep_unflatten                        true
% 2.33/0.99  --prep_res_sim                          true
% 2.33/0.99  --prep_upred                            true
% 2.33/0.99  --prep_sem_filter                       exhaustive
% 2.33/0.99  --prep_sem_filter_out                   false
% 2.33/0.99  --pred_elim                             true
% 2.33/0.99  --res_sim_input                         true
% 2.33/0.99  --eq_ax_congr_red                       true
% 2.33/0.99  --pure_diseq_elim                       true
% 2.33/0.99  --brand_transform                       false
% 2.33/0.99  --non_eq_to_eq                          false
% 2.33/0.99  --prep_def_merge                        true
% 2.33/0.99  --prep_def_merge_prop_impl              false
% 2.33/0.99  --prep_def_merge_mbd                    true
% 2.33/0.99  --prep_def_merge_tr_red                 false
% 2.33/0.99  --prep_def_merge_tr_cl                  false
% 2.33/0.99  --smt_preprocessing                     true
% 2.33/0.99  --smt_ac_axioms                         fast
% 2.33/0.99  --preprocessed_out                      false
% 2.33/0.99  --preprocessed_stats                    false
% 2.33/0.99  
% 2.33/0.99  ------ Abstraction refinement Options
% 2.33/0.99  
% 2.33/0.99  --abstr_ref                             []
% 2.33/0.99  --abstr_ref_prep                        false
% 2.33/0.99  --abstr_ref_until_sat                   false
% 2.33/0.99  --abstr_ref_sig_restrict                funpre
% 2.33/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 2.33/0.99  --abstr_ref_under                       []
% 2.33/0.99  
% 2.33/0.99  ------ SAT Options
% 2.33/0.99  
% 2.33/0.99  --sat_mode                              false
% 2.33/0.99  --sat_fm_restart_options                ""
% 2.33/0.99  --sat_gr_def                            false
% 2.33/0.99  --sat_epr_types                         true
% 2.33/0.99  --sat_non_cyclic_types                  false
% 2.33/0.99  --sat_finite_models                     false
% 2.33/0.99  --sat_fm_lemmas                         false
% 2.33/0.99  --sat_fm_prep                           false
% 2.33/0.99  --sat_fm_uc_incr                        true
% 2.33/0.99  --sat_out_model                         small
% 2.33/0.99  --sat_out_clauses                       false
% 2.33/0.99  
% 2.33/0.99  ------ QBF Options
% 2.33/0.99  
% 2.33/0.99  --qbf_mode                              false
% 2.33/0.99  --qbf_elim_univ                         false
% 2.33/0.99  --qbf_dom_inst                          none
% 2.33/0.99  --qbf_dom_pre_inst                      false
% 2.33/0.99  --qbf_sk_in                             false
% 2.33/0.99  --qbf_pred_elim                         true
% 2.33/0.99  --qbf_split                             512
% 2.33/0.99  
% 2.33/0.99  ------ BMC1 Options
% 2.33/0.99  
% 2.33/0.99  --bmc1_incremental                      false
% 2.33/0.99  --bmc1_axioms                           reachable_all
% 2.33/0.99  --bmc1_min_bound                        0
% 2.33/0.99  --bmc1_max_bound                        -1
% 2.33/0.99  --bmc1_max_bound_default                -1
% 2.33/0.99  --bmc1_symbol_reachability              true
% 2.33/0.99  --bmc1_property_lemmas                  false
% 2.33/0.99  --bmc1_k_induction                      false
% 2.33/0.99  --bmc1_non_equiv_states                 false
% 2.33/0.99  --bmc1_deadlock                         false
% 2.33/0.99  --bmc1_ucm                              false
% 2.33/0.99  --bmc1_add_unsat_core                   none
% 2.33/0.99  --bmc1_unsat_core_children              false
% 2.33/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 2.33/0.99  --bmc1_out_stat                         full
% 2.33/0.99  --bmc1_ground_init                      false
% 2.33/0.99  --bmc1_pre_inst_next_state              false
% 2.33/0.99  --bmc1_pre_inst_state                   false
% 2.33/0.99  --bmc1_pre_inst_reach_state             false
% 2.33/0.99  --bmc1_out_unsat_core                   false
% 2.33/0.99  --bmc1_aig_witness_out                  false
% 2.33/0.99  --bmc1_verbose                          false
% 2.33/0.99  --bmc1_dump_clauses_tptp                false
% 2.33/0.99  --bmc1_dump_unsat_core_tptp             false
% 2.33/0.99  --bmc1_dump_file                        -
% 2.33/0.99  --bmc1_ucm_expand_uc_limit              128
% 2.33/0.99  --bmc1_ucm_n_expand_iterations          6
% 2.33/0.99  --bmc1_ucm_extend_mode                  1
% 2.33/0.99  --bmc1_ucm_init_mode                    2
% 2.33/0.99  --bmc1_ucm_cone_mode                    none
% 2.33/0.99  --bmc1_ucm_reduced_relation_type        0
% 2.33/0.99  --bmc1_ucm_relax_model                  4
% 2.33/0.99  --bmc1_ucm_full_tr_after_sat            true
% 2.33/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 2.33/0.99  --bmc1_ucm_layered_model                none
% 2.33/0.99  --bmc1_ucm_max_lemma_size               10
% 2.33/0.99  
% 2.33/0.99  ------ AIG Options
% 2.33/0.99  
% 2.33/0.99  --aig_mode                              false
% 2.33/0.99  
% 2.33/0.99  ------ Instantiation Options
% 2.33/0.99  
% 2.33/0.99  --instantiation_flag                    true
% 2.33/0.99  --inst_sos_flag                         false
% 2.33/0.99  --inst_sos_phase                        true
% 2.33/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.33/0.99  --inst_lit_sel_side                     none
% 2.33/0.99  --inst_solver_per_active                1400
% 2.33/0.99  --inst_solver_calls_frac                1.
% 2.33/0.99  --inst_passive_queue_type               priority_queues
% 2.33/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.33/0.99  --inst_passive_queues_freq              [25;2]
% 2.33/0.99  --inst_dismatching                      true
% 2.33/0.99  --inst_eager_unprocessed_to_passive     true
% 2.33/0.99  --inst_prop_sim_given                   true
% 2.33/0.99  --inst_prop_sim_new                     false
% 2.33/0.99  --inst_subs_new                         false
% 2.33/0.99  --inst_eq_res_simp                      false
% 2.33/0.99  --inst_subs_given                       false
% 2.33/0.99  --inst_orphan_elimination               true
% 2.33/0.99  --inst_learning_loop_flag               true
% 2.33/0.99  --inst_learning_start                   3000
% 2.33/0.99  --inst_learning_factor                  2
% 2.33/0.99  --inst_start_prop_sim_after_learn       3
% 2.33/0.99  --inst_sel_renew                        solver
% 2.33/0.99  --inst_lit_activity_flag                true
% 2.33/0.99  --inst_restr_to_given                   false
% 2.33/0.99  --inst_activity_threshold               500
% 2.33/0.99  --inst_out_proof                        true
% 2.33/0.99  
% 2.33/0.99  ------ Resolution Options
% 2.33/0.99  
% 2.33/0.99  --resolution_flag                       false
% 2.33/0.99  --res_lit_sel                           adaptive
% 2.33/0.99  --res_lit_sel_side                      none
% 2.33/0.99  --res_ordering                          kbo
% 2.33/0.99  --res_to_prop_solver                    active
% 2.33/0.99  --res_prop_simpl_new                    false
% 2.33/0.99  --res_prop_simpl_given                  true
% 2.33/0.99  --res_passive_queue_type                priority_queues
% 2.33/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.33/0.99  --res_passive_queues_freq               [15;5]
% 2.33/0.99  --res_forward_subs                      full
% 2.33/0.99  --res_backward_subs                     full
% 2.33/0.99  --res_forward_subs_resolution           true
% 2.33/0.99  --res_backward_subs_resolution          true
% 2.33/0.99  --res_orphan_elimination                true
% 2.33/0.99  --res_time_limit                        2.
% 2.33/0.99  --res_out_proof                         true
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Options
% 2.33/0.99  
% 2.33/0.99  --superposition_flag                    true
% 2.33/0.99  --sup_passive_queue_type                priority_queues
% 2.33/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.33/0.99  --sup_passive_queues_freq               [8;1;4]
% 2.33/0.99  --demod_completeness_check              fast
% 2.33/0.99  --demod_use_ground                      true
% 2.33/0.99  --sup_to_prop_solver                    passive
% 2.33/0.99  --sup_prop_simpl_new                    true
% 2.33/0.99  --sup_prop_simpl_given                  true
% 2.33/0.99  --sup_fun_splitting                     false
% 2.33/0.99  --sup_smt_interval                      50000
% 2.33/0.99  
% 2.33/0.99  ------ Superposition Simplification Setup
% 2.33/0.99  
% 2.33/0.99  --sup_indices_passive                   []
% 2.33/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.33/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 2.33/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_full_bw                           [BwDemod]
% 2.33/0.99  --sup_immed_triv                        [TrivRules]
% 2.33/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.33/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_immed_bw_main                     []
% 2.33/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 2.33/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.33/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.33/0.99  
% 2.33/0.99  ------ Combination Options
% 2.33/0.99  
% 2.33/0.99  --comb_res_mult                         3
% 2.33/0.99  --comb_sup_mult                         2
% 2.33/0.99  --comb_inst_mult                        10
% 2.33/0.99  
% 2.33/0.99  ------ Debug Options
% 2.33/0.99  
% 2.33/0.99  --dbg_backtrace                         false
% 2.33/0.99  --dbg_dump_prop_clauses                 false
% 2.33/0.99  --dbg_dump_prop_clauses_file            -
% 2.33/0.99  --dbg_out_stat                          false
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  ------ Proving...
% 2.33/0.99  
% 2.33/0.99  
% 2.33/0.99  % SZS status Theorem for theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 2.33/0.99  
% 2.33/0.99  fof(f14,conjecture,(
% 2.33/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f15,negated_conjecture,(
% 2.33/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.33/0.99    inference(negated_conjecture,[],[f14])).
% 2.33/0.99  
% 2.33/0.99  fof(f39,plain,(
% 2.33/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.33/0.99    inference(ennf_transformation,[],[f15])).
% 2.33/0.99  
% 2.33/0.99  fof(f40,plain,(
% 2.33/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.33/0.99    inference(flattening,[],[f39])).
% 2.33/0.99  
% 2.33/0.99  fof(f45,plain,(
% 2.33/0.99    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.33/0.99    introduced(choice_axiom,[])).
% 2.33/0.99  
% 2.33/0.99  fof(f44,plain,(
% 2.33/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.33/0.99    introduced(choice_axiom,[])).
% 2.33/0.99  
% 2.33/0.99  fof(f43,plain,(
% 2.33/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.33/0.99    introduced(choice_axiom,[])).
% 2.33/0.99  
% 2.33/0.99  fof(f46,plain,(
% 2.33/0.99    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.33/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f40,f45,f44,f43])).
% 2.33/0.99  
% 2.33/0.99  fof(f73,plain,(
% 2.33/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.33/0.99    inference(cnf_transformation,[],[f46])).
% 2.33/0.99  
% 2.33/0.99  fof(f11,axiom,(
% 2.33/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f34,plain,(
% 2.33/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.33/0.99    inference(ennf_transformation,[],[f11])).
% 2.33/0.99  
% 2.33/0.99  fof(f65,plain,(
% 2.33/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f34])).
% 2.33/0.99  
% 2.33/0.99  fof(f68,plain,(
% 2.33/0.99    l1_struct_0(sK0)),
% 2.33/0.99    inference(cnf_transformation,[],[f46])).
% 2.33/0.99  
% 2.33/0.99  fof(f70,plain,(
% 2.33/0.99    l1_struct_0(sK1)),
% 2.33/0.99    inference(cnf_transformation,[],[f46])).
% 2.33/0.99  
% 2.33/0.99  fof(f6,axiom,(
% 2.33/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f25,plain,(
% 2.33/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.99    inference(ennf_transformation,[],[f6])).
% 2.33/0.99  
% 2.33/0.99  fof(f55,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.99    inference(cnf_transformation,[],[f25])).
% 2.33/0.99  
% 2.33/0.99  fof(f74,plain,(
% 2.33/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.33/0.99    inference(cnf_transformation,[],[f46])).
% 2.33/0.99  
% 2.33/0.99  fof(f7,axiom,(
% 2.33/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f26,plain,(
% 2.33/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.33/0.99    inference(ennf_transformation,[],[f7])).
% 2.33/0.99  
% 2.33/0.99  fof(f27,plain,(
% 2.33/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.33/0.99    inference(flattening,[],[f26])).
% 2.33/0.99  
% 2.33/0.99  fof(f57,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f27])).
% 2.33/0.99  
% 2.33/0.99  fof(f12,axiom,(
% 2.33/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f35,plain,(
% 2.33/0.99    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.33/0.99    inference(ennf_transformation,[],[f12])).
% 2.33/0.99  
% 2.33/0.99  fof(f36,plain,(
% 2.33/0.99    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.33/0.99    inference(flattening,[],[f35])).
% 2.33/0.99  
% 2.33/0.99  fof(f66,plain,(
% 2.33/0.99    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f36])).
% 2.33/0.99  
% 2.33/0.99  fof(f69,plain,(
% 2.33/0.99    ~v2_struct_0(sK1)),
% 2.33/0.99    inference(cnf_transformation,[],[f46])).
% 2.33/0.99  
% 2.33/0.99  fof(f5,axiom,(
% 2.33/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f16,plain,(
% 2.33/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.33/0.99    inference(pure_predicate_removal,[],[f5])).
% 2.33/0.99  
% 2.33/0.99  fof(f24,plain,(
% 2.33/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.99    inference(ennf_transformation,[],[f16])).
% 2.33/0.99  
% 2.33/0.99  fof(f54,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.99    inference(cnf_transformation,[],[f24])).
% 2.33/0.99  
% 2.33/0.99  fof(f8,axiom,(
% 2.33/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f28,plain,(
% 2.33/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.33/0.99    inference(ennf_transformation,[],[f8])).
% 2.33/0.99  
% 2.33/0.99  fof(f29,plain,(
% 2.33/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.33/0.99    inference(flattening,[],[f28])).
% 2.33/0.99  
% 2.33/0.99  fof(f41,plain,(
% 2.33/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.33/0.99    inference(nnf_transformation,[],[f29])).
% 2.33/0.99  
% 2.33/0.99  fof(f58,plain,(
% 2.33/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f41])).
% 2.33/0.99  
% 2.33/0.99  fof(f4,axiom,(
% 2.33/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f23,plain,(
% 2.33/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.33/0.99    inference(ennf_transformation,[],[f4])).
% 2.33/0.99  
% 2.33/0.99  fof(f53,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.33/0.99    inference(cnf_transformation,[],[f23])).
% 2.33/0.99  
% 2.33/0.99  fof(f71,plain,(
% 2.33/0.99    v1_funct_1(sK2)),
% 2.33/0.99    inference(cnf_transformation,[],[f46])).
% 2.33/0.99  
% 2.33/0.99  fof(f72,plain,(
% 2.33/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.33/0.99    inference(cnf_transformation,[],[f46])).
% 2.33/0.99  
% 2.33/0.99  fof(f10,axiom,(
% 2.33/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f32,plain,(
% 2.33/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.33/0.99    inference(ennf_transformation,[],[f10])).
% 2.33/0.99  
% 2.33/0.99  fof(f33,plain,(
% 2.33/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.33/0.99    inference(flattening,[],[f32])).
% 2.33/0.99  
% 2.33/0.99  fof(f64,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f75,plain,(
% 2.33/0.99    v2_funct_1(sK2)),
% 2.33/0.99    inference(cnf_transformation,[],[f46])).
% 2.33/0.99  
% 2.33/0.99  fof(f2,axiom,(
% 2.33/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f19,plain,(
% 2.33/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.99    inference(ennf_transformation,[],[f2])).
% 2.33/0.99  
% 2.33/0.99  fof(f20,plain,(
% 2.33/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.99    inference(flattening,[],[f19])).
% 2.33/0.99  
% 2.33/0.99  fof(f51,plain,(
% 2.33/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f20])).
% 2.33/0.99  
% 2.33/0.99  fof(f13,axiom,(
% 2.33/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f37,plain,(
% 2.33/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.33/0.99    inference(ennf_transformation,[],[f13])).
% 2.33/0.99  
% 2.33/0.99  fof(f38,plain,(
% 2.33/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.33/0.99    inference(flattening,[],[f37])).
% 2.33/0.99  
% 2.33/0.99  fof(f67,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f38])).
% 2.33/0.99  
% 2.33/0.99  fof(f3,axiom,(
% 2.33/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f21,plain,(
% 2.33/0.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.99    inference(ennf_transformation,[],[f3])).
% 2.33/0.99  
% 2.33/0.99  fof(f22,plain,(
% 2.33/0.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.99    inference(flattening,[],[f21])).
% 2.33/0.99  
% 2.33/0.99  fof(f52,plain,(
% 2.33/0.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f22])).
% 2.33/0.99  
% 2.33/0.99  fof(f1,axiom,(
% 2.33/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f17,plain,(
% 2.33/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.33/0.99    inference(ennf_transformation,[],[f1])).
% 2.33/0.99  
% 2.33/0.99  fof(f18,plain,(
% 2.33/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.33/0.99    inference(flattening,[],[f17])).
% 2.33/0.99  
% 2.33/0.99  fof(f49,plain,(
% 2.33/0.99    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f18])).
% 2.33/0.99  
% 2.33/0.99  fof(f48,plain,(
% 2.33/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f18])).
% 2.33/0.99  
% 2.33/0.99  fof(f63,plain,(
% 2.33/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f33])).
% 2.33/0.99  
% 2.33/0.99  fof(f9,axiom,(
% 2.33/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.33/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.33/0.99  
% 2.33/0.99  fof(f30,plain,(
% 2.33/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.33/0.99    inference(ennf_transformation,[],[f9])).
% 2.33/0.99  
% 2.33/0.99  fof(f31,plain,(
% 2.33/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.33/0.99    inference(flattening,[],[f30])).
% 2.33/0.99  
% 2.33/0.99  fof(f42,plain,(
% 2.33/0.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.33/0.99    inference(nnf_transformation,[],[f31])).
% 2.33/0.99  
% 2.33/0.99  fof(f61,plain,(
% 2.33/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.33/0.99    inference(cnf_transformation,[],[f42])).
% 2.33/0.99  
% 2.33/0.99  fof(f78,plain,(
% 2.33/0.99    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.33/0.99    inference(equality_resolution,[],[f61])).
% 2.33/0.99  
% 2.33/0.99  fof(f76,plain,(
% 2.33/0.99    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.33/0.99    inference(cnf_transformation,[],[f46])).
% 2.33/0.99  
% 2.33/0.99  cnf(c_24,negated_conjecture,
% 2.33/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.33/0.99      inference(cnf_transformation,[],[f73]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_607,negated_conjecture,
% 2.33/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_24]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1016,plain,
% 2.33/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_18,plain,
% 2.33/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f65]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_29,negated_conjecture,
% 2.33/0.99      ( l1_struct_0(sK0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f68]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_348,plain,
% 2.33/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_349,plain,
% 2.33/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_348]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_602,plain,
% 2.33/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_349]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_27,negated_conjecture,
% 2.33/0.99      ( l1_struct_0(sK1) ),
% 2.33/0.99      inference(cnf_transformation,[],[f70]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_343,plain,
% 2.33/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_344,plain,
% 2.33/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_343]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_603,plain,
% 2.33/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_344]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1036,plain,
% 2.33/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.33/0.99      inference(light_normalisation,[status(thm)],[c_1016,c_602,c_603]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_8,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f55]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_613,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.33/0.99      | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_8]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1011,plain,
% 2.33/0.99      ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
% 2.33/0.99      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 2.33/0.99      inference(predicate_to_equality,[status(thm)],[c_613]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1299,plain,
% 2.33/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.33/0.99      inference(superposition,[status(thm)],[c_1036,c_1011]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_23,negated_conjecture,
% 2.33/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.33/0.99      inference(cnf_transformation,[],[f74]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_608,negated_conjecture,
% 2.33/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.33/0.99      inference(subtyping,[status(esa)],[c_23]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1033,plain,
% 2.33/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.33/0.99      inference(light_normalisation,[status(thm)],[c_608,c_602,c_603]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1430,plain,
% 2.33/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.33/0.99      inference(demodulation,[status(thm)],[c_1299,c_1033]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_1434,plain,
% 2.33/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 2.33/0.99      inference(demodulation,[status(thm)],[c_1430,c_1036]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_9,plain,
% 2.33/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.33/0.99      | v1_partfun1(X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | v1_xboole_0(X2)
% 2.33/0.99      | ~ v1_funct_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f57]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_19,plain,
% 2.33/0.99      ( v2_struct_0(X0)
% 2.33/0.99      | ~ l1_struct_0(X0)
% 2.33/0.99      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.33/0.99      inference(cnf_transformation,[],[f66]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_28,negated_conjecture,
% 2.33/0.99      ( ~ v2_struct_0(sK1) ),
% 2.33/0.99      inference(cnf_transformation,[],[f69]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_330,plain,
% 2.33/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_19,c_28]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_331,plain,
% 2.33/0.99      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_330]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_42,plain,
% 2.33/0.99      ( v2_struct_0(sK1)
% 2.33/0.99      | ~ l1_struct_0(sK1)
% 2.33/0.99      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.33/0.99      inference(instantiation,[status(thm)],[c_19]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_333,plain,
% 2.33/0.99      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.33/0.99      inference(global_propositional_subsumption,
% 2.33/0.99                [status(thm)],
% 2.33/0.99                [c_331,c_28,c_27,c_42]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_355,plain,
% 2.33/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 2.33/0.99      | v1_partfun1(X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | ~ v1_funct_1(X0)
% 2.33/0.99      | k2_struct_0(sK1) != X2 ),
% 2.33/0.99      inference(resolution_lifted,[status(thm)],[c_9,c_333]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_356,plain,
% 2.33/0.99      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.33/0.99      | v1_partfun1(X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.33/0.99      | ~ v1_funct_1(X0) ),
% 2.33/0.99      inference(unflattening,[status(thm)],[c_355]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_7,plain,
% 2.33/0.99      ( v4_relat_1(X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.33/0.99      inference(cnf_transformation,[],[f54]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_12,plain,
% 2.33/0.99      ( ~ v1_partfun1(X0,X1)
% 2.33/0.99      | ~ v4_relat_1(X0,X1)
% 2.33/0.99      | ~ v1_relat_1(X0)
% 2.33/0.99      | k1_relat_1(X0) = X1 ),
% 2.33/0.99      inference(cnf_transformation,[],[f58]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_378,plain,
% 2.33/0.99      ( ~ v1_partfun1(X0,X1)
% 2.33/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | ~ v1_relat_1(X0)
% 2.33/0.99      | k1_relat_1(X0) = X1 ),
% 2.33/0.99      inference(resolution,[status(thm)],[c_7,c_12]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_6,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/0.99      | v1_relat_1(X0) ),
% 2.33/0.99      inference(cnf_transformation,[],[f53]) ).
% 2.33/0.99  
% 2.33/0.99  cnf(c_382,plain,
% 2.33/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | ~ v1_partfun1(X0,X1)
% 2.33/1.00      | k1_relat_1(X0) = X1 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_378,c_12,c_7,c_6]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_383,plain,
% 2.33/1.00      ( ~ v1_partfun1(X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | k1_relat_1(X0) = X1 ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_382]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_422,plain,
% 2.33/1.00      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | k1_relat_1(X0) = X1 ),
% 2.33/1.00      inference(resolution,[status(thm)],[c_356,c_383]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_601,plain,
% 2.33/1.00      ( ~ v1_funct_2(X0_51,X0_52,k2_struct_0(sK1))
% 2.33/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.33/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1))))
% 2.33/1.00      | ~ v1_funct_1(X0_51)
% 2.33/1.00      | k1_relat_1(X0_51) = X0_52 ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_422]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1020,plain,
% 2.33/1.00      ( k1_relat_1(X0_51) = X0_52
% 2.33/1.00      | v1_funct_2(X0_51,X0_52,k2_struct_0(sK1)) != iProver_top
% 2.33/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.33/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_struct_0(sK1)))) != iProver_top
% 2.33/1.00      | v1_funct_1(X0_51) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_601]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2038,plain,
% 2.33/1.00      ( k1_relat_1(X0_51) = X0_52
% 2.33/1.00      | v1_funct_2(X0_51,X0_52,k2_relat_1(sK2)) != iProver_top
% 2.33/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.33/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,k2_relat_1(sK2)))) != iProver_top
% 2.33/1.00      | v1_funct_1(X0_51) != iProver_top ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_1020,c_1430]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2047,plain,
% 2.33/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.33/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.33/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_52))) != iProver_top
% 2.33/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_1434,c_2038]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_26,negated_conjecture,
% 2.33/1.00      ( v1_funct_1(sK2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f71]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_33,plain,
% 2.33/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_25,negated_conjecture,
% 2.33/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.33/1.00      inference(cnf_transformation,[],[f72]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_606,negated_conjecture,
% 2.33/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1017,plain,
% 2.33/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_606]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1030,plain,
% 2.33/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_1017,c_602,c_603]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1435,plain,
% 2.33/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_1430,c_1030]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2129,plain,
% 2.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_52))) != iProver_top
% 2.33/1.00      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_2047,c_33,c_1435]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2130,plain,
% 2.33/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.33/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0_52))) != iProver_top ),
% 2.33/1.00      inference(renaming,[status(thm)],[c_2129]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2137,plain,
% 2.33/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_1434,c_2130]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1432,plain,
% 2.33/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_1430,c_1299]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2141,plain,
% 2.33/1.00      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_2137,c_1432]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_15,plain,
% 2.33/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | ~ v2_funct_1(X0)
% 2.33/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.33/1.00      inference(cnf_transformation,[],[f64]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_612,plain,
% 2.33/1.00      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.33/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.33/1.00      | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
% 2.33/1.00      | ~ v1_funct_1(X0_51)
% 2.33/1.00      | ~ v2_funct_1(X0_51)
% 2.33/1.00      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1012,plain,
% 2.33/1.00      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.33/1.00      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.33/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.33/1.00      | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
% 2.33/1.00      | v1_funct_1(X0_51) != iProver_top
% 2.33/1.00      | v2_funct_1(X0_51) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2595,plain,
% 2.33/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.33/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 2.33/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.33/1.00      | v1_funct_1(sK2) != iProver_top
% 2.33/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2141,c_1012]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_22,negated_conjecture,
% 2.33/1.00      ( v2_funct_1(sK2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f75]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_36,plain,
% 2.33/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2140,plain,
% 2.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_2137,c_1434]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2142,plain,
% 2.33/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_2137,c_1435]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2972,plain,
% 2.33/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_2595,c_33,c_36,c_2140,c_2142]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2977,plain,
% 2.33/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2972,c_1011]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_614,plain,
% 2.33/1.00      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.33/1.00      | v1_relat_1(X0_51) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1010,plain,
% 2.33/1.00      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.33/1.00      | v1_relat_1(X0_51) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_614]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1288,plain,
% 2.33/1.00      ( v1_relat_1(sK2) = iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_1036,c_1010]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0)
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | ~ v2_funct_1(X0)
% 2.33/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f51]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_617,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0_51)
% 2.33/1.00      | ~ v1_funct_1(X0_51)
% 2.33/1.00      | ~ v2_funct_1(X0_51)
% 2.33/1.00      | k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_3]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1007,plain,
% 2.33/1.00      ( k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51)
% 2.33/1.00      | v1_relat_1(X0_51) != iProver_top
% 2.33/1.00      | v1_funct_1(X0_51) != iProver_top
% 2.33/1.00      | v2_funct_1(X0_51) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1651,plain,
% 2.33/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.33/1.00      | v1_funct_1(sK2) != iProver_top
% 2.33/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_1288,c_1007]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_667,plain,
% 2.33/1.00      ( ~ v1_relat_1(sK2)
% 2.33/1.00      | ~ v1_funct_1(sK2)
% 2.33/1.00      | ~ v2_funct_1(sK2)
% 2.33/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_617]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1203,plain,
% 2.33/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.33/1.00      | v1_relat_1(sK2) ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_614]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1969,plain,
% 2.33/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_1651,c_26,c_24,c_22,c_667,c_1203]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2982,plain,
% 2.33/1.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_2977,c_1969]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_20,plain,
% 2.33/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | ~ v2_funct_1(X0)
% 2.33/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.33/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.33/1.00      inference(cnf_transformation,[],[f67]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_610,plain,
% 2.33/1.00      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.33/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.33/1.00      | ~ v1_funct_1(X0_51)
% 2.33/1.00      | ~ v2_funct_1(X0_51)
% 2.33/1.00      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.33/1.00      | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_20]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1014,plain,
% 2.33/1.00      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.33/1.00      | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51)
% 2.33/1.00      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.33/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.33/1.00      | v1_funct_1(X0_51) != iProver_top
% 2.33/1.00      | v2_funct_1(X0_51) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3329,plain,
% 2.33/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.33/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.33/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.33/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.33/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2982,c_1014]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_5,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0)
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | ~ v2_funct_1(X0)
% 2.33/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.33/1.00      inference(cnf_transformation,[],[f52]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_615,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0_51)
% 2.33/1.00      | ~ v1_funct_1(X0_51)
% 2.33/1.00      | ~ v2_funct_1(X0_51)
% 2.33/1.00      | k2_funct_1(k2_funct_1(X0_51)) = X0_51 ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_5]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1009,plain,
% 2.33/1.00      ( k2_funct_1(k2_funct_1(X0_51)) = X0_51
% 2.33/1.00      | v1_relat_1(X0_51) != iProver_top
% 2.33/1.00      | v1_funct_1(X0_51) != iProver_top
% 2.33/1.00      | v2_funct_1(X0_51) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1750,plain,
% 2.33/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.33/1.00      | v1_funct_1(sK2) != iProver_top
% 2.33/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_1288,c_1009]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_673,plain,
% 2.33/1.00      ( ~ v1_relat_1(sK2)
% 2.33/1.00      | ~ v1_funct_1(sK2)
% 2.33/1.00      | ~ v2_funct_1(sK2)
% 2.33/1.00      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_615]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1962,plain,
% 2.33/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_1750,c_26,c_24,c_22,c_673,c_1203]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3342,plain,
% 2.33/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2
% 2.33/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 2.33/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 2.33/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.33/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_3329,c_1962]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_35,plain,
% 2.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_0,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0)
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | ~ v2_funct_1(X0)
% 2.33/1.00      | v2_funct_1(k2_funct_1(X0)) ),
% 2.33/1.00      inference(cnf_transformation,[],[f49]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_620,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0_51)
% 2.33/1.00      | ~ v1_funct_1(X0_51)
% 2.33/1.00      | ~ v2_funct_1(X0_51)
% 2.33/1.00      | v2_funct_1(k2_funct_1(X0_51)) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_657,plain,
% 2.33/1.00      ( v1_relat_1(X0_51) != iProver_top
% 2.33/1.00      | v1_funct_1(X0_51) != iProver_top
% 2.33/1.00      | v2_funct_1(X0_51) != iProver_top
% 2.33/1.00      | v2_funct_1(k2_funct_1(X0_51)) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_659,plain,
% 2.33/1.00      ( v1_relat_1(sK2) != iProver_top
% 2.33/1.00      | v1_funct_1(sK2) != iProver_top
% 2.33/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.33/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_657]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0)
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | v1_funct_1(k2_funct_1(X0))
% 2.33/1.00      | ~ v2_funct_1(X0) ),
% 2.33/1.00      inference(cnf_transformation,[],[f48]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_619,plain,
% 2.33/1.00      ( ~ v1_relat_1(X0_51)
% 2.33/1.00      | ~ v1_funct_1(X0_51)
% 2.33/1.00      | v1_funct_1(k2_funct_1(X0_51))
% 2.33/1.00      | ~ v2_funct_1(X0_51) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_660,plain,
% 2.33/1.00      ( v1_relat_1(X0_51) != iProver_top
% 2.33/1.00      | v1_funct_1(X0_51) != iProver_top
% 2.33/1.00      | v1_funct_1(k2_funct_1(X0_51)) = iProver_top
% 2.33/1.00      | v2_funct_1(X0_51) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_662,plain,
% 2.33/1.00      ( v1_relat_1(sK2) != iProver_top
% 2.33/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.33/1.00      | v1_funct_1(sK2) != iProver_top
% 2.33/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_660]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1204,plain,
% 2.33/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.33/1.00      | v1_relat_1(sK2) = iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_1203]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_16,plain,
% 2.33/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.33/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | ~ v2_funct_1(X0)
% 2.33/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.33/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_611,plain,
% 2.33/1.00      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 2.33/1.00      | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52)
% 2.33/1.00      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 2.33/1.00      | ~ v1_funct_1(X0_51)
% 2.33/1.00      | ~ v2_funct_1(X0_51)
% 2.33/1.00      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_16]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1013,plain,
% 2.33/1.00      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 2.33/1.00      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 2.33/1.00      | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52) = iProver_top
% 2.33/1.00      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 2.33/1.00      | v1_funct_1(X0_51) != iProver_top
% 2.33/1.00      | v2_funct_1(X0_51) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2597,plain,
% 2.33/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 2.33/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.33/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.33/1.00      | v1_funct_1(sK2) != iProver_top
% 2.33/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_2141,c_1013]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3417,plain,
% 2.33/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_3342,c_33,c_35,c_36,c_659,c_662,c_1204,c_2140,c_2142,
% 2.33/1.00                 c_2595,c_2597]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_13,plain,
% 2.33/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 2.33/1.00      | ~ v1_funct_2(X2,X0,X1)
% 2.33/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.33/1.00      | ~ v1_funct_1(X2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f78]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_21,negated_conjecture,
% 2.33/1.00      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.33/1.00      inference(cnf_transformation,[],[f76]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_452,plain,
% 2.33/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 2.33/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.33/1.00      | ~ v1_funct_1(X0)
% 2.33/1.00      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.33/1.00      | u1_struct_0(sK1) != X2
% 2.33/1.00      | u1_struct_0(sK0) != X1
% 2.33/1.00      | sK2 != X0 ),
% 2.33/1.00      inference(resolution_lifted,[status(thm)],[c_13,c_21]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_453,plain,
% 2.33/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.33/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.33/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.33/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.33/1.00      inference(unflattening,[status(thm)],[c_452]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_600,plain,
% 2.33/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.33/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.33/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.33/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.33/1.00      inference(subtyping,[status(esa)],[c_453]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1021,plain,
% 2.33/1.00      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.33/1.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.33/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.33/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.33/1.00      inference(predicate_to_equality,[status(thm)],[c_600]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1149,plain,
% 2.33/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.33/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.33/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.33/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_1021,c_602,c_603]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1433,plain,
% 2.33/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 2.33/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.33/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.33/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_1430,c_1149]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2139,plain,
% 2.33/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != sK2
% 2.33/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.33/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.33/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))) != iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_2137,c_1433]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_1909,plain,
% 2.33/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 2.33/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 2.33/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 2.33/1.00      | v1_funct_1(sK2) != iProver_top
% 2.33/1.00      | v2_funct_1(sK2) != iProver_top ),
% 2.33/1.00      inference(superposition,[status(thm)],[c_1432,c_1014]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2905,plain,
% 2.33/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.33/1.00      inference(global_propositional_subsumption,
% 2.33/1.00                [status(thm)],
% 2.33/1.00                [c_1909,c_33,c_36,c_1434,c_1435]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2907,plain,
% 2.33/1.00      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_2905,c_2137]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_2910,plain,
% 2.33/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 2.33/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.33/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.33/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 2.33/1.00      inference(light_normalisation,[status(thm)],[c_2139,c_2907]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_3420,plain,
% 2.33/1.00      ( sK2 != sK2
% 2.33/1.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 2.33/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 2.33/1.00      | v1_funct_1(sK2) != iProver_top ),
% 2.33/1.00      inference(demodulation,[status(thm)],[c_3417,c_2910]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_622,plain,( X0_51 = X0_51 ),theory(equality) ).
% 2.33/1.00  
% 2.33/1.00  cnf(c_653,plain,
% 2.33/1.00      ( sK2 = sK2 ),
% 2.33/1.00      inference(instantiation,[status(thm)],[c_622]) ).
% 2.33/1.00  
% 2.33/1.00  cnf(contradiction,plain,
% 2.33/1.00      ( $false ),
% 2.33/1.00      inference(minisat,[status(thm)],[c_3420,c_2142,c_2140,c_653,c_33]) ).
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 2.33/1.00  
% 2.33/1.00  ------                               Statistics
% 2.33/1.00  
% 2.33/1.00  ------ General
% 2.33/1.00  
% 2.33/1.00  abstr_ref_over_cycles:                  0
% 2.33/1.00  abstr_ref_under_cycles:                 0
% 2.33/1.00  gc_basic_clause_elim:                   0
% 2.33/1.00  forced_gc_time:                         0
% 2.33/1.00  parsing_time:                           0.007
% 2.33/1.00  unif_index_cands_time:                  0.
% 2.33/1.00  unif_index_add_time:                    0.
% 2.33/1.00  orderings_time:                         0.
% 2.33/1.00  out_proof_time:                         0.016
% 2.33/1.00  total_time:                             0.128
% 2.33/1.00  num_of_symbols:                         56
% 2.33/1.00  num_of_terms:                           2954
% 2.33/1.00  
% 2.33/1.00  ------ Preprocessing
% 2.33/1.00  
% 2.33/1.00  num_of_splits:                          0
% 2.33/1.00  num_of_split_atoms:                     0
% 2.33/1.00  num_of_reused_defs:                     0
% 2.33/1.00  num_eq_ax_congr_red:                    4
% 2.33/1.00  num_of_sem_filtered_clauses:            1
% 2.33/1.00  num_of_subtypes:                        5
% 2.33/1.00  monotx_restored_types:                  1
% 2.33/1.00  sat_num_of_epr_types:                   0
% 2.33/1.00  sat_num_of_non_cyclic_types:            0
% 2.33/1.00  sat_guarded_non_collapsed_types:        1
% 2.33/1.00  num_pure_diseq_elim:                    0
% 2.33/1.00  simp_replaced_by:                       0
% 2.33/1.00  res_preprocessed:                       129
% 2.33/1.00  prep_upred:                             0
% 2.33/1.00  prep_unflattend:                        15
% 2.33/1.00  smt_new_axioms:                         0
% 2.33/1.00  pred_elim_cands:                        5
% 2.33/1.00  pred_elim:                              6
% 2.33/1.00  pred_elim_cl:                           8
% 2.33/1.00  pred_elim_cycles:                       8
% 2.33/1.00  merged_defs:                            0
% 2.33/1.00  merged_defs_ncl:                        0
% 2.33/1.00  bin_hyper_res:                          0
% 2.33/1.00  prep_cycles:                            4
% 2.33/1.00  pred_elim_time:                         0.002
% 2.33/1.00  splitting_time:                         0.
% 2.33/1.00  sem_filter_time:                        0.
% 2.33/1.00  monotx_time:                            0.
% 2.33/1.00  subtype_inf_time:                       0.001
% 2.33/1.00  
% 2.33/1.00  ------ Problem properties
% 2.33/1.00  
% 2.33/1.00  clauses:                                21
% 2.33/1.00  conjectures:                            5
% 2.33/1.00  epr:                                    2
% 2.33/1.00  horn:                                   21
% 2.33/1.00  ground:                                 8
% 2.33/1.00  unary:                                  7
% 2.33/1.00  binary:                                 2
% 2.33/1.00  lits:                                   66
% 2.33/1.00  lits_eq:                                13
% 2.33/1.00  fd_pure:                                0
% 2.33/1.00  fd_pseudo:                              0
% 2.33/1.00  fd_cond:                                0
% 2.33/1.00  fd_pseudo_cond:                         1
% 2.33/1.00  ac_symbols:                             0
% 2.33/1.00  
% 2.33/1.00  ------ Propositional Solver
% 2.33/1.00  
% 2.33/1.00  prop_solver_calls:                      30
% 2.33/1.00  prop_fast_solver_calls:                 1015
% 2.33/1.00  smt_solver_calls:                       0
% 2.33/1.00  smt_fast_solver_calls:                  0
% 2.33/1.00  prop_num_of_clauses:                    1211
% 2.33/1.00  prop_preprocess_simplified:             4498
% 2.33/1.00  prop_fo_subsumed:                       44
% 2.33/1.00  prop_solver_time:                       0.
% 2.33/1.00  smt_solver_time:                        0.
% 2.33/1.00  smt_fast_solver_time:                   0.
% 2.33/1.00  prop_fast_solver_time:                  0.
% 2.33/1.00  prop_unsat_core_time:                   0.
% 2.33/1.00  
% 2.33/1.00  ------ QBF
% 2.33/1.00  
% 2.33/1.00  qbf_q_res:                              0
% 2.33/1.00  qbf_num_tautologies:                    0
% 2.33/1.00  qbf_prep_cycles:                        0
% 2.33/1.00  
% 2.33/1.00  ------ BMC1
% 2.33/1.00  
% 2.33/1.00  bmc1_current_bound:                     -1
% 2.33/1.00  bmc1_last_solved_bound:                 -1
% 2.33/1.00  bmc1_unsat_core_size:                   -1
% 2.33/1.00  bmc1_unsat_core_parents_size:           -1
% 2.33/1.00  bmc1_merge_next_fun:                    0
% 2.33/1.00  bmc1_unsat_core_clauses_time:           0.
% 2.33/1.00  
% 2.33/1.00  ------ Instantiation
% 2.33/1.00  
% 2.33/1.00  inst_num_of_clauses:                    418
% 2.33/1.00  inst_num_in_passive:                    81
% 2.33/1.00  inst_num_in_active:                     251
% 2.33/1.00  inst_num_in_unprocessed:                86
% 2.33/1.00  inst_num_of_loops:                      270
% 2.33/1.00  inst_num_of_learning_restarts:          0
% 2.33/1.00  inst_num_moves_active_passive:          14
% 2.33/1.00  inst_lit_activity:                      0
% 2.33/1.00  inst_lit_activity_moves:                0
% 2.33/1.00  inst_num_tautologies:                   0
% 2.33/1.00  inst_num_prop_implied:                  0
% 2.33/1.00  inst_num_existing_simplified:           0
% 2.33/1.00  inst_num_eq_res_simplified:             0
% 2.33/1.00  inst_num_child_elim:                    0
% 2.33/1.00  inst_num_of_dismatching_blockings:      80
% 2.33/1.00  inst_num_of_non_proper_insts:           408
% 2.33/1.00  inst_num_of_duplicates:                 0
% 2.33/1.00  inst_inst_num_from_inst_to_res:         0
% 2.33/1.00  inst_dismatching_checking_time:         0.
% 2.33/1.00  
% 2.33/1.00  ------ Resolution
% 2.33/1.00  
% 2.33/1.00  res_num_of_clauses:                     0
% 2.33/1.00  res_num_in_passive:                     0
% 2.33/1.00  res_num_in_active:                      0
% 2.33/1.00  res_num_of_loops:                       133
% 2.33/1.00  res_forward_subset_subsumed:            45
% 2.33/1.00  res_backward_subset_subsumed:           0
% 2.33/1.00  res_forward_subsumed:                   0
% 2.33/1.00  res_backward_subsumed:                  0
% 2.33/1.00  res_forward_subsumption_resolution:     1
% 2.33/1.00  res_backward_subsumption_resolution:    0
% 2.33/1.00  res_clause_to_clause_subsumption:       160
% 2.33/1.00  res_orphan_elimination:                 0
% 2.33/1.00  res_tautology_del:                      44
% 2.33/1.00  res_num_eq_res_simplified:              0
% 2.33/1.00  res_num_sel_changes:                    0
% 2.33/1.00  res_moves_from_active_to_pass:          0
% 2.33/1.00  
% 2.33/1.00  ------ Superposition
% 2.33/1.00  
% 2.33/1.00  sup_time_total:                         0.
% 2.33/1.00  sup_time_generating:                    0.
% 2.33/1.00  sup_time_sim_full:                      0.
% 2.33/1.00  sup_time_sim_immed:                     0.
% 2.33/1.00  
% 2.33/1.00  sup_num_of_clauses:                     44
% 2.33/1.00  sup_num_in_active:                      39
% 2.33/1.00  sup_num_in_passive:                     5
% 2.33/1.00  sup_num_of_loops:                       52
% 2.33/1.00  sup_fw_superposition:                   31
% 2.33/1.00  sup_bw_superposition:                   23
% 2.33/1.00  sup_immediate_simplified:               26
% 2.33/1.00  sup_given_eliminated:                   0
% 2.33/1.00  comparisons_done:                       0
% 2.33/1.00  comparisons_avoided:                    0
% 2.33/1.00  
% 2.33/1.00  ------ Simplifications
% 2.33/1.00  
% 2.33/1.00  
% 2.33/1.00  sim_fw_subset_subsumed:                 3
% 2.33/1.00  sim_bw_subset_subsumed:                 4
% 2.33/1.00  sim_fw_subsumed:                        3
% 2.33/1.00  sim_bw_subsumed:                        0
% 2.33/1.00  sim_fw_subsumption_res:                 0
% 2.33/1.00  sim_bw_subsumption_res:                 0
% 2.33/1.00  sim_tautology_del:                      0
% 2.33/1.00  sim_eq_tautology_del:                   18
% 2.33/1.00  sim_eq_res_simp:                        0
% 2.33/1.00  sim_fw_demodulated:                     0
% 2.33/1.00  sim_bw_demodulated:                     12
% 2.33/1.00  sim_light_normalised:                   30
% 2.33/1.00  sim_joinable_taut:                      0
% 2.33/1.00  sim_joinable_simp:                      0
% 2.33/1.00  sim_ac_normalised:                      0
% 2.33/1.00  sim_smt_subsumption:                    0
% 2.33/1.00  
%------------------------------------------------------------------------------
