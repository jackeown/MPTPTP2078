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
% DateTime   : Thu Dec  3 12:17:42 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :  152 (2886 expanded)
%              Number of clauses        :   98 ( 876 expanded)
%              Number of leaves         :   13 ( 839 expanded)
%              Depth                    :   24
%              Number of atoms          :  609 (19427 expanded)
%              Number of equality atoms :  213 (3410 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f10,conjecture,(
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
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,negated_conjecture,(
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
                    & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f26,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
          & v2_funct_1(X2)
          & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2)
        & v2_funct_1(sK2)
        & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
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
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31,f30,f29])).

fof(f54,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f41,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f51,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f55,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
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

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f17])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f40])).

fof(f56,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f14,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f37,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f36,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f9,axiom,(
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
                  & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f49,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f16,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f38,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

cnf(c_17,negated_conjecture,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_633,negated_conjecture,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_23,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_458,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_23])).

cnf(c_459,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_458])).

cnf(c_623,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_459])).

cnf(c_21,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_453,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_454,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_624,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_454])).

cnf(c_1066,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_633,c_623,c_624])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_638,plain,
    ( ~ v1_funct_2(X0_49,X0_47,X1_47)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | k2_tops_2(X0_47,X1_47,X0_49) = k2_funct_1(X0_49)
    | k2_relset_1(X0_47,X1_47,X0_49) != X1_47 ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1040,plain,
    ( k2_tops_2(X0_47,X1_47,X0_49) = k2_funct_1(X0_49)
    | k2_relset_1(X0_47,X1_47,X0_49) != X1_47
    | v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_638])).

cnf(c_1726,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_1040])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_27,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_16,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_30,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_18,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_632,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1045,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_1069,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1045,c_623,c_624])).

cnf(c_19,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_631,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_1046,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_1063,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1046,c_623,c_624])).

cnf(c_2049,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1726,c_27,c_30,c_1069,c_1063])).

cnf(c_6,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_15,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_258,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_15])).

cnf(c_259,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_258])).

cnf(c_629,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_259])).

cnf(c_1048,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_1198,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1048,c_623,c_624])).

cnf(c_2052,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2049,c_1198])).

cnf(c_29,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_642,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | v2_funct_1(k2_funct_1(X0_49))
    | ~ v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_681,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v2_funct_1(k2_funct_1(X0_49)) = iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_642])).

cnf(c_683,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_641,plain,
    ( ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_funct_1(X0_49))
    | ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_684,plain,
    ( v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_funct_1(X0_49)) = iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_641])).

cnf(c_686,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_684])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_644,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
    | ~ v1_relat_1(X1_49)
    | v1_relat_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1277,plain,
    ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | v1_relat_1(X0_49)
    | ~ v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_1382,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1277])).

cnf(c_1383,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1382])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_643,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1411,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_1412,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1411])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_637,plain,
    ( ~ v1_funct_2(X0_49,X0_47,X1_47)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | m1_subset_1(k2_tops_2(X0_47,X1_47,X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_47)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1041,plain,
    ( v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | m1_subset_1(k2_tops_2(X0_47,X1_47,X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_47))) = iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_2068,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_1041])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_636,plain,
    ( ~ v1_funct_2(X0_49,X0_47,X1_47)
    | v1_funct_2(k2_tops_2(X0_47,X1_47,X0_49),X1_47,X0_47)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ v1_funct_1(X0_49) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1042,plain,
    ( v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
    | v1_funct_2(k2_tops_2(X0_47,X1_47,X0_49),X1_47,X0_47) = iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_2069,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2049,c_1042])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_22,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_310,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_311,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_310])).

cnf(c_315,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_311,c_21])).

cnf(c_316,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_315])).

cnf(c_405,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_316,c_23])).

cnf(c_406,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_405])).

cnf(c_626,plain,
    ( ~ v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_406])).

cnf(c_1051,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
    | v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_1172,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_49) != k2_struct_0(sK1)
    | v1_funct_2(X0_49,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1051,c_623,c_624])).

cnf(c_1527,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1066,c_1172])).

cnf(c_1228,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_1530,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1527,c_27,c_30,c_1069,c_1063,c_1228,c_1066])).

cnf(c_2054,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2049,c_1530])).

cnf(c_2129,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2054,c_1040])).

cnf(c_630,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1047,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_639,plain,
    ( ~ v1_funct_1(X0_49)
    | ~ v2_funct_1(X0_49)
    | ~ v1_relat_1(X0_49)
    | k2_funct_1(k2_funct_1(X0_49)) = X0_49 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1039,plain,
    ( k2_funct_1(k2_funct_1(X0_49)) = X0_49
    | v1_funct_1(X0_49) != iProver_top
    | v2_funct_1(X0_49) != iProver_top
    | v1_relat_1(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_639])).

cnf(c_1695,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1047,c_1039])).

cnf(c_691,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_639])).

cnf(c_1962,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1695,c_20,c_18,c_16,c_691,c_1382,c_1411])).

cnf(c_2130,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2129,c_1962])).

cnf(c_2206,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2068,c_27,c_1069,c_1063])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_635,plain,
    ( ~ v1_funct_2(X0_49,X0_47,X1_47)
    | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
    | ~ v1_funct_1(X0_49)
    | v1_funct_1(k2_tops_2(X0_47,X1_47,X0_49)) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1043,plain,
    ( v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
    | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
    | v1_funct_1(X0_49) != iProver_top
    | v1_funct_1(k2_tops_2(X0_47,X1_47,X0_49)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_2211,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2206,c_1043])).

cnf(c_2315,plain,
    ( m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2052,c_27,c_29,c_30,c_683,c_686,c_1069,c_1063,c_1383,c_1412,c_2068,c_2069,c_2130,c_2211])).

cnf(c_2316,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2315])).

cnf(c_2309,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2130,c_27,c_29,c_30,c_683,c_686,c_1069,c_1063,c_1383,c_1412,c_2068,c_2069])).

cnf(c_2319,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2316,c_2309])).

cnf(c_2322,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2319,c_1069,c_1063])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 16:13:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 2.66/1.02  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.02  
% 2.66/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.66/1.02  
% 2.66/1.02  ------  iProver source info
% 2.66/1.02  
% 2.66/1.02  git: date: 2020-06-30 10:37:57 +0100
% 2.66/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.66/1.02  git: non_committed_changes: false
% 2.66/1.02  git: last_make_outside_of_git: false
% 2.66/1.02  
% 2.66/1.02  ------ 
% 2.66/1.02  
% 2.66/1.02  ------ Input Options
% 2.66/1.02  
% 2.66/1.02  --out_options                           all
% 2.66/1.02  --tptp_safe_out                         true
% 2.66/1.02  --problem_path                          ""
% 2.66/1.02  --include_path                          ""
% 2.66/1.02  --clausifier                            res/vclausify_rel
% 2.66/1.02  --clausifier_options                    --mode clausify
% 2.66/1.02  --stdin                                 false
% 2.66/1.02  --stats_out                             all
% 2.66/1.02  
% 2.66/1.02  ------ General Options
% 2.66/1.02  
% 2.66/1.02  --fof                                   false
% 2.66/1.02  --time_out_real                         305.
% 2.66/1.02  --time_out_virtual                      -1.
% 2.66/1.02  --symbol_type_check                     false
% 2.66/1.02  --clausify_out                          false
% 2.66/1.02  --sig_cnt_out                           false
% 2.66/1.02  --trig_cnt_out                          false
% 2.66/1.02  --trig_cnt_out_tolerance                1.
% 2.66/1.02  --trig_cnt_out_sk_spl                   false
% 2.66/1.02  --abstr_cl_out                          false
% 2.66/1.02  
% 2.66/1.02  ------ Global Options
% 2.66/1.02  
% 2.66/1.02  --schedule                              default
% 2.66/1.02  --add_important_lit                     false
% 2.66/1.02  --prop_solver_per_cl                    1000
% 2.66/1.02  --min_unsat_core                        false
% 2.66/1.02  --soft_assumptions                      false
% 2.66/1.02  --soft_lemma_size                       3
% 2.66/1.02  --prop_impl_unit_size                   0
% 2.66/1.02  --prop_impl_unit                        []
% 2.66/1.02  --share_sel_clauses                     true
% 2.66/1.02  --reset_solvers                         false
% 2.66/1.02  --bc_imp_inh                            [conj_cone]
% 2.66/1.02  --conj_cone_tolerance                   3.
% 2.66/1.02  --extra_neg_conj                        none
% 2.66/1.02  --large_theory_mode                     true
% 2.66/1.02  --prolific_symb_bound                   200
% 2.66/1.02  --lt_threshold                          2000
% 2.66/1.02  --clause_weak_htbl                      true
% 2.66/1.02  --gc_record_bc_elim                     false
% 2.66/1.02  
% 2.66/1.02  ------ Preprocessing Options
% 2.66/1.02  
% 2.66/1.02  --preprocessing_flag                    true
% 2.66/1.02  --time_out_prep_mult                    0.1
% 2.66/1.02  --splitting_mode                        input
% 2.66/1.02  --splitting_grd                         true
% 2.66/1.02  --splitting_cvd                         false
% 2.66/1.02  --splitting_cvd_svl                     false
% 2.66/1.02  --splitting_nvd                         32
% 2.66/1.02  --sub_typing                            true
% 2.66/1.02  --prep_gs_sim                           true
% 2.66/1.02  --prep_unflatten                        true
% 2.66/1.02  --prep_res_sim                          true
% 2.66/1.02  --prep_upred                            true
% 2.66/1.02  --prep_sem_filter                       exhaustive
% 2.66/1.02  --prep_sem_filter_out                   false
% 2.66/1.02  --pred_elim                             true
% 2.66/1.02  --res_sim_input                         true
% 2.66/1.02  --eq_ax_congr_red                       true
% 2.66/1.02  --pure_diseq_elim                       true
% 2.66/1.02  --brand_transform                       false
% 2.66/1.02  --non_eq_to_eq                          false
% 2.66/1.02  --prep_def_merge                        true
% 2.66/1.02  --prep_def_merge_prop_impl              false
% 2.66/1.02  --prep_def_merge_mbd                    true
% 2.66/1.02  --prep_def_merge_tr_red                 false
% 2.66/1.02  --prep_def_merge_tr_cl                  false
% 2.66/1.02  --smt_preprocessing                     true
% 2.66/1.02  --smt_ac_axioms                         fast
% 2.66/1.02  --preprocessed_out                      false
% 2.66/1.02  --preprocessed_stats                    false
% 2.66/1.02  
% 2.66/1.02  ------ Abstraction refinement Options
% 2.66/1.02  
% 2.66/1.02  --abstr_ref                             []
% 2.66/1.02  --abstr_ref_prep                        false
% 2.66/1.02  --abstr_ref_until_sat                   false
% 2.66/1.02  --abstr_ref_sig_restrict                funpre
% 2.66/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/1.02  --abstr_ref_under                       []
% 2.66/1.02  
% 2.66/1.02  ------ SAT Options
% 2.66/1.02  
% 2.66/1.02  --sat_mode                              false
% 2.66/1.02  --sat_fm_restart_options                ""
% 2.66/1.02  --sat_gr_def                            false
% 2.66/1.02  --sat_epr_types                         true
% 2.66/1.02  --sat_non_cyclic_types                  false
% 2.66/1.02  --sat_finite_models                     false
% 2.66/1.02  --sat_fm_lemmas                         false
% 2.66/1.02  --sat_fm_prep                           false
% 2.66/1.02  --sat_fm_uc_incr                        true
% 2.66/1.02  --sat_out_model                         small
% 2.66/1.02  --sat_out_clauses                       false
% 2.66/1.02  
% 2.66/1.02  ------ QBF Options
% 2.66/1.02  
% 2.66/1.02  --qbf_mode                              false
% 2.66/1.02  --qbf_elim_univ                         false
% 2.66/1.02  --qbf_dom_inst                          none
% 2.66/1.02  --qbf_dom_pre_inst                      false
% 2.66/1.02  --qbf_sk_in                             false
% 2.66/1.02  --qbf_pred_elim                         true
% 2.66/1.02  --qbf_split                             512
% 2.66/1.02  
% 2.66/1.02  ------ BMC1 Options
% 2.66/1.02  
% 2.66/1.02  --bmc1_incremental                      false
% 2.66/1.02  --bmc1_axioms                           reachable_all
% 2.66/1.02  --bmc1_min_bound                        0
% 2.66/1.02  --bmc1_max_bound                        -1
% 2.66/1.02  --bmc1_max_bound_default                -1
% 2.66/1.02  --bmc1_symbol_reachability              true
% 2.66/1.02  --bmc1_property_lemmas                  false
% 2.66/1.02  --bmc1_k_induction                      false
% 2.66/1.02  --bmc1_non_equiv_states                 false
% 2.66/1.02  --bmc1_deadlock                         false
% 2.66/1.02  --bmc1_ucm                              false
% 2.66/1.02  --bmc1_add_unsat_core                   none
% 2.66/1.02  --bmc1_unsat_core_children              false
% 2.66/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/1.02  --bmc1_out_stat                         full
% 2.66/1.02  --bmc1_ground_init                      false
% 2.66/1.02  --bmc1_pre_inst_next_state              false
% 2.66/1.02  --bmc1_pre_inst_state                   false
% 2.66/1.02  --bmc1_pre_inst_reach_state             false
% 2.66/1.02  --bmc1_out_unsat_core                   false
% 2.66/1.02  --bmc1_aig_witness_out                  false
% 2.66/1.02  --bmc1_verbose                          false
% 2.66/1.02  --bmc1_dump_clauses_tptp                false
% 2.66/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.66/1.02  --bmc1_dump_file                        -
% 2.66/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.66/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.66/1.02  --bmc1_ucm_extend_mode                  1
% 2.66/1.02  --bmc1_ucm_init_mode                    2
% 2.66/1.02  --bmc1_ucm_cone_mode                    none
% 2.66/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.66/1.02  --bmc1_ucm_relax_model                  4
% 2.66/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.66/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/1.02  --bmc1_ucm_layered_model                none
% 2.66/1.02  --bmc1_ucm_max_lemma_size               10
% 2.66/1.02  
% 2.66/1.02  ------ AIG Options
% 2.66/1.02  
% 2.66/1.02  --aig_mode                              false
% 2.66/1.02  
% 2.66/1.02  ------ Instantiation Options
% 2.66/1.02  
% 2.66/1.02  --instantiation_flag                    true
% 2.66/1.02  --inst_sos_flag                         false
% 2.66/1.02  --inst_sos_phase                        true
% 2.66/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/1.02  --inst_lit_sel_side                     num_symb
% 2.66/1.02  --inst_solver_per_active                1400
% 2.66/1.02  --inst_solver_calls_frac                1.
% 2.66/1.02  --inst_passive_queue_type               priority_queues
% 2.66/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/1.02  --inst_passive_queues_freq              [25;2]
% 2.66/1.02  --inst_dismatching                      true
% 2.66/1.02  --inst_eager_unprocessed_to_passive     true
% 2.66/1.02  --inst_prop_sim_given                   true
% 2.66/1.02  --inst_prop_sim_new                     false
% 2.66/1.02  --inst_subs_new                         false
% 2.66/1.02  --inst_eq_res_simp                      false
% 2.66/1.02  --inst_subs_given                       false
% 2.66/1.02  --inst_orphan_elimination               true
% 2.66/1.02  --inst_learning_loop_flag               true
% 2.66/1.02  --inst_learning_start                   3000
% 2.66/1.02  --inst_learning_factor                  2
% 2.66/1.02  --inst_start_prop_sim_after_learn       3
% 2.66/1.02  --inst_sel_renew                        solver
% 2.66/1.02  --inst_lit_activity_flag                true
% 2.66/1.02  --inst_restr_to_given                   false
% 2.66/1.02  --inst_activity_threshold               500
% 2.66/1.02  --inst_out_proof                        true
% 2.66/1.02  
% 2.66/1.02  ------ Resolution Options
% 2.66/1.02  
% 2.66/1.02  --resolution_flag                       true
% 2.66/1.02  --res_lit_sel                           adaptive
% 2.66/1.02  --res_lit_sel_side                      none
% 2.66/1.02  --res_ordering                          kbo
% 2.66/1.02  --res_to_prop_solver                    active
% 2.66/1.02  --res_prop_simpl_new                    false
% 2.66/1.02  --res_prop_simpl_given                  true
% 2.66/1.02  --res_passive_queue_type                priority_queues
% 2.66/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/1.02  --res_passive_queues_freq               [15;5]
% 2.66/1.02  --res_forward_subs                      full
% 2.66/1.02  --res_backward_subs                     full
% 2.66/1.02  --res_forward_subs_resolution           true
% 2.66/1.02  --res_backward_subs_resolution          true
% 2.66/1.02  --res_orphan_elimination                true
% 2.66/1.02  --res_time_limit                        2.
% 2.66/1.02  --res_out_proof                         true
% 2.66/1.02  
% 2.66/1.02  ------ Superposition Options
% 2.66/1.02  
% 2.66/1.02  --superposition_flag                    true
% 2.66/1.02  --sup_passive_queue_type                priority_queues
% 2.66/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.66/1.02  --demod_completeness_check              fast
% 2.66/1.02  --demod_use_ground                      true
% 2.66/1.02  --sup_to_prop_solver                    passive
% 2.66/1.02  --sup_prop_simpl_new                    true
% 2.66/1.02  --sup_prop_simpl_given                  true
% 2.66/1.02  --sup_fun_splitting                     false
% 2.66/1.02  --sup_smt_interval                      50000
% 2.66/1.02  
% 2.66/1.02  ------ Superposition Simplification Setup
% 2.66/1.02  
% 2.66/1.02  --sup_indices_passive                   []
% 2.66/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.02  --sup_full_bw                           [BwDemod]
% 2.66/1.02  --sup_immed_triv                        [TrivRules]
% 2.66/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.02  --sup_immed_bw_main                     []
% 2.66/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.02  
% 2.66/1.02  ------ Combination Options
% 2.66/1.02  
% 2.66/1.02  --comb_res_mult                         3
% 2.66/1.02  --comb_sup_mult                         2
% 2.66/1.02  --comb_inst_mult                        10
% 2.66/1.02  
% 2.66/1.02  ------ Debug Options
% 2.66/1.02  
% 2.66/1.02  --dbg_backtrace                         false
% 2.66/1.02  --dbg_dump_prop_clauses                 false
% 2.66/1.02  --dbg_dump_prop_clauses_file            -
% 2.66/1.02  --dbg_out_stat                          false
% 2.66/1.02  ------ Parsing...
% 2.66/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.66/1.02  
% 2.66/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.66/1.02  
% 2.66/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.66/1.02  
% 2.66/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.66/1.02  ------ Proving...
% 2.66/1.02  ------ Problem Properties 
% 2.66/1.02  
% 2.66/1.02  
% 2.66/1.02  clauses                                 22
% 2.66/1.02  conjectures                             5
% 2.66/1.02  EPR                                     2
% 2.66/1.02  Horn                                    22
% 2.66/1.02  unary                                   8
% 2.66/1.02  binary                                  0
% 2.66/1.02  lits                                    73
% 2.66/1.02  lits eq                                 15
% 2.66/1.02  fd_pure                                 0
% 2.66/1.02  fd_pseudo                               0
% 2.66/1.02  fd_cond                                 0
% 2.66/1.02  fd_pseudo_cond                          0
% 2.66/1.02  AC symbols                              0
% 2.66/1.02  
% 2.66/1.02  ------ Schedule dynamic 5 is on 
% 2.66/1.02  
% 2.66/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.66/1.02  
% 2.66/1.02  
% 2.66/1.02  ------ 
% 2.66/1.02  Current options:
% 2.66/1.02  ------ 
% 2.66/1.02  
% 2.66/1.02  ------ Input Options
% 2.66/1.02  
% 2.66/1.02  --out_options                           all
% 2.66/1.02  --tptp_safe_out                         true
% 2.66/1.02  --problem_path                          ""
% 2.66/1.02  --include_path                          ""
% 2.66/1.02  --clausifier                            res/vclausify_rel
% 2.66/1.02  --clausifier_options                    --mode clausify
% 2.66/1.02  --stdin                                 false
% 2.66/1.02  --stats_out                             all
% 2.66/1.02  
% 2.66/1.02  ------ General Options
% 2.66/1.02  
% 2.66/1.02  --fof                                   false
% 2.66/1.02  --time_out_real                         305.
% 2.66/1.02  --time_out_virtual                      -1.
% 2.66/1.02  --symbol_type_check                     false
% 2.66/1.02  --clausify_out                          false
% 2.66/1.02  --sig_cnt_out                           false
% 2.66/1.02  --trig_cnt_out                          false
% 2.66/1.02  --trig_cnt_out_tolerance                1.
% 2.66/1.02  --trig_cnt_out_sk_spl                   false
% 2.66/1.02  --abstr_cl_out                          false
% 2.66/1.02  
% 2.66/1.02  ------ Global Options
% 2.66/1.02  
% 2.66/1.02  --schedule                              default
% 2.66/1.02  --add_important_lit                     false
% 2.66/1.02  --prop_solver_per_cl                    1000
% 2.66/1.02  --min_unsat_core                        false
% 2.66/1.02  --soft_assumptions                      false
% 2.66/1.02  --soft_lemma_size                       3
% 2.66/1.02  --prop_impl_unit_size                   0
% 2.66/1.02  --prop_impl_unit                        []
% 2.66/1.02  --share_sel_clauses                     true
% 2.66/1.02  --reset_solvers                         false
% 2.66/1.02  --bc_imp_inh                            [conj_cone]
% 2.66/1.02  --conj_cone_tolerance                   3.
% 2.66/1.02  --extra_neg_conj                        none
% 2.66/1.02  --large_theory_mode                     true
% 2.66/1.02  --prolific_symb_bound                   200
% 2.66/1.02  --lt_threshold                          2000
% 2.66/1.02  --clause_weak_htbl                      true
% 2.66/1.02  --gc_record_bc_elim                     false
% 2.66/1.02  
% 2.66/1.02  ------ Preprocessing Options
% 2.66/1.02  
% 2.66/1.02  --preprocessing_flag                    true
% 2.66/1.02  --time_out_prep_mult                    0.1
% 2.66/1.02  --splitting_mode                        input
% 2.66/1.02  --splitting_grd                         true
% 2.66/1.02  --splitting_cvd                         false
% 2.66/1.02  --splitting_cvd_svl                     false
% 2.66/1.02  --splitting_nvd                         32
% 2.66/1.02  --sub_typing                            true
% 2.66/1.02  --prep_gs_sim                           true
% 2.66/1.02  --prep_unflatten                        true
% 2.66/1.02  --prep_res_sim                          true
% 2.66/1.02  --prep_upred                            true
% 2.66/1.02  --prep_sem_filter                       exhaustive
% 2.66/1.02  --prep_sem_filter_out                   false
% 2.66/1.02  --pred_elim                             true
% 2.66/1.02  --res_sim_input                         true
% 2.66/1.02  --eq_ax_congr_red                       true
% 2.66/1.02  --pure_diseq_elim                       true
% 2.66/1.02  --brand_transform                       false
% 2.66/1.02  --non_eq_to_eq                          false
% 2.66/1.02  --prep_def_merge                        true
% 2.66/1.02  --prep_def_merge_prop_impl              false
% 2.66/1.02  --prep_def_merge_mbd                    true
% 2.66/1.02  --prep_def_merge_tr_red                 false
% 2.66/1.02  --prep_def_merge_tr_cl                  false
% 2.66/1.02  --smt_preprocessing                     true
% 2.66/1.02  --smt_ac_axioms                         fast
% 2.66/1.02  --preprocessed_out                      false
% 2.66/1.02  --preprocessed_stats                    false
% 2.66/1.02  
% 2.66/1.02  ------ Abstraction refinement Options
% 2.66/1.02  
% 2.66/1.02  --abstr_ref                             []
% 2.66/1.02  --abstr_ref_prep                        false
% 2.66/1.02  --abstr_ref_until_sat                   false
% 2.66/1.02  --abstr_ref_sig_restrict                funpre
% 2.66/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 2.66/1.02  --abstr_ref_under                       []
% 2.66/1.02  
% 2.66/1.02  ------ SAT Options
% 2.66/1.02  
% 2.66/1.02  --sat_mode                              false
% 2.66/1.02  --sat_fm_restart_options                ""
% 2.66/1.02  --sat_gr_def                            false
% 2.66/1.02  --sat_epr_types                         true
% 2.66/1.02  --sat_non_cyclic_types                  false
% 2.66/1.02  --sat_finite_models                     false
% 2.66/1.02  --sat_fm_lemmas                         false
% 2.66/1.02  --sat_fm_prep                           false
% 2.66/1.02  --sat_fm_uc_incr                        true
% 2.66/1.02  --sat_out_model                         small
% 2.66/1.02  --sat_out_clauses                       false
% 2.66/1.02  
% 2.66/1.02  ------ QBF Options
% 2.66/1.02  
% 2.66/1.02  --qbf_mode                              false
% 2.66/1.02  --qbf_elim_univ                         false
% 2.66/1.02  --qbf_dom_inst                          none
% 2.66/1.02  --qbf_dom_pre_inst                      false
% 2.66/1.02  --qbf_sk_in                             false
% 2.66/1.02  --qbf_pred_elim                         true
% 2.66/1.02  --qbf_split                             512
% 2.66/1.02  
% 2.66/1.02  ------ BMC1 Options
% 2.66/1.02  
% 2.66/1.02  --bmc1_incremental                      false
% 2.66/1.02  --bmc1_axioms                           reachable_all
% 2.66/1.02  --bmc1_min_bound                        0
% 2.66/1.02  --bmc1_max_bound                        -1
% 2.66/1.02  --bmc1_max_bound_default                -1
% 2.66/1.02  --bmc1_symbol_reachability              true
% 2.66/1.02  --bmc1_property_lemmas                  false
% 2.66/1.02  --bmc1_k_induction                      false
% 2.66/1.02  --bmc1_non_equiv_states                 false
% 2.66/1.02  --bmc1_deadlock                         false
% 2.66/1.02  --bmc1_ucm                              false
% 2.66/1.02  --bmc1_add_unsat_core                   none
% 2.66/1.02  --bmc1_unsat_core_children              false
% 2.66/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 2.66/1.02  --bmc1_out_stat                         full
% 2.66/1.02  --bmc1_ground_init                      false
% 2.66/1.02  --bmc1_pre_inst_next_state              false
% 2.66/1.02  --bmc1_pre_inst_state                   false
% 2.66/1.02  --bmc1_pre_inst_reach_state             false
% 2.66/1.02  --bmc1_out_unsat_core                   false
% 2.66/1.02  --bmc1_aig_witness_out                  false
% 2.66/1.02  --bmc1_verbose                          false
% 2.66/1.02  --bmc1_dump_clauses_tptp                false
% 2.66/1.02  --bmc1_dump_unsat_core_tptp             false
% 2.66/1.02  --bmc1_dump_file                        -
% 2.66/1.02  --bmc1_ucm_expand_uc_limit              128
% 2.66/1.02  --bmc1_ucm_n_expand_iterations          6
% 2.66/1.02  --bmc1_ucm_extend_mode                  1
% 2.66/1.02  --bmc1_ucm_init_mode                    2
% 2.66/1.02  --bmc1_ucm_cone_mode                    none
% 2.66/1.02  --bmc1_ucm_reduced_relation_type        0
% 2.66/1.02  --bmc1_ucm_relax_model                  4
% 2.66/1.02  --bmc1_ucm_full_tr_after_sat            true
% 2.66/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 2.66/1.02  --bmc1_ucm_layered_model                none
% 2.66/1.02  --bmc1_ucm_max_lemma_size               10
% 2.66/1.02  
% 2.66/1.02  ------ AIG Options
% 2.66/1.02  
% 2.66/1.02  --aig_mode                              false
% 2.66/1.02  
% 2.66/1.02  ------ Instantiation Options
% 2.66/1.02  
% 2.66/1.02  --instantiation_flag                    true
% 2.66/1.02  --inst_sos_flag                         false
% 2.66/1.02  --inst_sos_phase                        true
% 2.66/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.66/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.66/1.02  --inst_lit_sel_side                     none
% 2.66/1.02  --inst_solver_per_active                1400
% 2.66/1.02  --inst_solver_calls_frac                1.
% 2.66/1.02  --inst_passive_queue_type               priority_queues
% 2.66/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.66/1.02  --inst_passive_queues_freq              [25;2]
% 2.66/1.02  --inst_dismatching                      true
% 2.66/1.02  --inst_eager_unprocessed_to_passive     true
% 2.66/1.02  --inst_prop_sim_given                   true
% 2.66/1.02  --inst_prop_sim_new                     false
% 2.66/1.02  --inst_subs_new                         false
% 2.66/1.02  --inst_eq_res_simp                      false
% 2.66/1.02  --inst_subs_given                       false
% 2.66/1.02  --inst_orphan_elimination               true
% 2.66/1.02  --inst_learning_loop_flag               true
% 2.66/1.02  --inst_learning_start                   3000
% 2.66/1.02  --inst_learning_factor                  2
% 2.66/1.02  --inst_start_prop_sim_after_learn       3
% 2.66/1.02  --inst_sel_renew                        solver
% 2.66/1.02  --inst_lit_activity_flag                true
% 2.66/1.02  --inst_restr_to_given                   false
% 2.66/1.02  --inst_activity_threshold               500
% 2.66/1.02  --inst_out_proof                        true
% 2.66/1.02  
% 2.66/1.02  ------ Resolution Options
% 2.66/1.02  
% 2.66/1.02  --resolution_flag                       false
% 2.66/1.02  --res_lit_sel                           adaptive
% 2.66/1.02  --res_lit_sel_side                      none
% 2.66/1.02  --res_ordering                          kbo
% 2.66/1.02  --res_to_prop_solver                    active
% 2.66/1.02  --res_prop_simpl_new                    false
% 2.66/1.02  --res_prop_simpl_given                  true
% 2.66/1.02  --res_passive_queue_type                priority_queues
% 2.66/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.66/1.02  --res_passive_queues_freq               [15;5]
% 2.66/1.02  --res_forward_subs                      full
% 2.66/1.02  --res_backward_subs                     full
% 2.66/1.02  --res_forward_subs_resolution           true
% 2.66/1.02  --res_backward_subs_resolution          true
% 2.66/1.02  --res_orphan_elimination                true
% 2.66/1.02  --res_time_limit                        2.
% 2.66/1.02  --res_out_proof                         true
% 2.66/1.02  
% 2.66/1.02  ------ Superposition Options
% 2.66/1.02  
% 2.66/1.02  --superposition_flag                    true
% 2.66/1.02  --sup_passive_queue_type                priority_queues
% 2.66/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.66/1.02  --sup_passive_queues_freq               [8;1;4]
% 2.66/1.02  --demod_completeness_check              fast
% 2.66/1.02  --demod_use_ground                      true
% 2.66/1.02  --sup_to_prop_solver                    passive
% 2.66/1.02  --sup_prop_simpl_new                    true
% 2.66/1.02  --sup_prop_simpl_given                  true
% 2.66/1.02  --sup_fun_splitting                     false
% 2.66/1.02  --sup_smt_interval                      50000
% 2.66/1.02  
% 2.66/1.02  ------ Superposition Simplification Setup
% 2.66/1.02  
% 2.66/1.02  --sup_indices_passive                   []
% 2.66/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.66/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 2.66/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.02  --sup_full_bw                           [BwDemod]
% 2.66/1.02  --sup_immed_triv                        [TrivRules]
% 2.66/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.66/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.02  --sup_immed_bw_main                     []
% 2.66/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 2.66/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.66/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.66/1.02  
% 2.66/1.02  ------ Combination Options
% 2.66/1.02  
% 2.66/1.02  --comb_res_mult                         3
% 2.66/1.02  --comb_sup_mult                         2
% 2.66/1.02  --comb_inst_mult                        10
% 2.66/1.02  
% 2.66/1.02  ------ Debug Options
% 2.66/1.02  
% 2.66/1.02  --dbg_backtrace                         false
% 2.66/1.02  --dbg_dump_prop_clauses                 false
% 2.66/1.02  --dbg_dump_prop_clauses_file            -
% 2.66/1.02  --dbg_out_stat                          false
% 2.66/1.02  
% 2.66/1.02  
% 2.66/1.02  
% 2.66/1.02  
% 2.66/1.02  ------ Proving...
% 2.66/1.02  
% 2.66/1.02  
% 2.66/1.02  % SZS status Theorem for theBenchmark.p
% 2.66/1.02  
% 2.66/1.02   Resolution empty clause
% 2.66/1.02  
% 2.66/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 2.66/1.02  
% 2.66/1.02  fof(f10,conjecture,(
% 2.66/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.66/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.02  
% 2.66/1.02  fof(f11,negated_conjecture,(
% 2.66/1.02    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.66/1.02    inference(negated_conjecture,[],[f10])).
% 2.66/1.02  
% 2.66/1.02  fof(f26,plain,(
% 2.66/1.02    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.66/1.02    inference(ennf_transformation,[],[f11])).
% 2.66/1.02  
% 2.66/1.02  fof(f27,plain,(
% 2.66/1.02    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.66/1.02    inference(flattening,[],[f26])).
% 2.66/1.02  
% 2.66/1.02  fof(f31,plain,(
% 2.66/1.02    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.66/1.02    introduced(choice_axiom,[])).
% 2.66/1.02  
% 2.66/1.02  fof(f30,plain,(
% 2.66/1.02    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.66/1.02    introduced(choice_axiom,[])).
% 2.66/1.02  
% 2.66/1.02  fof(f29,plain,(
% 2.66/1.02    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.66/1.02    introduced(choice_axiom,[])).
% 2.66/1.02  
% 2.66/1.02  fof(f32,plain,(
% 2.66/1.02    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.66/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31,f30,f29])).
% 2.66/1.02  
% 2.66/1.02  fof(f54,plain,(
% 2.66/1.02    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 2.66/1.02    inference(cnf_transformation,[],[f32])).
% 2.66/1.02  
% 2.66/1.02  fof(f6,axiom,(
% 2.66/1.02    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.66/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.02  
% 2.66/1.02  fof(f19,plain,(
% 2.66/1.02    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.66/1.02    inference(ennf_transformation,[],[f6])).
% 2.66/1.02  
% 2.66/1.02  fof(f41,plain,(
% 2.66/1.02    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.66/1.02    inference(cnf_transformation,[],[f19])).
% 2.66/1.02  
% 2.66/1.02  fof(f48,plain,(
% 2.66/1.02    l1_struct_0(sK0)),
% 2.66/1.02    inference(cnf_transformation,[],[f32])).
% 2.66/1.02  
% 2.66/1.02  fof(f50,plain,(
% 2.66/1.02    l1_struct_0(sK1)),
% 2.66/1.02    inference(cnf_transformation,[],[f32])).
% 2.66/1.02  
% 2.66/1.02  fof(f7,axiom,(
% 2.66/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.66/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.02  
% 2.66/1.02  fof(f20,plain,(
% 2.66/1.02    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.66/1.02    inference(ennf_transformation,[],[f7])).
% 2.66/1.02  
% 2.66/1.02  fof(f21,plain,(
% 2.66/1.02    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.66/1.02    inference(flattening,[],[f20])).
% 2.66/1.02  
% 2.66/1.02  fof(f42,plain,(
% 2.66/1.02    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.66/1.02    inference(cnf_transformation,[],[f21])).
% 2.66/1.02  
% 2.66/1.02  fof(f51,plain,(
% 2.66/1.02    v1_funct_1(sK2)),
% 2.66/1.02    inference(cnf_transformation,[],[f32])).
% 2.66/1.02  
% 2.66/1.02  fof(f55,plain,(
% 2.66/1.02    v2_funct_1(sK2)),
% 2.66/1.02    inference(cnf_transformation,[],[f32])).
% 2.66/1.02  
% 2.66/1.02  fof(f53,plain,(
% 2.66/1.02    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.66/1.02    inference(cnf_transformation,[],[f32])).
% 2.66/1.02  
% 2.66/1.02  fof(f52,plain,(
% 2.66/1.02    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.66/1.02    inference(cnf_transformation,[],[f32])).
% 2.66/1.02  
% 2.66/1.02  fof(f5,axiom,(
% 2.66/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.66/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.02  
% 2.66/1.02  fof(f17,plain,(
% 2.66/1.02    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.66/1.02    inference(ennf_transformation,[],[f5])).
% 2.66/1.02  
% 2.66/1.02  fof(f18,plain,(
% 2.66/1.02    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.66/1.02    inference(flattening,[],[f17])).
% 2.66/1.02  
% 2.66/1.02  fof(f28,plain,(
% 2.66/1.02    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.66/1.02    inference(nnf_transformation,[],[f18])).
% 2.66/1.02  
% 2.66/1.02  fof(f40,plain,(
% 2.66/1.02    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.66/1.02    inference(cnf_transformation,[],[f28])).
% 2.66/1.02  
% 2.66/1.02  fof(f57,plain,(
% 2.66/1.02    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.66/1.02    inference(equality_resolution,[],[f40])).
% 2.66/1.02  
% 2.66/1.02  fof(f56,plain,(
% 2.66/1.02    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.66/1.02    inference(cnf_transformation,[],[f32])).
% 2.66/1.02  
% 2.66/1.02  fof(f3,axiom,(
% 2.66/1.02    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.66/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.02  
% 2.66/1.02  fof(f13,plain,(
% 2.66/1.02    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.66/1.02    inference(ennf_transformation,[],[f3])).
% 2.66/1.02  
% 2.66/1.02  fof(f14,plain,(
% 2.66/1.02    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/1.02    inference(flattening,[],[f13])).
% 2.66/1.02  
% 2.66/1.02  fof(f37,plain,(
% 2.66/1.02    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/1.02    inference(cnf_transformation,[],[f14])).
% 2.66/1.02  
% 2.66/1.02  fof(f36,plain,(
% 2.66/1.02    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/1.02    inference(cnf_transformation,[],[f14])).
% 2.66/1.02  
% 2.66/1.02  fof(f1,axiom,(
% 2.66/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.66/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.02  
% 2.66/1.02  fof(f12,plain,(
% 2.66/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.66/1.02    inference(ennf_transformation,[],[f1])).
% 2.66/1.02  
% 2.66/1.02  fof(f33,plain,(
% 2.66/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.66/1.02    inference(cnf_transformation,[],[f12])).
% 2.66/1.02  
% 2.66/1.02  fof(f2,axiom,(
% 2.66/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.66/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.02  
% 2.66/1.02  fof(f34,plain,(
% 2.66/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.66/1.02    inference(cnf_transformation,[],[f2])).
% 2.66/1.02  
% 2.66/1.02  fof(f8,axiom,(
% 2.66/1.02    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 2.66/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.02  
% 2.66/1.02  fof(f22,plain,(
% 2.66/1.02    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.66/1.02    inference(ennf_transformation,[],[f8])).
% 2.66/1.02  
% 2.66/1.02  fof(f23,plain,(
% 2.66/1.02    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.66/1.02    inference(flattening,[],[f22])).
% 2.66/1.02  
% 2.66/1.02  fof(f45,plain,(
% 2.66/1.02    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.66/1.02    inference(cnf_transformation,[],[f23])).
% 2.66/1.02  
% 2.66/1.02  fof(f44,plain,(
% 2.66/1.02    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.66/1.02    inference(cnf_transformation,[],[f23])).
% 2.66/1.02  
% 2.66/1.02  fof(f9,axiom,(
% 2.66/1.02    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 2.66/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.02  
% 2.66/1.02  fof(f24,plain,(
% 2.66/1.02    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 2.66/1.02    inference(ennf_transformation,[],[f9])).
% 2.66/1.02  
% 2.66/1.02  fof(f25,plain,(
% 2.66/1.02    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.66/1.02    inference(flattening,[],[f24])).
% 2.66/1.02  
% 2.66/1.02  fof(f47,plain,(
% 2.66/1.02    ( ! [X2,X0,X1] : (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.66/1.02    inference(cnf_transformation,[],[f25])).
% 2.66/1.02  
% 2.66/1.02  fof(f49,plain,(
% 2.66/1.02    ~v2_struct_0(sK1)),
% 2.66/1.02    inference(cnf_transformation,[],[f32])).
% 2.66/1.02  
% 2.66/1.02  fof(f4,axiom,(
% 2.66/1.02    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.66/1.02    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.66/1.02  
% 2.66/1.02  fof(f15,plain,(
% 2.66/1.02    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.66/1.02    inference(ennf_transformation,[],[f4])).
% 2.66/1.02  
% 2.66/1.02  fof(f16,plain,(
% 2.66/1.02    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.66/1.02    inference(flattening,[],[f15])).
% 2.66/1.02  
% 2.66/1.02  fof(f38,plain,(
% 2.66/1.02    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.66/1.02    inference(cnf_transformation,[],[f16])).
% 2.66/1.02  
% 2.66/1.02  fof(f43,plain,(
% 2.66/1.02    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.66/1.02    inference(cnf_transformation,[],[f23])).
% 2.66/1.02  
% 2.66/1.02  cnf(c_17,negated_conjecture,
% 2.66/1.02      ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
% 2.66/1.02      inference(cnf_transformation,[],[f54]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_633,negated_conjecture,
% 2.66/1.02      ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_17]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_8,plain,
% 2.66/1.02      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.66/1.02      inference(cnf_transformation,[],[f41]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_23,negated_conjecture,
% 2.66/1.02      ( l1_struct_0(sK0) ),
% 2.66/1.02      inference(cnf_transformation,[],[f48]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_458,plain,
% 2.66/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.66/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_23]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_459,plain,
% 2.66/1.02      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.66/1.02      inference(unflattening,[status(thm)],[c_458]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_623,plain,
% 2.66/1.02      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_459]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_21,negated_conjecture,
% 2.66/1.02      ( l1_struct_0(sK1) ),
% 2.66/1.02      inference(cnf_transformation,[],[f50]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_453,plain,
% 2.66/1.02      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.66/1.02      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_454,plain,
% 2.66/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.66/1.02      inference(unflattening,[status(thm)],[c_453]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_624,plain,
% 2.66/1.02      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_454]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1066,plain,
% 2.66/1.02      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.66/1.02      inference(light_normalisation,[status(thm)],[c_633,c_623,c_624]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_9,plain,
% 2.66/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.66/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.02      | ~ v1_funct_1(X0)
% 2.66/1.02      | ~ v2_funct_1(X0)
% 2.66/1.02      | k2_relset_1(X1,X2,X0) != X2
% 2.66/1.02      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0) ),
% 2.66/1.02      inference(cnf_transformation,[],[f42]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_638,plain,
% 2.66/1.02      ( ~ v1_funct_2(X0_49,X0_47,X1_47)
% 2.66/1.02      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.66/1.02      | ~ v1_funct_1(X0_49)
% 2.66/1.02      | ~ v2_funct_1(X0_49)
% 2.66/1.02      | k2_tops_2(X0_47,X1_47,X0_49) = k2_funct_1(X0_49)
% 2.66/1.02      | k2_relset_1(X0_47,X1_47,X0_49) != X1_47 ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_9]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1040,plain,
% 2.66/1.02      ( k2_tops_2(X0_47,X1_47,X0_49) = k2_funct_1(X0_49)
% 2.66/1.02      | k2_relset_1(X0_47,X1_47,X0_49) != X1_47
% 2.66/1.02      | v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
% 2.66/1.02      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.66/1.02      | v1_funct_1(X0_49) != iProver_top
% 2.66/1.02      | v2_funct_1(X0_49) != iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_638]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1726,plain,
% 2.66/1.02      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.66/1.02      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.66/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.66/1.02      | v1_funct_1(sK2) != iProver_top
% 2.66/1.02      | v2_funct_1(sK2) != iProver_top ),
% 2.66/1.02      inference(superposition,[status(thm)],[c_1066,c_1040]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_20,negated_conjecture,
% 2.66/1.02      ( v1_funct_1(sK2) ),
% 2.66/1.02      inference(cnf_transformation,[],[f51]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_27,plain,
% 2.66/1.02      ( v1_funct_1(sK2) = iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_16,negated_conjecture,
% 2.66/1.02      ( v2_funct_1(sK2) ),
% 2.66/1.02      inference(cnf_transformation,[],[f55]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_30,plain,
% 2.66/1.02      ( v2_funct_1(sK2) = iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_18,negated_conjecture,
% 2.66/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.66/1.02      inference(cnf_transformation,[],[f53]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_632,negated_conjecture,
% 2.66/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_18]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1045,plain,
% 2.66/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1069,plain,
% 2.66/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.66/1.02      inference(light_normalisation,[status(thm)],[c_1045,c_623,c_624]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_19,negated_conjecture,
% 2.66/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.66/1.02      inference(cnf_transformation,[],[f52]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_631,negated_conjecture,
% 2.66/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_19]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1046,plain,
% 2.66/1.02      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1063,plain,
% 2.66/1.02      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.66/1.02      inference(light_normalisation,[status(thm)],[c_1046,c_623,c_624]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_2049,plain,
% 2.66/1.02      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.66/1.02      inference(global_propositional_subsumption,
% 2.66/1.02                [status(thm)],
% 2.66/1.02                [c_1726,c_27,c_30,c_1069,c_1063]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_6,plain,
% 2.66/1.02      ( r2_funct_2(X0,X1,X2,X2)
% 2.66/1.02      | ~ v1_funct_2(X2,X0,X1)
% 2.66/1.02      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.66/1.02      | ~ v1_funct_1(X2) ),
% 2.66/1.02      inference(cnf_transformation,[],[f57]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_15,negated_conjecture,
% 2.66/1.02      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.66/1.02      inference(cnf_transformation,[],[f56]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_258,plain,
% 2.66/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.66/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.02      | ~ v1_funct_1(X0)
% 2.66/1.02      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.66/1.02      | u1_struct_0(sK1) != X2
% 2.66/1.02      | u1_struct_0(sK0) != X1
% 2.66/1.02      | sK2 != X0 ),
% 2.66/1.02      inference(resolution_lifted,[status(thm)],[c_6,c_15]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_259,plain,
% 2.66/1.02      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.66/1.02      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.66/1.02      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.66/1.02      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.66/1.02      inference(unflattening,[status(thm)],[c_258]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_629,plain,
% 2.66/1.02      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.66/1.02      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.66/1.02      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.66/1.02      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_259]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1048,plain,
% 2.66/1.02      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.66/1.02      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.66/1.02      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.66/1.02      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1198,plain,
% 2.66/1.02      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.66/1.02      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.66/1.02      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.66/1.02      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.66/1.02      inference(light_normalisation,[status(thm)],[c_1048,c_623,c_624]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_2052,plain,
% 2.66/1.02      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.66/1.02      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.66/1.02      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.66/1.02      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.66/1.02      inference(demodulation,[status(thm)],[c_2049,c_1198]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_29,plain,
% 2.66/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_2,plain,
% 2.66/1.02      ( ~ v1_funct_1(X0)
% 2.66/1.02      | ~ v2_funct_1(X0)
% 2.66/1.02      | v2_funct_1(k2_funct_1(X0))
% 2.66/1.02      | ~ v1_relat_1(X0) ),
% 2.66/1.02      inference(cnf_transformation,[],[f37]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_642,plain,
% 2.66/1.02      ( ~ v1_funct_1(X0_49)
% 2.66/1.02      | ~ v2_funct_1(X0_49)
% 2.66/1.02      | v2_funct_1(k2_funct_1(X0_49))
% 2.66/1.02      | ~ v1_relat_1(X0_49) ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_2]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_681,plain,
% 2.66/1.02      ( v1_funct_1(X0_49) != iProver_top
% 2.66/1.02      | v2_funct_1(X0_49) != iProver_top
% 2.66/1.02      | v2_funct_1(k2_funct_1(X0_49)) = iProver_top
% 2.66/1.02      | v1_relat_1(X0_49) != iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_642]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_683,plain,
% 2.66/1.02      ( v1_funct_1(sK2) != iProver_top
% 2.66/1.02      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.66/1.02      | v2_funct_1(sK2) != iProver_top
% 2.66/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.66/1.02      inference(instantiation,[status(thm)],[c_681]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_3,plain,
% 2.66/1.02      ( ~ v1_funct_1(X0)
% 2.66/1.02      | v1_funct_1(k2_funct_1(X0))
% 2.66/1.02      | ~ v2_funct_1(X0)
% 2.66/1.02      | ~ v1_relat_1(X0) ),
% 2.66/1.02      inference(cnf_transformation,[],[f36]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_641,plain,
% 2.66/1.02      ( ~ v1_funct_1(X0_49)
% 2.66/1.02      | v1_funct_1(k2_funct_1(X0_49))
% 2.66/1.02      | ~ v2_funct_1(X0_49)
% 2.66/1.02      | ~ v1_relat_1(X0_49) ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_3]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_684,plain,
% 2.66/1.02      ( v1_funct_1(X0_49) != iProver_top
% 2.66/1.02      | v1_funct_1(k2_funct_1(X0_49)) = iProver_top
% 2.66/1.02      | v2_funct_1(X0_49) != iProver_top
% 2.66/1.02      | v1_relat_1(X0_49) != iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_641]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_686,plain,
% 2.66/1.02      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.66/1.02      | v1_funct_1(sK2) != iProver_top
% 2.66/1.02      | v2_funct_1(sK2) != iProver_top
% 2.66/1.02      | v1_relat_1(sK2) != iProver_top ),
% 2.66/1.02      inference(instantiation,[status(thm)],[c_684]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_0,plain,
% 2.66/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.66/1.02      inference(cnf_transformation,[],[f33]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_644,plain,
% 2.66/1.02      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(X1_49))
% 2.66/1.02      | ~ v1_relat_1(X1_49)
% 2.66/1.02      | v1_relat_1(X0_49) ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_0]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1277,plain,
% 2.66/1.02      ( ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.66/1.02      | v1_relat_1(X0_49)
% 2.66/1.02      | ~ v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 2.66/1.02      inference(instantiation,[status(thm)],[c_644]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1382,plain,
% 2.66/1.02      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.66/1.02      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.66/1.02      | v1_relat_1(sK2) ),
% 2.66/1.02      inference(instantiation,[status(thm)],[c_1277]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1383,plain,
% 2.66/1.02      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.66/1.02      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.66/1.02      | v1_relat_1(sK2) = iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_1382]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1,plain,
% 2.66/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.66/1.02      inference(cnf_transformation,[],[f34]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_643,plain,
% 2.66/1.02      ( v1_relat_1(k2_zfmisc_1(X0_47,X1_47)) ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_1]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1411,plain,
% 2.66/1.02      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.66/1.02      inference(instantiation,[status(thm)],[c_643]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1412,plain,
% 2.66/1.02      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_1411]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_10,plain,
% 2.66/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.66/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.02      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.66/1.02      | ~ v1_funct_1(X0) ),
% 2.66/1.02      inference(cnf_transformation,[],[f45]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_637,plain,
% 2.66/1.02      ( ~ v1_funct_2(X0_49,X0_47,X1_47)
% 2.66/1.02      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.66/1.02      | m1_subset_1(k2_tops_2(X0_47,X1_47,X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_47)))
% 2.66/1.02      | ~ v1_funct_1(X0_49) ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_10]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1041,plain,
% 2.66/1.02      ( v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
% 2.66/1.02      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.66/1.02      | m1_subset_1(k2_tops_2(X0_47,X1_47,X0_49),k1_zfmisc_1(k2_zfmisc_1(X1_47,X0_47))) = iProver_top
% 2.66/1.02      | v1_funct_1(X0_49) != iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_2068,plain,
% 2.66/1.02      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.66/1.02      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.66/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.66/1.02      | v1_funct_1(sK2) != iProver_top ),
% 2.66/1.02      inference(superposition,[status(thm)],[c_2049,c_1041]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_11,plain,
% 2.66/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 2.66/1.02      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 2.66/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.02      | ~ v1_funct_1(X0) ),
% 2.66/1.02      inference(cnf_transformation,[],[f44]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_636,plain,
% 2.66/1.02      ( ~ v1_funct_2(X0_49,X0_47,X1_47)
% 2.66/1.02      | v1_funct_2(k2_tops_2(X0_47,X1_47,X0_49),X1_47,X0_47)
% 2.66/1.02      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.66/1.02      | ~ v1_funct_1(X0_49) ),
% 2.66/1.02      inference(subtyping,[status(esa)],[c_11]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_1042,plain,
% 2.66/1.02      ( v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
% 2.66/1.02      | v1_funct_2(k2_tops_2(X0_47,X1_47,X0_49),X1_47,X0_47) = iProver_top
% 2.66/1.02      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.66/1.02      | v1_funct_1(X0_49) != iProver_top ),
% 2.66/1.02      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_2069,plain,
% 2.66/1.02      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.66/1.02      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.66/1.02      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.66/1.02      | v1_funct_1(sK2) != iProver_top ),
% 2.66/1.02      inference(superposition,[status(thm)],[c_2049,c_1042]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_13,plain,
% 2.66/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.66/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.66/1.02      | v2_struct_0(X2)
% 2.66/1.02      | ~ l1_struct_0(X1)
% 2.66/1.02      | ~ l1_struct_0(X2)
% 2.66/1.02      | ~ v1_funct_1(X0)
% 2.66/1.02      | ~ v2_funct_1(X0)
% 2.66/1.02      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.66/1.02      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 2.66/1.02      inference(cnf_transformation,[],[f47]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_22,negated_conjecture,
% 2.66/1.02      ( ~ v2_struct_0(sK1) ),
% 2.66/1.02      inference(cnf_transformation,[],[f49]) ).
% 2.66/1.02  
% 2.66/1.02  cnf(c_310,plain,
% 2.66/1.02      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.66/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.66/1.02      | ~ l1_struct_0(X1)
% 2.66/1.02      | ~ l1_struct_0(X2)
% 2.66/1.02      | ~ v1_funct_1(X0)
% 2.66/1.02      | ~ v2_funct_1(X0)
% 2.66/1.02      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.66/1.02      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 2.66/1.03      | sK1 != X2 ),
% 2.66/1.03      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_311,plain,
% 2.66/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.66/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.66/1.03      | ~ l1_struct_0(X1)
% 2.66/1.03      | ~ l1_struct_0(sK1)
% 2.66/1.03      | ~ v1_funct_1(X0)
% 2.66/1.03      | ~ v2_funct_1(X0)
% 2.66/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.66/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.66/1.03      inference(unflattening,[status(thm)],[c_310]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_315,plain,
% 2.66/1.03      ( ~ l1_struct_0(X1)
% 2.66/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.66/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.66/1.03      | ~ v1_funct_1(X0)
% 2.66/1.03      | ~ v2_funct_1(X0)
% 2.66/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.66/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.66/1.03      inference(global_propositional_subsumption,[status(thm)],[c_311,c_21]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_316,plain,
% 2.66/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.66/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.66/1.03      | ~ l1_struct_0(X1)
% 2.66/1.03      | ~ v1_funct_1(X0)
% 2.66/1.03      | ~ v2_funct_1(X0)
% 2.66/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.66/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.66/1.03      inference(renaming,[status(thm)],[c_315]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_405,plain,
% 2.66/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.66/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.66/1.03      | ~ v1_funct_1(X0)
% 2.66/1.03      | ~ v2_funct_1(X0)
% 2.66/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.66/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1)
% 2.66/1.03      | sK0 != X1 ),
% 2.66/1.03      inference(resolution_lifted,[status(thm)],[c_316,c_23]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_406,plain,
% 2.66/1.03      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.66/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.66/1.03      | ~ v1_funct_1(X0)
% 2.66/1.03      | ~ v2_funct_1(X0)
% 2.66/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK0)
% 2.66/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.66/1.03      inference(unflattening,[status(thm)],[c_405]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_626,plain,
% 2.66/1.03      ( ~ v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.66/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.66/1.03      | ~ v1_funct_1(X0_49)
% 2.66/1.03      | ~ v2_funct_1(X0_49)
% 2.66/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
% 2.66/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1) ),
% 2.66/1.03      inference(subtyping,[status(esa)],[c_406]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_1051,plain,
% 2.66/1.03      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
% 2.66/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_49) != k2_struct_0(sK1)
% 2.66/1.03      | v1_funct_2(X0_49,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.66/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.66/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.66/1.03      | v2_funct_1(X0_49) != iProver_top ),
% 2.66/1.03      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_1172,plain,
% 2.66/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_49)) = k2_struct_0(sK0)
% 2.66/1.03      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_49) != k2_struct_0(sK1)
% 2.66/1.03      | v1_funct_2(X0_49,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.66/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.66/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.66/1.03      | v2_funct_1(X0_49) != iProver_top ),
% 2.66/1.03      inference(light_normalisation,[status(thm)],[c_1051,c_623,c_624]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_1527,plain,
% 2.66/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.66/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.66/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.66/1.03      | v1_funct_1(sK2) != iProver_top
% 2.66/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.66/1.03      inference(superposition,[status(thm)],[c_1066,c_1172]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_1228,plain,
% 2.66/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.66/1.03      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.66/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.66/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.66/1.03      | v1_funct_1(sK2) != iProver_top
% 2.66/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.66/1.03      inference(instantiation,[status(thm)],[c_1172]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_1530,plain,
% 2.66/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0) ),
% 2.66/1.03      inference(global_propositional_subsumption,
% 2.66/1.03                [status(thm)],
% 2.66/1.03                [c_1527,c_27,c_30,c_1069,c_1063,c_1228,c_1066]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_2054,plain,
% 2.66/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 2.66/1.03      inference(demodulation,[status(thm)],[c_2049,c_1530]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_2129,plain,
% 2.66/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.66/1.03      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.66/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.66/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.66/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.66/1.03      inference(superposition,[status(thm)],[c_2054,c_1040]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_630,negated_conjecture,
% 2.66/1.03      ( v1_funct_1(sK2) ),
% 2.66/1.03      inference(subtyping,[status(esa)],[c_20]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_1047,plain,
% 2.66/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 2.66/1.03      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_5,plain,
% 2.66/1.03      ( ~ v1_funct_1(X0)
% 2.66/1.03      | ~ v2_funct_1(X0)
% 2.66/1.03      | ~ v1_relat_1(X0)
% 2.66/1.03      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.66/1.03      inference(cnf_transformation,[],[f38]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_639,plain,
% 2.66/1.03      ( ~ v1_funct_1(X0_49)
% 2.66/1.03      | ~ v2_funct_1(X0_49)
% 2.66/1.03      | ~ v1_relat_1(X0_49)
% 2.66/1.03      | k2_funct_1(k2_funct_1(X0_49)) = X0_49 ),
% 2.66/1.03      inference(subtyping,[status(esa)],[c_5]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_1039,plain,
% 2.66/1.03      ( k2_funct_1(k2_funct_1(X0_49)) = X0_49
% 2.66/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.66/1.03      | v2_funct_1(X0_49) != iProver_top
% 2.66/1.03      | v1_relat_1(X0_49) != iProver_top ),
% 2.66/1.03      inference(predicate_to_equality,[status(thm)],[c_639]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_1695,plain,
% 2.66/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.66/1.03      | v2_funct_1(sK2) != iProver_top
% 2.66/1.03      | v1_relat_1(sK2) != iProver_top ),
% 2.66/1.03      inference(superposition,[status(thm)],[c_1047,c_1039]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_691,plain,
% 2.66/1.03      ( ~ v1_funct_1(sK2)
% 2.66/1.03      | ~ v2_funct_1(sK2)
% 2.66/1.03      | ~ v1_relat_1(sK2)
% 2.66/1.03      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.66/1.03      inference(instantiation,[status(thm)],[c_639]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_1962,plain,
% 2.66/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.66/1.03      inference(global_propositional_subsumption,
% 2.66/1.03                [status(thm)],
% 2.66/1.03                [c_1695,c_20,c_18,c_16,c_691,c_1382,c_1411]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_2130,plain,
% 2.66/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.66/1.03      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.66/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.66/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.66/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.66/1.03      inference(light_normalisation,[status(thm)],[c_2129,c_1962]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_2206,plain,
% 2.66/1.03      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top ),
% 2.66/1.03      inference(global_propositional_subsumption,
% 2.66/1.03                [status(thm)],
% 2.66/1.03                [c_2068,c_27,c_1069,c_1063]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_12,plain,
% 2.66/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.66/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.66/1.03      | ~ v1_funct_1(X0)
% 2.66/1.03      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 2.66/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_635,plain,
% 2.66/1.03      ( ~ v1_funct_2(X0_49,X0_47,X1_47)
% 2.66/1.03      | ~ m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47)))
% 2.66/1.03      | ~ v1_funct_1(X0_49)
% 2.66/1.03      | v1_funct_1(k2_tops_2(X0_47,X1_47,X0_49)) ),
% 2.66/1.03      inference(subtyping,[status(esa)],[c_12]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_1043,plain,
% 2.66/1.03      ( v1_funct_2(X0_49,X0_47,X1_47) != iProver_top
% 2.66/1.03      | m1_subset_1(X0_49,k1_zfmisc_1(k2_zfmisc_1(X0_47,X1_47))) != iProver_top
% 2.66/1.03      | v1_funct_1(X0_49) != iProver_top
% 2.66/1.03      | v1_funct_1(k2_tops_2(X0_47,X1_47,X0_49)) = iProver_top ),
% 2.66/1.03      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_2211,plain,
% 2.66/1.03      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.66/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
% 2.66/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.66/1.03      inference(superposition,[status(thm)],[c_2206,c_1043]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_2315,plain,
% 2.66/1.03      ( m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.66/1.03      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top ),
% 2.66/1.03      inference(global_propositional_subsumption,
% 2.66/1.03                [status(thm)],
% 2.66/1.03                [c_2052,c_27,c_29,c_30,c_683,c_686,c_1069,c_1063,c_1383,
% 2.66/1.03                 c_1412,c_2068,c_2069,c_2130,c_2211]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_2316,plain,
% 2.66/1.03      ( v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.66/1.03      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.66/1.03      inference(renaming,[status(thm)],[c_2315]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_2309,plain,
% 2.66/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.66/1.03      inference(global_propositional_subsumption,
% 2.66/1.03                [status(thm)],
% 2.66/1.03                [c_2130,c_27,c_29,c_30,c_683,c_686,c_1069,c_1063,c_1383,
% 2.66/1.03                 c_1412,c_2068,c_2069]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_2319,plain,
% 2.66/1.03      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.66/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.66/1.03      inference(light_normalisation,[status(thm)],[c_2316,c_2309]) ).
% 2.66/1.03  
% 2.66/1.03  cnf(c_2322,plain,
% 2.66/1.03      ( $false ),
% 2.66/1.03      inference(forward_subsumption_resolution,
% 2.66/1.03                [status(thm)],
% 2.66/1.03                [c_2319,c_1069,c_1063]) ).
% 2.66/1.03  
% 2.66/1.03  
% 2.66/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.66/1.03  
% 2.66/1.03  ------                               Statistics
% 2.66/1.03  
% 2.66/1.03  ------ General
% 2.66/1.03  
% 2.66/1.03  abstr_ref_over_cycles:                  0
% 2.66/1.03  abstr_ref_under_cycles:                 0
% 2.66/1.03  gc_basic_clause_elim:                   0
% 2.66/1.03  forced_gc_time:                         0
% 2.66/1.03  parsing_time:                           0.012
% 2.66/1.03  unif_index_cands_time:                  0.
% 2.66/1.03  unif_index_add_time:                    0.
% 2.66/1.03  orderings_time:                         0.
% 2.66/1.03  out_proof_time:                         0.009
% 2.66/1.03  total_time:                             0.222
% 2.66/1.03  num_of_symbols:                         51
% 2.66/1.03  num_of_terms:                           2253
% 2.66/1.03  
% 2.66/1.03  ------ Preprocessing
% 2.66/1.03  
% 2.66/1.03  num_of_splits:                          0
% 2.66/1.03  num_of_split_atoms:                     0
% 2.66/1.03  num_of_reused_defs:                     0
% 2.66/1.03  num_eq_ax_congr_red:                    2
% 2.66/1.03  num_of_sem_filtered_clauses:            1
% 2.66/1.03  num_of_subtypes:                        4
% 2.66/1.03  monotx_restored_types:                  0
% 2.66/1.03  sat_num_of_epr_types:                   0
% 2.66/1.03  sat_num_of_non_cyclic_types:            0
% 2.66/1.03  sat_guarded_non_collapsed_types:        1
% 2.66/1.03  num_pure_diseq_elim:                    0
% 2.66/1.03  simp_replaced_by:                       0
% 2.66/1.03  res_preprocessed:                       123
% 2.66/1.03  prep_upred:                             0
% 2.66/1.03  prep_unflattend:                        15
% 2.66/1.03  smt_new_axioms:                         0
% 2.66/1.03  pred_elim_cands:                        5
% 2.66/1.03  pred_elim:                              3
% 2.66/1.03  pred_elim_cl:                           2
% 2.66/1.03  pred_elim_cycles:                       5
% 2.66/1.03  merged_defs:                            0
% 2.66/1.03  merged_defs_ncl:                        0
% 2.66/1.03  bin_hyper_res:                          0
% 2.66/1.03  prep_cycles:                            4
% 2.66/1.03  pred_elim_time:                         0.007
% 2.66/1.03  splitting_time:                         0.
% 2.66/1.03  sem_filter_time:                        0.
% 2.66/1.03  monotx_time:                            0.
% 2.66/1.03  subtype_inf_time:                       0.001
% 2.66/1.03  
% 2.66/1.03  ------ Problem properties
% 2.66/1.03  
% 2.66/1.03  clauses:                                22
% 2.66/1.03  conjectures:                            5
% 2.66/1.03  epr:                                    2
% 2.66/1.03  horn:                                   22
% 2.66/1.03  ground:                                 8
% 2.66/1.03  unary:                                  8
% 2.66/1.03  binary:                                 0
% 2.66/1.03  lits:                                   73
% 2.66/1.03  lits_eq:                                15
% 2.66/1.03  fd_pure:                                0
% 2.66/1.03  fd_pseudo:                              0
% 2.66/1.03  fd_cond:                                0
% 2.66/1.03  fd_pseudo_cond:                         0
% 2.66/1.03  ac_symbols:                             0
% 2.66/1.03  
% 2.66/1.03  ------ Propositional Solver
% 2.66/1.03  
% 2.66/1.03  prop_solver_calls:                      27
% 2.66/1.03  prop_fast_solver_calls:                 969
% 2.66/1.03  smt_solver_calls:                       0
% 2.66/1.03  smt_fast_solver_calls:                  0
% 2.66/1.03  prop_num_of_clauses:                    734
% 2.66/1.03  prop_preprocess_simplified:             3486
% 2.66/1.03  prop_fo_subsumed:                       31
% 2.66/1.03  prop_solver_time:                       0.
% 2.66/1.03  smt_solver_time:                        0.
% 2.66/1.03  smt_fast_solver_time:                   0.
% 2.66/1.03  prop_fast_solver_time:                  0.
% 2.66/1.03  prop_unsat_core_time:                   0.
% 2.66/1.03  
% 2.66/1.03  ------ QBF
% 2.66/1.03  
% 2.66/1.03  qbf_q_res:                              0
% 2.66/1.03  qbf_num_tautologies:                    0
% 2.66/1.03  qbf_prep_cycles:                        0
% 2.66/1.03  
% 2.66/1.03  ------ BMC1
% 2.66/1.03  
% 2.66/1.03  bmc1_current_bound:                     -1
% 2.66/1.03  bmc1_last_solved_bound:                 -1
% 2.66/1.03  bmc1_unsat_core_size:                   -1
% 2.66/1.03  bmc1_unsat_core_parents_size:           -1
% 2.66/1.03  bmc1_merge_next_fun:                    0
% 2.66/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.66/1.03  
% 2.66/1.03  ------ Instantiation
% 2.66/1.03  
% 2.66/1.03  inst_num_of_clauses:                    240
% 2.66/1.03  inst_num_in_passive:                    5
% 2.66/1.03  inst_num_in_active:                     153
% 2.66/1.03  inst_num_in_unprocessed:                82
% 2.66/1.03  inst_num_of_loops:                      170
% 2.66/1.03  inst_num_of_learning_restarts:          0
% 2.66/1.03  inst_num_moves_active_passive:          14
% 2.66/1.03  inst_lit_activity:                      0
% 2.66/1.03  inst_lit_activity_moves:                0
% 2.66/1.03  inst_num_tautologies:                   0
% 2.66/1.03  inst_num_prop_implied:                  0
% 2.66/1.03  inst_num_existing_simplified:           0
% 2.66/1.03  inst_num_eq_res_simplified:             0
% 2.66/1.03  inst_num_child_elim:                    0
% 2.66/1.03  inst_num_of_dismatching_blockings:      19
% 2.66/1.03  inst_num_of_non_proper_insts:           193
% 2.66/1.03  inst_num_of_duplicates:                 0
% 2.66/1.03  inst_inst_num_from_inst_to_res:         0
% 2.66/1.03  inst_dismatching_checking_time:         0.
% 2.66/1.03  
% 2.66/1.03  ------ Resolution
% 2.66/1.03  
% 2.66/1.03  res_num_of_clauses:                     0
% 2.66/1.03  res_num_in_passive:                     0
% 2.66/1.03  res_num_in_active:                      0
% 2.66/1.03  res_num_of_loops:                       127
% 2.66/1.03  res_forward_subset_subsumed:            27
% 2.66/1.03  res_backward_subset_subsumed:           0
% 2.66/1.03  res_forward_subsumed:                   0
% 2.66/1.03  res_backward_subsumed:                  0
% 2.66/1.03  res_forward_subsumption_resolution:     0
% 2.66/1.03  res_backward_subsumption_resolution:    0
% 2.66/1.03  res_clause_to_clause_subsumption:       55
% 2.66/1.03  res_orphan_elimination:                 0
% 2.66/1.03  res_tautology_del:                      28
% 2.66/1.03  res_num_eq_res_simplified:              0
% 2.66/1.03  res_num_sel_changes:                    0
% 2.66/1.03  res_moves_from_active_to_pass:          0
% 2.66/1.03  
% 2.66/1.03  ------ Superposition
% 2.66/1.03  
% 2.66/1.03  sup_time_total:                         0.
% 2.66/1.03  sup_time_generating:                    0.
% 2.66/1.03  sup_time_sim_full:                      0.
% 2.66/1.03  sup_time_sim_immed:                     0.
% 2.66/1.03  
% 2.66/1.03  sup_num_of_clauses:                     36
% 2.66/1.03  sup_num_in_active:                      30
% 2.66/1.03  sup_num_in_passive:                     6
% 2.66/1.03  sup_num_of_loops:                       33
% 2.66/1.03  sup_fw_superposition:                   8
% 2.66/1.03  sup_bw_superposition:                   13
% 2.66/1.03  sup_immediate_simplified:               7
% 2.66/1.03  sup_given_eliminated:                   0
% 2.66/1.03  comparisons_done:                       0
% 2.66/1.03  comparisons_avoided:                    0
% 2.66/1.03  
% 2.66/1.03  ------ Simplifications
% 2.66/1.03  
% 2.66/1.03  
% 2.66/1.03  sim_fw_subset_subsumed:                 5
% 2.66/1.03  sim_bw_subset_subsumed:                 0
% 2.66/1.03  sim_fw_subsumed:                        0
% 2.66/1.03  sim_bw_subsumed:                        0
% 2.66/1.03  sim_fw_subsumption_res:                 2
% 2.66/1.03  sim_bw_subsumption_res:                 0
% 2.66/1.03  sim_tautology_del:                      0
% 2.66/1.03  sim_eq_tautology_del:                   1
% 2.66/1.03  sim_eq_res_simp:                        0
% 2.66/1.03  sim_fw_demodulated:                     0
% 2.66/1.03  sim_bw_demodulated:                     3
% 2.66/1.03  sim_light_normalised:                   12
% 2.66/1.03  sim_joinable_taut:                      0
% 2.66/1.03  sim_joinable_simp:                      0
% 2.66/1.03  sim_ac_normalised:                      0
% 2.66/1.03  sim_smt_subsumption:                    0
% 2.66/1.03  
%------------------------------------------------------------------------------
