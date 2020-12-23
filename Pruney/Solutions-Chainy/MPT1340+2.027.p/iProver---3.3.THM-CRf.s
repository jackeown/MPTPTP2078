%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:26 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  199 (7368 expanded)
%              Number of clauses        :  131 (2236 expanded)
%              Number of leaves         :   21 (2152 expanded)
%              Depth                    :   21
%              Number of atoms          :  712 (47210 expanded)
%              Number of equality atoms :  317 (8498 expanded)
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f36,plain,(
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

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f42,plain,(
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

fof(f41,plain,(
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

fof(f40,plain,
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

fof(f43,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f42,f41,f40])).

fof(f66,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f59,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f68,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f30])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f69,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f73,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f39,plain,(
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
    inference(nnf_transformation,[],[f26])).

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
    inference(cnf_transformation,[],[f39])).

fof(f80,plain,(
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
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
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

fof(f35,plain,(
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
    inference(flattening,[],[f34])).

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
    inference(cnf_transformation,[],[f35])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f60,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f67,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f17,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f46,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f19,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f47,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

cnf(c_30,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1139,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_15,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1150,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1484,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1139,c_1150])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1140,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_1483,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1140,c_1150])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1775,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1483,c_24])).

cnf(c_1877,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1484,c_1775])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1143,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1157,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_1587,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1143,c_1157])).

cnf(c_1953,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1587,c_1483,c_1484])).

cnf(c_2369,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1877,c_1953])).

cnf(c_2372,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2369,c_1953])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1149,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3824,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2372,c_1149])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_34,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_23,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_37,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1142,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1773,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1483,c_1142])).

cnf(c_1950,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1773,c_1484])).

cnf(c_2373,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2369,c_1950])).

cnf(c_1772,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1483,c_1143])).

cnf(c_2388,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1772,c_1484,c_2369])).

cnf(c_4575,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3824,c_34,c_37,c_2373,c_2388])).

cnf(c_13,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_22,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_430,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_431,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_430])).

cnf(c_1138,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_431])).

cnf(c_1771,plain,
    ( k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1483,c_1138])).

cnf(c_3456,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1771,c_1484,c_2369])).

cnf(c_4580,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4575,c_3456])).

cnf(c_31,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_33,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_35,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_36,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1379,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1427,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_tops_2(X0,X1,sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1533,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1427])).

cnf(c_1534,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1533])).

cnf(c_1451,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_1576,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1451])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1461,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X0))
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1598,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0))
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_1696,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1598])).

cnf(c_1697,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1696])).

cnf(c_682,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1683,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_682])).

cnf(c_2151,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1683])).

cnf(c_2138,plain,
    ( X0 != X1
    | X0 = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_682])).

cnf(c_2856,plain,
    ( X0 = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | X0 != k2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_3323,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2856])).

cnf(c_681,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3324,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1158,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1705,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1143,c_1158])).

cnf(c_2031,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1705,c_1483,c_1484])).

cnf(c_2371,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2369,c_2031])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1151,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3050,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
    | k2_relat_1(sK2) = k1_xboole_0
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2388,c_1151])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_16,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_338,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_16])).

cnf(c_29,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_356,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) != k1_xboole_0
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_338,c_29])).

cnf(c_357,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_356])).

cnf(c_359,plain,
    ( u1_struct_0(sK1) != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_357,c_28])).

cnf(c_1774,plain,
    ( k2_struct_0(sK1) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1483,c_359])).

cnf(c_2374,plain,
    ( k2_relat_1(sK2) != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_2369,c_1774])).

cnf(c_3802,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3050,c_2373,c_2374])).

cnf(c_3821,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2371,c_3802])).

cnf(c_687,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1643,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | X0 != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_687])).

cnf(c_3903,plain,
    ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1643])).

cnf(c_3904,plain,
    ( k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3903])).

cnf(c_686,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1944,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | X0 != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_686])).

cnf(c_3902,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_1944])).

cnf(c_3906,plain,
    ( k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3902])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1148,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_1146,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3627,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) != iProver_top
    | v1_funct_1(k2_tops_2(X2,X1,k2_tops_2(X1,X2,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_1146])).

cnf(c_42,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_45,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4122,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_1(k2_tops_2(X2,X1,k2_tops_2(X1,X2,X0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3627,c_42,c_45])).

cnf(c_4123,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_tops_2(X2,X1,k2_tops_2(X1,X2,X0))) = iProver_top ),
    inference(renaming,[status(thm)],[c_4122])).

cnf(c_4596,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4575,c_4123])).

cnf(c_4597,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4575,c_1148])).

cnf(c_1147,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4598,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4575,c_1147])).

cnf(c_3632,plain,
    ( k2_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = k2_relat_1(k2_tops_2(X1,X0,X2))
    | v1_funct_2(X2,X1,X0) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1148,c_1157])).

cnf(c_4551,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2388,c_3632])).

cnf(c_4773,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4551,c_34,c_2373])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1159,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_1582,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1143,c_1159])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1162,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2902,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_1162])).

cnf(c_1385,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1468,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_3159,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2902,c_27,c_25,c_23,c_1385,c_1468])).

cnf(c_4775,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4773,c_3159,c_4575])).

cnf(c_4777,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4775,c_1149])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1160,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2221,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1582,c_1160])).

cnf(c_1466,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2520,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2221,c_27,c_25,c_23,c_1385,c_1466])).

cnf(c_4797,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4777,c_2520])).

cnf(c_4851,plain,
    ( m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4580,c_31,c_28,c_33,c_27,c_34,c_26,c_35,c_25,c_36,c_24,c_23,c_37,c_1379,c_1534,c_1576,c_1697,c_2151,c_2373,c_2388,c_3323,c_3324,c_3821,c_3904,c_3906,c_4596,c_4597,c_4598,c_4797])).

cnf(c_4852,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_4851])).

cnf(c_4807,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4797,c_31,c_28,c_33,c_27,c_34,c_26,c_35,c_25,c_36,c_24,c_23,c_37,c_1379,c_1534,c_1576,c_1697,c_2151,c_2373,c_2388,c_3323,c_3324,c_3821,c_3904,c_3906,c_4597,c_4598])).

cnf(c_4855,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4852,c_4807])).

cnf(c_4858,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4855,c_2388,c_2373])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:08:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.02/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/0.99  
% 3.02/0.99  ------  iProver source info
% 3.02/0.99  
% 3.02/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.02/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/0.99  git: non_committed_changes: false
% 3.02/0.99  git: last_make_outside_of_git: false
% 3.02/0.99  
% 3.02/0.99  ------ 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options
% 3.02/0.99  
% 3.02/0.99  --out_options                           all
% 3.02/0.99  --tptp_safe_out                         true
% 3.02/0.99  --problem_path                          ""
% 3.02/0.99  --include_path                          ""
% 3.02/0.99  --clausifier                            res/vclausify_rel
% 3.02/0.99  --clausifier_options                    --mode clausify
% 3.02/0.99  --stdin                                 false
% 3.02/0.99  --stats_out                             all
% 3.02/0.99  
% 3.02/0.99  ------ General Options
% 3.02/0.99  
% 3.02/0.99  --fof                                   false
% 3.02/0.99  --time_out_real                         305.
% 3.02/0.99  --time_out_virtual                      -1.
% 3.02/0.99  --symbol_type_check                     false
% 3.02/0.99  --clausify_out                          false
% 3.02/0.99  --sig_cnt_out                           false
% 3.02/0.99  --trig_cnt_out                          false
% 3.02/0.99  --trig_cnt_out_tolerance                1.
% 3.02/0.99  --trig_cnt_out_sk_spl                   false
% 3.02/0.99  --abstr_cl_out                          false
% 3.02/0.99  
% 3.02/0.99  ------ Global Options
% 3.02/0.99  
% 3.02/0.99  --schedule                              default
% 3.02/0.99  --add_important_lit                     false
% 3.02/0.99  --prop_solver_per_cl                    1000
% 3.02/0.99  --min_unsat_core                        false
% 3.02/0.99  --soft_assumptions                      false
% 3.02/0.99  --soft_lemma_size                       3
% 3.02/0.99  --prop_impl_unit_size                   0
% 3.02/0.99  --prop_impl_unit                        []
% 3.02/0.99  --share_sel_clauses                     true
% 3.02/0.99  --reset_solvers                         false
% 3.02/0.99  --bc_imp_inh                            [conj_cone]
% 3.02/0.99  --conj_cone_tolerance                   3.
% 3.02/0.99  --extra_neg_conj                        none
% 3.02/0.99  --large_theory_mode                     true
% 3.02/0.99  --prolific_symb_bound                   200
% 3.02/0.99  --lt_threshold                          2000
% 3.02/0.99  --clause_weak_htbl                      true
% 3.02/0.99  --gc_record_bc_elim                     false
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing Options
% 3.02/0.99  
% 3.02/0.99  --preprocessing_flag                    true
% 3.02/0.99  --time_out_prep_mult                    0.1
% 3.02/0.99  --splitting_mode                        input
% 3.02/0.99  --splitting_grd                         true
% 3.02/0.99  --splitting_cvd                         false
% 3.02/0.99  --splitting_cvd_svl                     false
% 3.02/0.99  --splitting_nvd                         32
% 3.02/0.99  --sub_typing                            true
% 3.02/0.99  --prep_gs_sim                           true
% 3.02/0.99  --prep_unflatten                        true
% 3.02/0.99  --prep_res_sim                          true
% 3.02/0.99  --prep_upred                            true
% 3.02/0.99  --prep_sem_filter                       exhaustive
% 3.02/0.99  --prep_sem_filter_out                   false
% 3.02/0.99  --pred_elim                             true
% 3.02/0.99  --res_sim_input                         true
% 3.02/0.99  --eq_ax_congr_red                       true
% 3.02/0.99  --pure_diseq_elim                       true
% 3.02/0.99  --brand_transform                       false
% 3.02/0.99  --non_eq_to_eq                          false
% 3.02/0.99  --prep_def_merge                        true
% 3.02/0.99  --prep_def_merge_prop_impl              false
% 3.02/0.99  --prep_def_merge_mbd                    true
% 3.02/0.99  --prep_def_merge_tr_red                 false
% 3.02/0.99  --prep_def_merge_tr_cl                  false
% 3.02/0.99  --smt_preprocessing                     true
% 3.02/0.99  --smt_ac_axioms                         fast
% 3.02/0.99  --preprocessed_out                      false
% 3.02/0.99  --preprocessed_stats                    false
% 3.02/0.99  
% 3.02/0.99  ------ Abstraction refinement Options
% 3.02/0.99  
% 3.02/0.99  --abstr_ref                             []
% 3.02/0.99  --abstr_ref_prep                        false
% 3.02/0.99  --abstr_ref_until_sat                   false
% 3.02/0.99  --abstr_ref_sig_restrict                funpre
% 3.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.99  --abstr_ref_under                       []
% 3.02/0.99  
% 3.02/0.99  ------ SAT Options
% 3.02/0.99  
% 3.02/0.99  --sat_mode                              false
% 3.02/0.99  --sat_fm_restart_options                ""
% 3.02/0.99  --sat_gr_def                            false
% 3.02/0.99  --sat_epr_types                         true
% 3.02/0.99  --sat_non_cyclic_types                  false
% 3.02/0.99  --sat_finite_models                     false
% 3.02/0.99  --sat_fm_lemmas                         false
% 3.02/0.99  --sat_fm_prep                           false
% 3.02/0.99  --sat_fm_uc_incr                        true
% 3.02/0.99  --sat_out_model                         small
% 3.02/0.99  --sat_out_clauses                       false
% 3.02/0.99  
% 3.02/0.99  ------ QBF Options
% 3.02/0.99  
% 3.02/0.99  --qbf_mode                              false
% 3.02/0.99  --qbf_elim_univ                         false
% 3.02/0.99  --qbf_dom_inst                          none
% 3.02/0.99  --qbf_dom_pre_inst                      false
% 3.02/0.99  --qbf_sk_in                             false
% 3.02/0.99  --qbf_pred_elim                         true
% 3.02/0.99  --qbf_split                             512
% 3.02/0.99  
% 3.02/0.99  ------ BMC1 Options
% 3.02/0.99  
% 3.02/0.99  --bmc1_incremental                      false
% 3.02/0.99  --bmc1_axioms                           reachable_all
% 3.02/0.99  --bmc1_min_bound                        0
% 3.02/0.99  --bmc1_max_bound                        -1
% 3.02/0.99  --bmc1_max_bound_default                -1
% 3.02/0.99  --bmc1_symbol_reachability              true
% 3.02/0.99  --bmc1_property_lemmas                  false
% 3.02/0.99  --bmc1_k_induction                      false
% 3.02/0.99  --bmc1_non_equiv_states                 false
% 3.02/0.99  --bmc1_deadlock                         false
% 3.02/0.99  --bmc1_ucm                              false
% 3.02/0.99  --bmc1_add_unsat_core                   none
% 3.02/0.99  --bmc1_unsat_core_children              false
% 3.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.99  --bmc1_out_stat                         full
% 3.02/0.99  --bmc1_ground_init                      false
% 3.02/0.99  --bmc1_pre_inst_next_state              false
% 3.02/0.99  --bmc1_pre_inst_state                   false
% 3.02/0.99  --bmc1_pre_inst_reach_state             false
% 3.02/0.99  --bmc1_out_unsat_core                   false
% 3.02/0.99  --bmc1_aig_witness_out                  false
% 3.02/0.99  --bmc1_verbose                          false
% 3.02/0.99  --bmc1_dump_clauses_tptp                false
% 3.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.99  --bmc1_dump_file                        -
% 3.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.99  --bmc1_ucm_extend_mode                  1
% 3.02/0.99  --bmc1_ucm_init_mode                    2
% 3.02/0.99  --bmc1_ucm_cone_mode                    none
% 3.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.99  --bmc1_ucm_relax_model                  4
% 3.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.99  --bmc1_ucm_layered_model                none
% 3.02/0.99  --bmc1_ucm_max_lemma_size               10
% 3.02/0.99  
% 3.02/0.99  ------ AIG Options
% 3.02/0.99  
% 3.02/0.99  --aig_mode                              false
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation Options
% 3.02/0.99  
% 3.02/0.99  --instantiation_flag                    true
% 3.02/0.99  --inst_sos_flag                         false
% 3.02/0.99  --inst_sos_phase                        true
% 3.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel_side                     num_symb
% 3.02/0.99  --inst_solver_per_active                1400
% 3.02/0.99  --inst_solver_calls_frac                1.
% 3.02/0.99  --inst_passive_queue_type               priority_queues
% 3.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.99  --inst_passive_queues_freq              [25;2]
% 3.02/0.99  --inst_dismatching                      true
% 3.02/0.99  --inst_eager_unprocessed_to_passive     true
% 3.02/0.99  --inst_prop_sim_given                   true
% 3.02/0.99  --inst_prop_sim_new                     false
% 3.02/0.99  --inst_subs_new                         false
% 3.02/0.99  --inst_eq_res_simp                      false
% 3.02/0.99  --inst_subs_given                       false
% 3.02/0.99  --inst_orphan_elimination               true
% 3.02/0.99  --inst_learning_loop_flag               true
% 3.02/0.99  --inst_learning_start                   3000
% 3.02/0.99  --inst_learning_factor                  2
% 3.02/0.99  --inst_start_prop_sim_after_learn       3
% 3.02/0.99  --inst_sel_renew                        solver
% 3.02/0.99  --inst_lit_activity_flag                true
% 3.02/0.99  --inst_restr_to_given                   false
% 3.02/0.99  --inst_activity_threshold               500
% 3.02/0.99  --inst_out_proof                        true
% 3.02/0.99  
% 3.02/0.99  ------ Resolution Options
% 3.02/0.99  
% 3.02/0.99  --resolution_flag                       true
% 3.02/0.99  --res_lit_sel                           adaptive
% 3.02/0.99  --res_lit_sel_side                      none
% 3.02/0.99  --res_ordering                          kbo
% 3.02/0.99  --res_to_prop_solver                    active
% 3.02/0.99  --res_prop_simpl_new                    false
% 3.02/0.99  --res_prop_simpl_given                  true
% 3.02/0.99  --res_passive_queue_type                priority_queues
% 3.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.99  --res_passive_queues_freq               [15;5]
% 3.02/0.99  --res_forward_subs                      full
% 3.02/0.99  --res_backward_subs                     full
% 3.02/0.99  --res_forward_subs_resolution           true
% 3.02/0.99  --res_backward_subs_resolution          true
% 3.02/0.99  --res_orphan_elimination                true
% 3.02/0.99  --res_time_limit                        2.
% 3.02/0.99  --res_out_proof                         true
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Options
% 3.02/0.99  
% 3.02/0.99  --superposition_flag                    true
% 3.02/0.99  --sup_passive_queue_type                priority_queues
% 3.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.99  --demod_completeness_check              fast
% 3.02/0.99  --demod_use_ground                      true
% 3.02/0.99  --sup_to_prop_solver                    passive
% 3.02/0.99  --sup_prop_simpl_new                    true
% 3.02/0.99  --sup_prop_simpl_given                  true
% 3.02/0.99  --sup_fun_splitting                     false
% 3.02/0.99  --sup_smt_interval                      50000
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Simplification Setup
% 3.02/0.99  
% 3.02/0.99  --sup_indices_passive                   []
% 3.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_full_bw                           [BwDemod]
% 3.02/0.99  --sup_immed_triv                        [TrivRules]
% 3.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_immed_bw_main                     []
% 3.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  
% 3.02/0.99  ------ Combination Options
% 3.02/0.99  
% 3.02/0.99  --comb_res_mult                         3
% 3.02/0.99  --comb_sup_mult                         2
% 3.02/0.99  --comb_inst_mult                        10
% 3.02/0.99  
% 3.02/0.99  ------ Debug Options
% 3.02/0.99  
% 3.02/0.99  --dbg_backtrace                         false
% 3.02/0.99  --dbg_dump_prop_clauses                 false
% 3.02/0.99  --dbg_dump_prop_clauses_file            -
% 3.02/0.99  --dbg_out_stat                          false
% 3.02/0.99  ------ Parsing...
% 3.02/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/0.99  ------ Proving...
% 3.02/0.99  ------ Problem Properties 
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  clauses                                 27
% 3.02/0.99  conjectures                             7
% 3.02/0.99  EPR                                     4
% 3.02/0.99  Horn                                    23
% 3.02/0.99  unary                                   8
% 3.02/0.99  binary                                  4
% 3.02/0.99  lits                                    79
% 3.02/0.99  lits eq                                 21
% 3.02/0.99  fd_pure                                 0
% 3.02/0.99  fd_pseudo                               0
% 3.02/0.99  fd_cond                                 3
% 3.02/0.99  fd_pseudo_cond                          0
% 3.02/0.99  AC symbols                              0
% 3.02/0.99  
% 3.02/0.99  ------ Schedule dynamic 5 is on 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  ------ 
% 3.02/0.99  Current options:
% 3.02/0.99  ------ 
% 3.02/0.99  
% 3.02/0.99  ------ Input Options
% 3.02/0.99  
% 3.02/0.99  --out_options                           all
% 3.02/0.99  --tptp_safe_out                         true
% 3.02/0.99  --problem_path                          ""
% 3.02/0.99  --include_path                          ""
% 3.02/0.99  --clausifier                            res/vclausify_rel
% 3.02/0.99  --clausifier_options                    --mode clausify
% 3.02/0.99  --stdin                                 false
% 3.02/0.99  --stats_out                             all
% 3.02/0.99  
% 3.02/0.99  ------ General Options
% 3.02/0.99  
% 3.02/0.99  --fof                                   false
% 3.02/0.99  --time_out_real                         305.
% 3.02/0.99  --time_out_virtual                      -1.
% 3.02/0.99  --symbol_type_check                     false
% 3.02/0.99  --clausify_out                          false
% 3.02/0.99  --sig_cnt_out                           false
% 3.02/0.99  --trig_cnt_out                          false
% 3.02/0.99  --trig_cnt_out_tolerance                1.
% 3.02/0.99  --trig_cnt_out_sk_spl                   false
% 3.02/0.99  --abstr_cl_out                          false
% 3.02/0.99  
% 3.02/0.99  ------ Global Options
% 3.02/0.99  
% 3.02/0.99  --schedule                              default
% 3.02/0.99  --add_important_lit                     false
% 3.02/0.99  --prop_solver_per_cl                    1000
% 3.02/0.99  --min_unsat_core                        false
% 3.02/0.99  --soft_assumptions                      false
% 3.02/0.99  --soft_lemma_size                       3
% 3.02/0.99  --prop_impl_unit_size                   0
% 3.02/0.99  --prop_impl_unit                        []
% 3.02/0.99  --share_sel_clauses                     true
% 3.02/0.99  --reset_solvers                         false
% 3.02/0.99  --bc_imp_inh                            [conj_cone]
% 3.02/0.99  --conj_cone_tolerance                   3.
% 3.02/0.99  --extra_neg_conj                        none
% 3.02/0.99  --large_theory_mode                     true
% 3.02/0.99  --prolific_symb_bound                   200
% 3.02/0.99  --lt_threshold                          2000
% 3.02/0.99  --clause_weak_htbl                      true
% 3.02/0.99  --gc_record_bc_elim                     false
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing Options
% 3.02/0.99  
% 3.02/0.99  --preprocessing_flag                    true
% 3.02/0.99  --time_out_prep_mult                    0.1
% 3.02/0.99  --splitting_mode                        input
% 3.02/0.99  --splitting_grd                         true
% 3.02/0.99  --splitting_cvd                         false
% 3.02/0.99  --splitting_cvd_svl                     false
% 3.02/0.99  --splitting_nvd                         32
% 3.02/0.99  --sub_typing                            true
% 3.02/0.99  --prep_gs_sim                           true
% 3.02/0.99  --prep_unflatten                        true
% 3.02/0.99  --prep_res_sim                          true
% 3.02/0.99  --prep_upred                            true
% 3.02/0.99  --prep_sem_filter                       exhaustive
% 3.02/0.99  --prep_sem_filter_out                   false
% 3.02/0.99  --pred_elim                             true
% 3.02/0.99  --res_sim_input                         true
% 3.02/0.99  --eq_ax_congr_red                       true
% 3.02/0.99  --pure_diseq_elim                       true
% 3.02/0.99  --brand_transform                       false
% 3.02/0.99  --non_eq_to_eq                          false
% 3.02/0.99  --prep_def_merge                        true
% 3.02/0.99  --prep_def_merge_prop_impl              false
% 3.02/0.99  --prep_def_merge_mbd                    true
% 3.02/0.99  --prep_def_merge_tr_red                 false
% 3.02/0.99  --prep_def_merge_tr_cl                  false
% 3.02/0.99  --smt_preprocessing                     true
% 3.02/0.99  --smt_ac_axioms                         fast
% 3.02/0.99  --preprocessed_out                      false
% 3.02/0.99  --preprocessed_stats                    false
% 3.02/0.99  
% 3.02/0.99  ------ Abstraction refinement Options
% 3.02/0.99  
% 3.02/0.99  --abstr_ref                             []
% 3.02/0.99  --abstr_ref_prep                        false
% 3.02/0.99  --abstr_ref_until_sat                   false
% 3.02/0.99  --abstr_ref_sig_restrict                funpre
% 3.02/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/0.99  --abstr_ref_under                       []
% 3.02/0.99  
% 3.02/0.99  ------ SAT Options
% 3.02/0.99  
% 3.02/0.99  --sat_mode                              false
% 3.02/0.99  --sat_fm_restart_options                ""
% 3.02/0.99  --sat_gr_def                            false
% 3.02/0.99  --sat_epr_types                         true
% 3.02/0.99  --sat_non_cyclic_types                  false
% 3.02/0.99  --sat_finite_models                     false
% 3.02/0.99  --sat_fm_lemmas                         false
% 3.02/0.99  --sat_fm_prep                           false
% 3.02/0.99  --sat_fm_uc_incr                        true
% 3.02/0.99  --sat_out_model                         small
% 3.02/0.99  --sat_out_clauses                       false
% 3.02/0.99  
% 3.02/0.99  ------ QBF Options
% 3.02/0.99  
% 3.02/0.99  --qbf_mode                              false
% 3.02/0.99  --qbf_elim_univ                         false
% 3.02/0.99  --qbf_dom_inst                          none
% 3.02/0.99  --qbf_dom_pre_inst                      false
% 3.02/0.99  --qbf_sk_in                             false
% 3.02/0.99  --qbf_pred_elim                         true
% 3.02/0.99  --qbf_split                             512
% 3.02/0.99  
% 3.02/0.99  ------ BMC1 Options
% 3.02/0.99  
% 3.02/0.99  --bmc1_incremental                      false
% 3.02/0.99  --bmc1_axioms                           reachable_all
% 3.02/0.99  --bmc1_min_bound                        0
% 3.02/0.99  --bmc1_max_bound                        -1
% 3.02/0.99  --bmc1_max_bound_default                -1
% 3.02/0.99  --bmc1_symbol_reachability              true
% 3.02/0.99  --bmc1_property_lemmas                  false
% 3.02/0.99  --bmc1_k_induction                      false
% 3.02/0.99  --bmc1_non_equiv_states                 false
% 3.02/0.99  --bmc1_deadlock                         false
% 3.02/0.99  --bmc1_ucm                              false
% 3.02/0.99  --bmc1_add_unsat_core                   none
% 3.02/0.99  --bmc1_unsat_core_children              false
% 3.02/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/0.99  --bmc1_out_stat                         full
% 3.02/0.99  --bmc1_ground_init                      false
% 3.02/0.99  --bmc1_pre_inst_next_state              false
% 3.02/0.99  --bmc1_pre_inst_state                   false
% 3.02/0.99  --bmc1_pre_inst_reach_state             false
% 3.02/0.99  --bmc1_out_unsat_core                   false
% 3.02/0.99  --bmc1_aig_witness_out                  false
% 3.02/0.99  --bmc1_verbose                          false
% 3.02/0.99  --bmc1_dump_clauses_tptp                false
% 3.02/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.02/0.99  --bmc1_dump_file                        -
% 3.02/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.02/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.02/0.99  --bmc1_ucm_extend_mode                  1
% 3.02/0.99  --bmc1_ucm_init_mode                    2
% 3.02/0.99  --bmc1_ucm_cone_mode                    none
% 3.02/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.02/0.99  --bmc1_ucm_relax_model                  4
% 3.02/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.02/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/0.99  --bmc1_ucm_layered_model                none
% 3.02/0.99  --bmc1_ucm_max_lemma_size               10
% 3.02/0.99  
% 3.02/0.99  ------ AIG Options
% 3.02/0.99  
% 3.02/0.99  --aig_mode                              false
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation Options
% 3.02/0.99  
% 3.02/0.99  --instantiation_flag                    true
% 3.02/0.99  --inst_sos_flag                         false
% 3.02/0.99  --inst_sos_phase                        true
% 3.02/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/0.99  --inst_lit_sel_side                     none
% 3.02/0.99  --inst_solver_per_active                1400
% 3.02/0.99  --inst_solver_calls_frac                1.
% 3.02/0.99  --inst_passive_queue_type               priority_queues
% 3.02/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/0.99  --inst_passive_queues_freq              [25;2]
% 3.02/0.99  --inst_dismatching                      true
% 3.02/0.99  --inst_eager_unprocessed_to_passive     true
% 3.02/0.99  --inst_prop_sim_given                   true
% 3.02/0.99  --inst_prop_sim_new                     false
% 3.02/0.99  --inst_subs_new                         false
% 3.02/0.99  --inst_eq_res_simp                      false
% 3.02/0.99  --inst_subs_given                       false
% 3.02/0.99  --inst_orphan_elimination               true
% 3.02/0.99  --inst_learning_loop_flag               true
% 3.02/0.99  --inst_learning_start                   3000
% 3.02/0.99  --inst_learning_factor                  2
% 3.02/0.99  --inst_start_prop_sim_after_learn       3
% 3.02/0.99  --inst_sel_renew                        solver
% 3.02/0.99  --inst_lit_activity_flag                true
% 3.02/0.99  --inst_restr_to_given                   false
% 3.02/0.99  --inst_activity_threshold               500
% 3.02/0.99  --inst_out_proof                        true
% 3.02/0.99  
% 3.02/0.99  ------ Resolution Options
% 3.02/0.99  
% 3.02/0.99  --resolution_flag                       false
% 3.02/0.99  --res_lit_sel                           adaptive
% 3.02/0.99  --res_lit_sel_side                      none
% 3.02/0.99  --res_ordering                          kbo
% 3.02/0.99  --res_to_prop_solver                    active
% 3.02/0.99  --res_prop_simpl_new                    false
% 3.02/0.99  --res_prop_simpl_given                  true
% 3.02/0.99  --res_passive_queue_type                priority_queues
% 3.02/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/0.99  --res_passive_queues_freq               [15;5]
% 3.02/0.99  --res_forward_subs                      full
% 3.02/0.99  --res_backward_subs                     full
% 3.02/0.99  --res_forward_subs_resolution           true
% 3.02/0.99  --res_backward_subs_resolution          true
% 3.02/0.99  --res_orphan_elimination                true
% 3.02/0.99  --res_time_limit                        2.
% 3.02/0.99  --res_out_proof                         true
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Options
% 3.02/0.99  
% 3.02/0.99  --superposition_flag                    true
% 3.02/0.99  --sup_passive_queue_type                priority_queues
% 3.02/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.02/0.99  --demod_completeness_check              fast
% 3.02/0.99  --demod_use_ground                      true
% 3.02/0.99  --sup_to_prop_solver                    passive
% 3.02/0.99  --sup_prop_simpl_new                    true
% 3.02/0.99  --sup_prop_simpl_given                  true
% 3.02/0.99  --sup_fun_splitting                     false
% 3.02/0.99  --sup_smt_interval                      50000
% 3.02/0.99  
% 3.02/0.99  ------ Superposition Simplification Setup
% 3.02/0.99  
% 3.02/0.99  --sup_indices_passive                   []
% 3.02/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_full_bw                           [BwDemod]
% 3.02/0.99  --sup_immed_triv                        [TrivRules]
% 3.02/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_immed_bw_main                     []
% 3.02/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/0.99  
% 3.02/0.99  ------ Combination Options
% 3.02/0.99  
% 3.02/0.99  --comb_res_mult                         3
% 3.02/0.99  --comb_sup_mult                         2
% 3.02/0.99  --comb_inst_mult                        10
% 3.02/0.99  
% 3.02/0.99  ------ Debug Options
% 3.02/0.99  
% 3.02/0.99  --dbg_backtrace                         false
% 3.02/0.99  --dbg_dump_prop_clauses                 false
% 3.02/0.99  --dbg_dump_prop_clauses_file            -
% 3.02/0.99  --dbg_out_stat                          false
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  ------ Proving...
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  % SZS status Theorem for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99   Resolution empty clause
% 3.02/0.99  
% 3.02/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  fof(f14,conjecture,(
% 3.02/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f15,negated_conjecture,(
% 3.02/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.02/0.99    inference(negated_conjecture,[],[f14])).
% 3.02/0.99  
% 3.02/0.99  fof(f36,plain,(
% 3.02/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.02/0.99    inference(ennf_transformation,[],[f15])).
% 3.02/0.99  
% 3.02/0.99  fof(f37,plain,(
% 3.02/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.02/0.99    inference(flattening,[],[f36])).
% 3.02/0.99  
% 3.02/0.99  fof(f42,plain,(
% 3.02/0.99    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f41,plain,(
% 3.02/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f40,plain,(
% 3.02/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.02/0.99    introduced(choice_axiom,[])).
% 3.02/0.99  
% 3.02/0.99  fof(f43,plain,(
% 3.02/0.99    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.02/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f37,f42,f41,f40])).
% 3.02/0.99  
% 3.02/0.99  fof(f66,plain,(
% 3.02/0.99    l1_struct_0(sK0)),
% 3.02/0.99    inference(cnf_transformation,[],[f43])).
% 3.02/0.99  
% 3.02/0.99  fof(f9,axiom,(
% 3.02/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f27,plain,(
% 3.02/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.02/0.99    inference(ennf_transformation,[],[f9])).
% 3.02/0.99  
% 3.02/0.99  fof(f59,plain,(
% 3.02/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f27])).
% 3.02/0.99  
% 3.02/0.99  fof(f68,plain,(
% 3.02/0.99    l1_struct_0(sK1)),
% 3.02/0.99    inference(cnf_transformation,[],[f43])).
% 3.02/0.99  
% 3.02/0.99  fof(f72,plain,(
% 3.02/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.02/0.99    inference(cnf_transformation,[],[f43])).
% 3.02/0.99  
% 3.02/0.99  fof(f71,plain,(
% 3.02/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.02/0.99    inference(cnf_transformation,[],[f43])).
% 3.02/0.99  
% 3.02/0.99  fof(f6,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f22,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f6])).
% 3.02/0.99  
% 3.02/0.99  fof(f50,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f22])).
% 3.02/0.99  
% 3.02/0.99  fof(f11,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f30,plain,(
% 3.02/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.02/0.99    inference(ennf_transformation,[],[f11])).
% 3.02/0.99  
% 3.02/0.99  fof(f31,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.02/0.99    inference(flattening,[],[f30])).
% 3.02/0.99  
% 3.02/0.99  fof(f61,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f31])).
% 3.02/0.99  
% 3.02/0.99  fof(f69,plain,(
% 3.02/0.99    v1_funct_1(sK2)),
% 3.02/0.99    inference(cnf_transformation,[],[f43])).
% 3.02/0.99  
% 3.02/0.99  fof(f73,plain,(
% 3.02/0.99    v2_funct_1(sK2)),
% 3.02/0.99    inference(cnf_transformation,[],[f43])).
% 3.02/0.99  
% 3.02/0.99  fof(f70,plain,(
% 3.02/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.02/0.99    inference(cnf_transformation,[],[f43])).
% 3.02/0.99  
% 3.02/0.99  fof(f8,axiom,(
% 3.02/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f25,plain,(
% 3.02/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.02/0.99    inference(ennf_transformation,[],[f8])).
% 3.02/0.99  
% 3.02/0.99  fof(f26,plain,(
% 3.02/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.02/0.99    inference(flattening,[],[f25])).
% 3.02/0.99  
% 3.02/0.99  fof(f39,plain,(
% 3.02/0.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.02/0.99    inference(nnf_transformation,[],[f26])).
% 3.02/0.99  
% 3.02/0.99  fof(f58,plain,(
% 3.02/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f39])).
% 3.02/0.99  
% 3.02/0.99  fof(f80,plain,(
% 3.02/0.99    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.02/0.99    inference(equality_resolution,[],[f58])).
% 3.02/0.99  
% 3.02/0.99  fof(f74,plain,(
% 3.02/0.99    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.02/0.99    inference(cnf_transformation,[],[f43])).
% 3.02/0.99  
% 3.02/0.99  fof(f12,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f32,plain,(
% 3.02/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.02/0.99    inference(ennf_transformation,[],[f12])).
% 3.02/0.99  
% 3.02/0.99  fof(f33,plain,(
% 3.02/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.02/0.99    inference(flattening,[],[f32])).
% 3.02/0.99  
% 3.02/0.99  fof(f62,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f33])).
% 3.02/0.99  
% 3.02/0.99  fof(f13,axiom,(
% 3.02/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f34,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.02/0.99    inference(ennf_transformation,[],[f13])).
% 3.02/0.99  
% 3.02/0.99  fof(f35,plain,(
% 3.02/0.99    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.02/0.99    inference(flattening,[],[f34])).
% 3.02/0.99  
% 3.02/0.99  fof(f65,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f35])).
% 3.02/0.99  
% 3.02/0.99  fof(f5,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f21,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f5])).
% 3.02/0.99  
% 3.02/0.99  fof(f49,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f21])).
% 3.02/0.99  
% 3.02/0.99  fof(f7,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f23,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f7])).
% 3.02/0.99  
% 3.02/0.99  fof(f24,plain,(
% 3.02/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(flattening,[],[f23])).
% 3.02/0.99  
% 3.02/0.99  fof(f38,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(nnf_transformation,[],[f24])).
% 3.02/0.99  
% 3.02/0.99  fof(f51,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f38])).
% 3.02/0.99  
% 3.02/0.99  fof(f1,axiom,(
% 3.02/0.99    v1_xboole_0(k1_xboole_0)),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f44,plain,(
% 3.02/0.99    v1_xboole_0(k1_xboole_0)),
% 3.02/0.99    inference(cnf_transformation,[],[f1])).
% 3.02/0.99  
% 3.02/0.99  fof(f10,axiom,(
% 3.02/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f28,plain,(
% 3.02/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f10])).
% 3.02/0.99  
% 3.02/0.99  fof(f29,plain,(
% 3.02/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.02/0.99    inference(flattening,[],[f28])).
% 3.02/0.99  
% 3.02/0.99  fof(f60,plain,(
% 3.02/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f29])).
% 3.02/0.99  
% 3.02/0.99  fof(f67,plain,(
% 3.02/0.99    ~v2_struct_0(sK1)),
% 3.02/0.99    inference(cnf_transformation,[],[f43])).
% 3.02/0.99  
% 3.02/0.99  fof(f64,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f33])).
% 3.02/0.99  
% 3.02/0.99  fof(f63,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f33])).
% 3.02/0.99  
% 3.02/0.99  fof(f4,axiom,(
% 3.02/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f20,plain,(
% 3.02/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/0.99    inference(ennf_transformation,[],[f4])).
% 3.02/0.99  
% 3.02/0.99  fof(f48,plain,(
% 3.02/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/0.99    inference(cnf_transformation,[],[f20])).
% 3.02/0.99  
% 3.02/0.99  fof(f2,axiom,(
% 3.02/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f16,plain,(
% 3.02/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f2])).
% 3.02/0.99  
% 3.02/0.99  fof(f17,plain,(
% 3.02/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/0.99    inference(flattening,[],[f16])).
% 3.02/0.99  
% 3.02/0.99  fof(f46,plain,(
% 3.02/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f17])).
% 3.02/0.99  
% 3.02/0.99  fof(f3,axiom,(
% 3.02/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.02/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/0.99  
% 3.02/0.99  fof(f18,plain,(
% 3.02/0.99    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/0.99    inference(ennf_transformation,[],[f3])).
% 3.02/0.99  
% 3.02/0.99  fof(f19,plain,(
% 3.02/0.99    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/0.99    inference(flattening,[],[f18])).
% 3.02/0.99  
% 3.02/0.99  fof(f47,plain,(
% 3.02/0.99    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/0.99    inference(cnf_transformation,[],[f19])).
% 3.02/0.99  
% 3.02/0.99  cnf(c_30,negated_conjecture,
% 3.02/0.99      ( l1_struct_0(sK0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1139,plain,
% 3.02/0.99      ( l1_struct_0(sK0) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_15,plain,
% 3.02/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1150,plain,
% 3.02/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_struct_0(X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1484,plain,
% 3.02/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1139,c_1150]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_28,negated_conjecture,
% 3.02/0.99      ( l1_struct_0(sK1) ),
% 3.02/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1140,plain,
% 3.02/0.99      ( l1_struct_0(sK1) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1483,plain,
% 3.02/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1140,c_1150]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_24,negated_conjecture,
% 3.02/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.02/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1775,plain,
% 3.02/0.99      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_1483,c_24]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1877,plain,
% 3.02/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_1484,c_1775]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_25,negated_conjecture,
% 3.02/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.02/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1143,plain,
% 3.02/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_6,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1157,plain,
% 3.02/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1587,plain,
% 3.02/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1143,c_1157]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1953,plain,
% 3.02/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_1587,c_1483,c_1484]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2369,plain,
% 3.02/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_1877,c_1953]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2372,plain,
% 3.02/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_2369,c_1953]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_17,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v2_funct_1(X0)
% 3.02/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.02/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.02/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1149,plain,
% 3.02/0.99      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 3.02/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.02/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.02/0.99      | v1_funct_1(X2) != iProver_top
% 3.02/0.99      | v2_funct_1(X2) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3824,plain,
% 3.02/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 3.02/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.02/0.99      | v1_funct_1(sK2) != iProver_top
% 3.02/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_2372,c_1149]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_27,negated_conjecture,
% 3.02/0.99      ( v1_funct_1(sK2) ),
% 3.02/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_34,plain,
% 3.02/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_23,negated_conjecture,
% 3.02/0.99      ( v2_funct_1(sK2) ),
% 3.02/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_37,plain,
% 3.02/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_26,negated_conjecture,
% 3.02/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.02/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1142,plain,
% 3.02/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1773,plain,
% 3.02/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_1483,c_1142]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1950,plain,
% 3.02/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_1773,c_1484]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2373,plain,
% 3.02/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_2369,c_1950]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1772,plain,
% 3.02/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_1483,c_1143]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2388,plain,
% 3.02/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_1772,c_1484,c_2369]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4575,plain,
% 3.02/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_3824,c_34,c_37,c_2373,c_2388]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_13,plain,
% 3.02/0.99      ( r2_funct_2(X0,X1,X2,X2)
% 3.02/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.02/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/0.99      | ~ v1_funct_1(X2) ),
% 3.02/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_22,negated_conjecture,
% 3.02/0.99      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.02/0.99      inference(cnf_transformation,[],[f74]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_430,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 3.02/0.99      | u1_struct_0(sK1) != X2
% 3.02/0.99      | u1_struct_0(sK0) != X1
% 3.02/0.99      | sK2 != X0 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_431,plain,
% 3.02/0.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.02/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_430]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1138,plain,
% 3.02/0.99      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.02/0.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_431]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1771,plain,
% 3.02/0.99      ( k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.02/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_1483,c_1138]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3456,plain,
% 3.02/0.99      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2
% 3.02/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))) != iProver_top ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_1771,c_1484,c_2369]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4580,plain,
% 3.02/0.99      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 3.02/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_4575,c_3456]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_31,plain,
% 3.02/0.99      ( l1_struct_0(sK0) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_33,plain,
% 3.02/0.99      ( l1_struct_0(sK1) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_35,plain,
% 3.02/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_36,plain,
% 3.02/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1379,plain,
% 3.02/0.99      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_20,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 3.02/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1427,plain,
% 3.02/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.02/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/0.99      | v1_funct_1(k2_tops_2(X0,X1,sK2))
% 3.02/0.99      | ~ v1_funct_1(sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_20]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1533,plain,
% 3.02/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.02/0.99      | ~ v1_funct_1(sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1427]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1534,plain,
% 3.02/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.02/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 3.02/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1533]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1451,plain,
% 3.02/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.02/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/0.99      | ~ v1_funct_1(sK2)
% 3.02/0.99      | ~ v2_funct_1(sK2)
% 3.02/0.99      | k2_tops_2(X0,X1,sK2) = k2_funct_1(sK2)
% 3.02/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1576,plain,
% 3.02/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/0.99      | ~ v1_funct_1(sK2)
% 3.02/0.99      | ~ v2_funct_1(sK2)
% 3.02/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.02/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1451]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_21,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.02/0.99      | ~ l1_struct_0(X1)
% 3.02/0.99      | ~ l1_struct_0(X2)
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v2_funct_1(X0)
% 3.02/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 3.02/0.99      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 3.02/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1461,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(X1))
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
% 3.02/0.99      | ~ l1_struct_0(X1)
% 3.02/0.99      | ~ l1_struct_0(sK0)
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v2_funct_1(X0)
% 3.02/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X0))
% 3.02/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X0) != k2_struct_0(X1) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_21]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1598,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/0.99      | ~ l1_struct_0(sK1)
% 3.02/0.99      | ~ l1_struct_0(sK0)
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v2_funct_1(X0)
% 3.02/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0))
% 3.02/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1461]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1696,plain,
% 3.02/0.99      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/0.99      | ~ l1_struct_0(sK1)
% 3.02/0.99      | ~ l1_struct_0(sK0)
% 3.02/0.99      | ~ v1_funct_1(sK2)
% 3.02/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.02/0.99      | ~ v2_funct_1(sK2)
% 3.02/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1598]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1697,plain,
% 3.02/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 3.02/0.99      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.02/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.02/0.99      | l1_struct_0(sK1) != iProver_top
% 3.02/0.99      | l1_struct_0(sK0) != iProver_top
% 3.02/0.99      | v1_funct_1(sK2) != iProver_top
% 3.02/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 3.02/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1696]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_682,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1683,plain,
% 3.02/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 3.02/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 3.02/0.99      | u1_struct_0(sK1) != X0 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_682]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2151,plain,
% 3.02/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 3.02/0.99      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 3.02/0.99      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1683]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2138,plain,
% 3.02/0.99      ( X0 != X1
% 3.02/0.99      | X0 = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 3.02/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X1 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_682]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2856,plain,
% 3.02/0.99      ( X0 = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 3.02/0.99      | X0 != k2_funct_1(sK2)
% 3.02/0.99      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2138]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3323,plain,
% 3.02/0.99      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
% 3.02/0.99      | k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 3.02/0.99      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_2856]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_681,plain,( X0 = X0 ),theory(equality) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3324,plain,
% 3.02/0.99      ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_681]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_5,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f49]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1158,plain,
% 3.02/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1705,plain,
% 3.02/0.99      ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1143,c_1158]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2031,plain,
% 3.02/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_1705,c_1483,c_1484]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2371,plain,
% 3.02/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k1_relat_1(sK2) ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_2369,c_2031]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_12,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.02/0.99      | k1_xboole_0 = X2 ),
% 3.02/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1151,plain,
% 3.02/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.02/0.99      | k1_xboole_0 = X1
% 3.02/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3050,plain,
% 3.02/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0)
% 3.02/0.99      | k2_relat_1(sK2) = k1_xboole_0
% 3.02/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_2388,c_1151]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_0,plain,
% 3.02/0.99      ( v1_xboole_0(k1_xboole_0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_16,plain,
% 3.02/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.02/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_338,plain,
% 3.02/0.99      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_0,c_16]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_29,negated_conjecture,
% 3.02/0.99      ( ~ v2_struct_0(sK1) ),
% 3.02/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_356,plain,
% 3.02/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) != k1_xboole_0 | sK1 != X0 ),
% 3.02/0.99      inference(resolution_lifted,[status(thm)],[c_338,c_29]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_357,plain,
% 3.02/0.99      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) != k1_xboole_0 ),
% 3.02/0.99      inference(unflattening,[status(thm)],[c_356]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_359,plain,
% 3.02/0.99      ( u1_struct_0(sK1) != k1_xboole_0 ),
% 3.02/0.99      inference(global_propositional_subsumption,[status(thm)],[c_357,c_28]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1774,plain,
% 3.02/0.99      ( k2_struct_0(sK1) != k1_xboole_0 ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_1483,c_359]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2374,plain,
% 3.02/0.99      ( k2_relat_1(sK2) != k1_xboole_0 ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_2369,c_1774]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3802,plain,
% 3.02/0.99      ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_struct_0(sK0) ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_3050,c_2373,c_2374]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3821,plain,
% 3.02/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.02/0.99      inference(demodulation,[status(thm)],[c_2371,c_3802]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_687,plain,
% 3.02/0.99      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.02/0.99      theory(equality) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1643,plain,
% 3.02/0.99      ( v1_funct_1(X0)
% 3.02/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.02/0.99      | X0 != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_687]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3903,plain,
% 3.02/0.99      ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.02/0.99      | v1_funct_1(k2_funct_1(sK2))
% 3.02/0.99      | k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1643]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3904,plain,
% 3.02/0.99      ( k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 3.02/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3903]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_686,plain,
% 3.02/0.99      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 3.02/0.99      theory(equality) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1944,plain,
% 3.02/0.99      ( v2_funct_1(X0)
% 3.02/0.99      | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.02/0.99      | X0 != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_686]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3902,plain,
% 3.02/0.99      ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.02/0.99      | v2_funct_1(k2_funct_1(sK2))
% 3.02/0.99      | k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1944]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3906,plain,
% 3.02/0.99      ( k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 3.02/0.99      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 3.02/0.99      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3902]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_18,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.02/0.99      | ~ v1_funct_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1148,plain,
% 3.02/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1))) = iProver_top
% 3.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1146,plain,
% 3.02/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/0.99      | v1_funct_1(X0) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3627,plain,
% 3.02/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.02/0.99      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) != iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/0.99      | v1_funct_1(X0) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_tops_2(X1,X2,X0)) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_tops_2(X2,X1,k2_tops_2(X1,X2,X0))) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1148,c_1146]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_42,plain,
% 3.02/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/0.99      | v1_funct_1(X0) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_tops_2(X1,X2,X0)) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_19,plain,
% 3.02/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/0.99      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 3.02/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/0.99      | ~ v1_funct_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_45,plain,
% 3.02/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.02/0.99      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4122,plain,
% 3.02/0.99      ( v1_funct_1(X0) != iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/0.99      | v1_funct_2(X0,X1,X2) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_tops_2(X2,X1,k2_tops_2(X1,X2,X0))) = iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_3627,c_42,c_45]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4123,plain,
% 3.02/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/0.99      | v1_funct_1(X0) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_tops_2(X2,X1,k2_tops_2(X1,X2,X0))) = iProver_top ),
% 3.02/0.99      inference(renaming,[status(thm)],[c_4122]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4596,plain,
% 3.02/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) = iProver_top
% 3.02/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_4575,c_4123]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4597,plain,
% 3.02/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 3.02/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.02/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_4575,c_1148]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1147,plain,
% 3.02/0.99      ( v1_funct_2(X0,X1,X2) != iProver_top
% 3.02/0.99      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1) = iProver_top
% 3.02/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4598,plain,
% 3.02/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 3.02/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.02/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_4575,c_1147]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3632,plain,
% 3.02/0.99      ( k2_relset_1(X0,X1,k2_tops_2(X1,X0,X2)) = k2_relat_1(k2_tops_2(X1,X0,X2))
% 3.02/0.99      | v1_funct_2(X2,X1,X0) != iProver_top
% 3.02/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 3.02/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1148,c_1157]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4551,plain,
% 3.02/0.99      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
% 3.02/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_2388,c_3632]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4773,plain,
% 3.02/0.99      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_4551,c_34,c_2373]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4,plain,
% 3.02/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1159,plain,
% 3.02/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.02/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1582,plain,
% 3.02/0.99      ( v1_relat_1(sK2) = iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1143,c_1159]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1,plain,
% 3.02/0.99      ( ~ v1_relat_1(X0)
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v2_funct_1(X0)
% 3.02/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.02/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1162,plain,
% 3.02/0.99      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.02/0.99      | v1_relat_1(X0) != iProver_top
% 3.02/0.99      | v1_funct_1(X0) != iProver_top
% 3.02/0.99      | v2_funct_1(X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2902,plain,
% 3.02/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.02/0.99      | v1_funct_1(sK2) != iProver_top
% 3.02/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1582,c_1162]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1385,plain,
% 3.02/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/0.99      | v1_relat_1(sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1468,plain,
% 3.02/0.99      ( ~ v1_relat_1(sK2)
% 3.02/0.99      | ~ v1_funct_1(sK2)
% 3.02/0.99      | ~ v2_funct_1(sK2)
% 3.02/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3159,plain,
% 3.02/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_2902,c_27,c_25,c_23,c_1385,c_1468]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4775,plain,
% 3.02/0.99      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_4773,c_3159,c_4575]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4777,plain,
% 3.02/0.99      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.02/0.99      | k2_struct_0(sK0) != k1_relat_1(sK2)
% 3.02/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.02/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_4775,c_1149]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_3,plain,
% 3.02/0.99      ( ~ v1_relat_1(X0)
% 3.02/0.99      | ~ v1_funct_1(X0)
% 3.02/0.99      | ~ v2_funct_1(X0)
% 3.02/0.99      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.02/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1160,plain,
% 3.02/0.99      ( k2_funct_1(k2_funct_1(X0)) = X0
% 3.02/0.99      | v1_relat_1(X0) != iProver_top
% 3.02/0.99      | v1_funct_1(X0) != iProver_top
% 3.02/0.99      | v2_funct_1(X0) != iProver_top ),
% 3.02/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2221,plain,
% 3.02/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.02/0.99      | v1_funct_1(sK2) != iProver_top
% 3.02/0.99      | v2_funct_1(sK2) != iProver_top ),
% 3.02/0.99      inference(superposition,[status(thm)],[c_1582,c_1160]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_1466,plain,
% 3.02/0.99      ( ~ v1_relat_1(sK2)
% 3.02/0.99      | ~ v1_funct_1(sK2)
% 3.02/0.99      | ~ v2_funct_1(sK2)
% 3.02/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.02/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_2520,plain,
% 3.02/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_2221,c_27,c_25,c_23,c_1385,c_1466]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4797,plain,
% 3.02/0.99      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 3.02/0.99      | k2_struct_0(sK0) != k1_relat_1(sK2)
% 3.02/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 3.02/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.02/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_4777,c_2520]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4851,plain,
% 3.02/0.99      ( m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.02/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_4580,c_31,c_28,c_33,c_27,c_34,c_26,c_35,c_25,c_36,c_24,
% 3.02/0.99                 c_23,c_37,c_1379,c_1534,c_1576,c_1697,c_2151,c_2373,c_2388,
% 3.02/0.99                 c_3323,c_3324,c_3821,c_3904,c_3906,c_4596,c_4597,c_4598,
% 3.02/0.99                 c_4797]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4852,plain,
% 3.02/0.99      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 3.02/0.99      inference(renaming,[status(thm)],[c_4851]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4807,plain,
% 3.02/0.99      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 3.02/0.99      inference(global_propositional_subsumption,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_4797,c_31,c_28,c_33,c_27,c_34,c_26,c_35,c_25,c_36,c_24,
% 3.02/0.99                 c_23,c_37,c_1379,c_1534,c_1576,c_1697,c_2151,c_2373,c_2388,
% 3.02/0.99                 c_3323,c_3324,c_3821,c_3904,c_3906,c_4597,c_4598]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4855,plain,
% 3.02/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 3.02/0.99      inference(light_normalisation,[status(thm)],[c_4852,c_4807]) ).
% 3.02/0.99  
% 3.02/0.99  cnf(c_4858,plain,
% 3.02/0.99      ( $false ),
% 3.02/0.99      inference(forward_subsumption_resolution,
% 3.02/0.99                [status(thm)],
% 3.02/0.99                [c_4855,c_2388,c_2373]) ).
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/0.99  
% 3.02/0.99  ------                               Statistics
% 3.02/0.99  
% 3.02/0.99  ------ General
% 3.02/0.99  
% 3.02/0.99  abstr_ref_over_cycles:                  0
% 3.02/0.99  abstr_ref_under_cycles:                 0
% 3.02/0.99  gc_basic_clause_elim:                   0
% 3.02/0.99  forced_gc_time:                         0
% 3.02/0.99  parsing_time:                           0.012
% 3.02/0.99  unif_index_cands_time:                  0.
% 3.02/0.99  unif_index_add_time:                    0.
% 3.02/0.99  orderings_time:                         0.
% 3.02/0.99  out_proof_time:                         0.015
% 3.02/0.99  total_time:                             0.193
% 3.02/0.99  num_of_symbols:                         54
% 3.02/0.99  num_of_terms:                           5160
% 3.02/0.99  
% 3.02/0.99  ------ Preprocessing
% 3.02/0.99  
% 3.02/0.99  num_of_splits:                          0
% 3.02/0.99  num_of_split_atoms:                     0
% 3.02/0.99  num_of_reused_defs:                     0
% 3.02/0.99  num_eq_ax_congr_red:                    9
% 3.02/0.99  num_of_sem_filtered_clauses:            1
% 3.02/0.99  num_of_subtypes:                        0
% 3.02/0.99  monotx_restored_types:                  0
% 3.02/0.99  sat_num_of_epr_types:                   0
% 3.02/0.99  sat_num_of_non_cyclic_types:            0
% 3.02/0.99  sat_guarded_non_collapsed_types:        0
% 3.02/0.99  num_pure_diseq_elim:                    0
% 3.02/0.99  simp_replaced_by:                       0
% 3.02/0.99  res_preprocessed:                       147
% 3.02/0.99  prep_upred:                             0
% 3.02/0.99  prep_unflattend:                        8
% 3.02/0.99  smt_new_axioms:                         0
% 3.02/0.99  pred_elim_cands:                        6
% 3.02/0.99  pred_elim:                              3
% 3.02/0.99  pred_elim_cl:                           4
% 3.02/0.99  pred_elim_cycles:                       6
% 3.02/0.99  merged_defs:                            0
% 3.02/0.99  merged_defs_ncl:                        0
% 3.02/0.99  bin_hyper_res:                          0
% 3.02/0.99  prep_cycles:                            4
% 3.02/0.99  pred_elim_time:                         0.004
% 3.02/0.99  splitting_time:                         0.
% 3.02/0.99  sem_filter_time:                        0.
% 3.02/0.99  monotx_time:                            0.001
% 3.02/0.99  subtype_inf_time:                       0.
% 3.02/0.99  
% 3.02/0.99  ------ Problem properties
% 3.02/0.99  
% 3.02/0.99  clauses:                                27
% 3.02/0.99  conjectures:                            7
% 3.02/0.99  epr:                                    4
% 3.02/0.99  horn:                                   23
% 3.02/0.99  ground:                                 9
% 3.02/0.99  unary:                                  8
% 3.02/0.99  binary:                                 4
% 3.02/0.99  lits:                                   79
% 3.02/0.99  lits_eq:                                21
% 3.02/0.99  fd_pure:                                0
% 3.02/0.99  fd_pseudo:                              0
% 3.02/0.99  fd_cond:                                3
% 3.02/0.99  fd_pseudo_cond:                         0
% 3.02/0.99  ac_symbols:                             0
% 3.02/0.99  
% 3.02/0.99  ------ Propositional Solver
% 3.02/0.99  
% 3.02/0.99  prop_solver_calls:                      28
% 3.02/0.99  prop_fast_solver_calls:                 1247
% 3.02/0.99  smt_solver_calls:                       0
% 3.02/0.99  smt_fast_solver_calls:                  0
% 3.02/0.99  prop_num_of_clauses:                    1497
% 3.02/0.99  prop_preprocess_simplified:             5468
% 3.02/0.99  prop_fo_subsumed:                       50
% 3.02/0.99  prop_solver_time:                       0.
% 3.02/0.99  smt_solver_time:                        0.
% 3.02/0.99  smt_fast_solver_time:                   0.
% 3.02/0.99  prop_fast_solver_time:                  0.
% 3.02/0.99  prop_unsat_core_time:                   0.
% 3.02/0.99  
% 3.02/0.99  ------ QBF
% 3.02/0.99  
% 3.02/0.99  qbf_q_res:                              0
% 3.02/0.99  qbf_num_tautologies:                    0
% 3.02/0.99  qbf_prep_cycles:                        0
% 3.02/0.99  
% 3.02/0.99  ------ BMC1
% 3.02/0.99  
% 3.02/0.99  bmc1_current_bound:                     -1
% 3.02/0.99  bmc1_last_solved_bound:                 -1
% 3.02/0.99  bmc1_unsat_core_size:                   -1
% 3.02/0.99  bmc1_unsat_core_parents_size:           -1
% 3.02/0.99  bmc1_merge_next_fun:                    0
% 3.02/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.02/0.99  
% 3.02/0.99  ------ Instantiation
% 3.02/0.99  
% 3.02/0.99  inst_num_of_clauses:                    517
% 3.02/0.99  inst_num_in_passive:                    66
% 3.02/0.99  inst_num_in_active:                     328
% 3.02/0.99  inst_num_in_unprocessed:                123
% 3.02/0.99  inst_num_of_loops:                      340
% 3.02/0.99  inst_num_of_learning_restarts:          0
% 3.02/0.99  inst_num_moves_active_passive:          9
% 3.02/0.99  inst_lit_activity:                      0
% 3.02/0.99  inst_lit_activity_moves:                0
% 3.02/0.99  inst_num_tautologies:                   0
% 3.02/0.99  inst_num_prop_implied:                  0
% 3.02/0.99  inst_num_existing_simplified:           0
% 3.02/0.99  inst_num_eq_res_simplified:             0
% 3.02/0.99  inst_num_child_elim:                    0
% 3.02/0.99  inst_num_of_dismatching_blockings:      74
% 3.02/0.99  inst_num_of_non_proper_insts:           396
% 3.02/0.99  inst_num_of_duplicates:                 0
% 3.02/0.99  inst_inst_num_from_inst_to_res:         0
% 3.02/0.99  inst_dismatching_checking_time:         0.
% 3.02/0.99  
% 3.02/0.99  ------ Resolution
% 3.02/0.99  
% 3.02/0.99  res_num_of_clauses:                     0
% 3.02/0.99  res_num_in_passive:                     0
% 3.02/0.99  res_num_in_active:                      0
% 3.02/0.99  res_num_of_loops:                       151
% 3.02/0.99  res_forward_subset_subsumed:            36
% 3.02/0.99  res_backward_subset_subsumed:           0
% 3.02/0.99  res_forward_subsumed:                   0
% 3.02/0.99  res_backward_subsumed:                  0
% 3.02/0.99  res_forward_subsumption_resolution:     0
% 3.02/0.99  res_backward_subsumption_resolution:    0
% 3.02/0.99  res_clause_to_clause_subsumption:       132
% 3.02/0.99  res_orphan_elimination:                 0
% 3.02/0.99  res_tautology_del:                      42
% 3.02/0.99  res_num_eq_res_simplified:              0
% 3.02/0.99  res_num_sel_changes:                    0
% 3.02/0.99  res_moves_from_active_to_pass:          0
% 3.02/0.99  
% 3.02/0.99  ------ Superposition
% 3.02/0.99  
% 3.02/0.99  sup_time_total:                         0.
% 3.02/0.99  sup_time_generating:                    0.
% 3.02/0.99  sup_time_sim_full:                      0.
% 3.02/0.99  sup_time_sim_immed:                     0.
% 3.02/0.99  
% 3.02/0.99  sup_num_of_clauses:                     64
% 3.02/0.99  sup_num_in_active:                      51
% 3.02/0.99  sup_num_in_passive:                     13
% 3.02/0.99  sup_num_of_loops:                       66
% 3.02/0.99  sup_fw_superposition:                   28
% 3.02/0.99  sup_bw_superposition:                   28
% 3.02/0.99  sup_immediate_simplified:               23
% 3.02/0.99  sup_given_eliminated:                   0
% 3.02/0.99  comparisons_done:                       0
% 3.02/0.99  comparisons_avoided:                    0
% 3.02/0.99  
% 3.02/0.99  ------ Simplifications
% 3.02/0.99  
% 3.02/0.99  
% 3.02/0.99  sim_fw_subset_subsumed:                 4
% 3.02/0.99  sim_bw_subset_subsumed:                 0
% 3.02/0.99  sim_fw_subsumed:                        1
% 3.02/0.99  sim_bw_subsumed:                        0
% 3.02/0.99  sim_fw_subsumption_res:                 2
% 3.02/0.99  sim_bw_subsumption_res:                 0
% 3.02/0.99  sim_tautology_del:                      1
% 3.02/0.99  sim_eq_tautology_del:                   3
% 3.02/0.99  sim_eq_res_simp:                        0
% 3.02/0.99  sim_fw_demodulated:                     0
% 3.02/0.99  sim_bw_demodulated:                     15
% 3.02/0.99  sim_light_normalised:                   32
% 3.02/0.99  sim_joinable_taut:                      0
% 3.02/0.99  sim_joinable_simp:                      0
% 3.02/0.99  sim_ac_normalised:                      0
% 3.02/0.99  sim_smt_subsumption:                    0
% 3.02/0.99  
%------------------------------------------------------------------------------
