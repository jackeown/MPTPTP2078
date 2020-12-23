%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:43 EST 2020

% Result     : Theorem 0.36s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :  257 (7895 expanded)
%              Number of clauses        :  186 (2916 expanded)
%              Number of leaves         :   21 (2084 expanded)
%              Depth                    :   24
%              Number of atoms          : 1067 (47278 expanded)
%              Number of equality atoms :  487 (8789 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   4 average)
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
    inference(ennf_transformation,[],[f15])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f42,f41,f40])).

fof(f65,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f57,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f67,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f71,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f43])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f12,axiom,(
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
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

fof(f18,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f47,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

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
    inference(ennf_transformation,[],[f13])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f20,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f46,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f8,axiom,(
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

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f7,axiom,(
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

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f24])).

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
    inference(nnf_transformation,[],[f25])).

fof(f53,plain,(
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

fof(f74,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f53])).

fof(f73,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_29,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_608,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_29])).

cnf(c_1164,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_608])).

cnf(c_13,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_620,plain,
    ( ~ l1_struct_0(X0_53)
    | u1_struct_0(X0_53) = k2_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1153,plain,
    ( u1_struct_0(X0_53) = k2_struct_0(X0_53)
    | l1_struct_0(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_620])).

cnf(c_1598,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1164,c_1153])).

cnf(c_27,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_609,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_27])).

cnf(c_1163,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_609])).

cnf(c_1597,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1163,c_1153])).

cnf(c_23,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_613,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1720,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1597,c_613])).

cnf(c_1779,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1598,c_1720])).

cnf(c_24,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_612,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1160,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_612])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_624,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1149,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_624])).

cnf(c_1606,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1160,c_1149])).

cnf(c_1834,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1606,c_1597,c_1598])).

cnf(c_1836,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_1779,c_1834])).

cnf(c_1838,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1836,c_1834])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_28,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_380,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_28])).

cnf(c_381,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_380])).

cnf(c_385,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_27])).

cnf(c_386,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_385])).

cnf(c_605,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_53)
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(u1_struct_0(X0_53),u1_struct_0(sK1),X0_51) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_53),k2_tops_2(u1_struct_0(X0_53),u1_struct_0(sK1),X0_51)) = k2_struct_0(X0_53) ),
    inference(subtyping,[status(esa)],[c_386])).

cnf(c_1167,plain,
    ( k2_relset_1(u1_struct_0(X0_53),u1_struct_0(sK1),X0_51) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_53),k2_tops_2(u1_struct_0(X0_53),u1_struct_0(sK1),X0_51)) = k2_struct_0(X0_53)
    | v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_605])).

cnf(c_2325,plain,
    ( k2_relset_1(u1_struct_0(X0_53),u1_struct_0(sK1),X0_51) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_53),k2_tops_2(u1_struct_0(X0_53),u1_struct_0(sK1),X0_51)) = k2_struct_0(X0_53)
    | v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1167,c_1836])).

cnf(c_2336,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_relat_1(sK2)
    | v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_2325])).

cnf(c_2337,plain,
    ( k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_relat_1(sK2)
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2336,c_1598])).

cnf(c_30,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2669,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_relat_1(sK2)
    | k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2337,c_30])).

cnf(c_2670,plain,
    ( k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_relat_1(sK2)
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(renaming,[status(thm)],[c_2669])).

cnf(c_1840,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1836,c_1597])).

cnf(c_2675,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = k2_struct_0(sK0)
    | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2670,c_1840])).

cnf(c_2838,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_2675])).

cnf(c_26,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_33,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_22,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_36,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_25,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_611,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1161,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_611])).

cnf(c_1719,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1597,c_1161])).

cnf(c_1781,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1719,c_1598])).

cnf(c_1839,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1836,c_1781])).

cnf(c_1718,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1597,c_1160])).

cnf(c_1867,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1718,c_1598,c_1836])).

cnf(c_2683,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2675])).

cnf(c_5988,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2838,c_33,c_36,c_1838,c_1839,c_1867,c_2683])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_619,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1154,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51)
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_619])).

cnf(c_2834,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_1154])).

cnf(c_4402,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2834,c_33,c_36,c_1839,c_1867])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_618,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | m1_subset_1(k2_tops_2(X0_52,X1_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1155,plain,
    ( v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(k2_tops_2(X0_52,X1_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_2408,plain,
    ( k2_relset_1(X0_52,X1_52,k2_tops_2(X1_52,X0_52,X0_51)) = k2_relat_1(k2_tops_2(X1_52,X0_52,X0_51))
    | v1_funct_2(X0_51,X1_52,X0_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top ),
    inference(superposition,[status(thm)],[c_1155,c_1149])).

cnf(c_3280,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1867,c_2408])).

cnf(c_3711,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3280,c_33,c_1839])).

cnf(c_4406,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(demodulation,[status(thm)],[c_4402,c_3711])).

cnf(c_610,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_26])).

cnf(c_1162,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_610])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_629,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1144,plain,
    ( k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51)
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_1654,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1144])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_631,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
    | ~ v1_relat_1(X1_51)
    | v1_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1142,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
    | v1_relat_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_1537,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1160,c_1142])).

cnf(c_1538,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1537])).

cnf(c_1655,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1654])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_630,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1660,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_2199,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1654,c_22,c_1538,c_1655,c_1660])).

cnf(c_4416,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4406,c_2199])).

cnf(c_5990,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5988,c_4402,c_4416])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_615,plain,
    ( ~ v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53))
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
    | ~ l1_struct_0(X1_53)
    | ~ l1_struct_0(X0_53)
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51))
    | k2_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51) != k2_struct_0(X1_53) ),
    inference(subtyping,[status(esa)],[c_20])).

cnf(c_1158,plain,
    ( k2_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51) != k2_struct_0(X1_53)
    | v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(X1_53) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_615])).

cnf(c_3017,plain,
    ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
    | v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_1158])).

cnf(c_3080,plain,
    ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3017,c_1598])).

cnf(c_3538,plain,
    ( l1_struct_0(X0_53) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3080,c_30])).

cnf(c_3539,plain,
    ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
    | l1_struct_0(X0_53) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3538])).

cnf(c_3552,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_struct_0(sK1)
    | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0_51)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1840,c_3539])).

cnf(c_3560,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
    | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3552,c_1836,c_1840])).

cnf(c_32,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3881,plain,
    ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3560,c_32])).

cnf(c_3882,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
    | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3881])).

cnf(c_3893,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_3882])).

cnf(c_3577,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_3560])).

cnf(c_5875,plain,
    ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3893,c_32,c_33,c_36,c_1838,c_1839,c_1867,c_3577])).

cnf(c_5879,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5875,c_4402])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_626,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k5_relat_1(X0_51,k2_funct_1(X0_51)) = k6_relat_1(k1_relat_1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_1147,plain,
    ( k5_relat_1(X0_51,k2_funct_1(X0_51)) = k6_relat_1(k1_relat_1(X0_51))
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_1940,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1147])).

cnf(c_687,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_626])).

cnf(c_2262,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1940,c_26,c_22,c_687,c_1538,c_1660])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_625,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v1_funct_1(X1_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | ~ v1_relat_1(X1_51)
    | k5_relat_1(X1_51,X0_51) != k6_relat_1(k2_relat_1(X0_51))
    | k1_relat_1(X0_51) != k2_relat_1(X1_51)
    | k2_funct_1(X0_51) = X1_51 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1148,plain,
    ( k5_relat_1(X0_51,X1_51) != k6_relat_1(k2_relat_1(X1_51))
    | k1_relat_1(X1_51) != k2_relat_1(X0_51)
    | k2_funct_1(X1_51) = X0_51
    | v1_funct_1(X1_51) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X1_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top
    | v1_relat_1(X1_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_2384,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2262,c_1148])).

cnf(c_3,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_628,plain,
    ( ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | ~ v1_relat_1(X0_51)
    | k1_relat_1(k2_funct_1(X0_51)) = k2_relat_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1145,plain,
    ( k1_relat_1(k2_funct_1(X0_51)) = k2_relat_1(X0_51)
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top
    | v1_relat_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_628])).

cnf(c_1882,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1162,c_1145])).

cnf(c_681,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_628])).

cnf(c_2203,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1882,c_26,c_22,c_681,c_1538,c_1660])).

cnf(c_2393,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2384,c_2199,c_2203])).

cnf(c_2394,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_2393])).

cnf(c_34,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_35,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_705,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_620])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_621,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_funct_1(X0_51))
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_1518,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_621])).

cnf(c_1519,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1518])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_623,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1524,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_623])).

cnf(c_1525,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1524])).

cnf(c_1661,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1660])).

cnf(c_1753,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_630])).

cnf(c_1754,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1753])).

cnf(c_638,plain,
    ( X0_52 != X1_52
    | X2_52 != X1_52
    | X2_52 = X0_52 ),
    theory(equality)).

cnf(c_1590,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_52
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_52 ),
    inference(instantiation,[status(thm)],[c_638])).

cnf(c_1756,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_1436,plain,
    ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | v1_relat_1(X0_51)
    | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
    inference(instantiation,[status(thm)],[c_631])).

cnf(c_2021,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1436])).

cnf(c_2025,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2021])).

cnf(c_3771,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2394,c_27,c_33,c_34,c_35,c_36,c_705,c_613,c_1519,c_1525,c_1537,c_1661,c_1754,c_1756,c_2025])).

cnf(c_5882,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_5879,c_3771])).

cnf(c_4540,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4416,c_1154])).

cnf(c_1527,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_619])).

cnf(c_1530,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK1)
    | ~ l1_struct_0(sK0)
    | ~ v1_funct_1(sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_615])).

cnf(c_1531,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1530])).

cnf(c_633,plain,
    ( X0_51 = X0_51 ),
    theory(equality)).

cnf(c_2215,plain,
    ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_622,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | ~ v2_funct_1(X0_51)
    | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1151,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52) = iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_2835,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_1151])).

cnf(c_637,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_2071,plain,
    ( X0_51 != X1_51
    | X0_51 = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X1_51 ),
    inference(instantiation,[status(thm)],[c_637])).

cnf(c_2618,plain,
    ( X0_51 = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | X0_51 != k2_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2071])).

cnf(c_2951,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k2_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2618])).

cnf(c_1150,plain,
    ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
    | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
    | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
    | v1_funct_1(X0_51) != iProver_top
    | v2_funct_1(X0_51) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_623])).

cnf(c_3006,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1838,c_1150])).

cnf(c_646,plain,
    ( ~ v2_funct_1(X0_51)
    | v2_funct_1(X1_51)
    | X1_51 != X0_51 ),
    theory(equality)).

cnf(c_2065,plain,
    ( ~ v2_funct_1(X0_51)
    | v2_funct_1(k2_funct_1(X1_51))
    | k2_funct_1(X1_51) != X0_51 ),
    inference(instantiation,[status(thm)],[c_646])).

cnf(c_3829,plain,
    ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(instantiation,[status(thm)],[c_2065])).

cnf(c_3830,plain,
    ( k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3829])).

cnf(c_5451,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4540,c_30,c_27,c_32,c_26,c_33,c_25,c_34,c_24,c_35,c_22,c_36,c_705,c_613,c_1519,c_1527,c_1531,c_1756,c_1839,c_1867,c_2215,c_2835,c_2951,c_3006,c_3830])).

cnf(c_5885,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_5882,c_5451])).

cnf(c_8,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_21,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_328,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_21])).

cnf(c_329,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_328])).

cnf(c_607,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_329])).

cnf(c_1165,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_607])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_616,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51)
    | v1_funct_1(k2_tops_2(X0_52,X1_52,X0_51)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1487,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_16,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_617,plain,
    ( ~ v1_funct_2(X0_51,X0_52,X1_52)
    | v1_funct_2(k2_tops_2(X0_52,X1_52,X0_51),X1_52,X0_52)
    | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
    | ~ v1_funct_1(X0_51) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_1490,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_1493,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_1560,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_616])).

cnf(c_1559,plain,
    ( v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_617])).

cnf(c_1558,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_618])).

cnf(c_2342,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1165,c_26,c_25,c_24,c_607,c_1487,c_1490,c_1493,c_1560,c_1559,c_1558])).

cnf(c_2344,plain,
    ( k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) != sK2 ),
    inference(light_normalisation,[status(thm)],[c_2342,c_1598])).

cnf(c_2538,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2 ),
    inference(demodulation,[status(thm)],[c_1840,c_2344])).

cnf(c_4409,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2 ),
    inference(demodulation,[status(thm)],[c_4402,c_2538])).

cnf(c_5984,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5885,c_4409])).

cnf(c_5992,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5990,c_5984])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 10:53:12 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 0.36/1.06  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 0.36/1.06  
% 0.36/1.06  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 0.36/1.06  
% 0.36/1.06  ------  iProver source info
% 0.36/1.06  
% 0.36/1.06  git: date: 2020-06-30 10:37:57 +0100
% 0.36/1.06  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 0.36/1.06  git: non_committed_changes: false
% 0.36/1.06  git: last_make_outside_of_git: false
% 0.36/1.06  
% 0.36/1.06  ------ 
% 0.36/1.06  
% 0.36/1.06  ------ Input Options
% 0.36/1.06  
% 0.36/1.06  --out_options                           all
% 0.36/1.06  --tptp_safe_out                         true
% 0.36/1.06  --problem_path                          ""
% 0.36/1.06  --include_path                          ""
% 0.36/1.06  --clausifier                            res/vclausify_rel
% 0.36/1.06  --clausifier_options                    --mode clausify
% 0.36/1.06  --stdin                                 false
% 0.36/1.06  --stats_out                             all
% 0.36/1.06  
% 0.36/1.06  ------ General Options
% 0.36/1.06  
% 0.36/1.06  --fof                                   false
% 0.36/1.06  --time_out_real                         305.
% 0.36/1.06  --time_out_virtual                      -1.
% 0.36/1.06  --symbol_type_check                     false
% 0.36/1.06  --clausify_out                          false
% 0.36/1.06  --sig_cnt_out                           false
% 0.36/1.06  --trig_cnt_out                          false
% 0.36/1.06  --trig_cnt_out_tolerance                1.
% 0.36/1.06  --trig_cnt_out_sk_spl                   false
% 0.36/1.06  --abstr_cl_out                          false
% 0.36/1.06  
% 0.36/1.06  ------ Global Options
% 0.36/1.06  
% 0.36/1.06  --schedule                              default
% 0.36/1.06  --add_important_lit                     false
% 0.36/1.06  --prop_solver_per_cl                    1000
% 0.36/1.06  --min_unsat_core                        false
% 0.36/1.06  --soft_assumptions                      false
% 0.36/1.06  --soft_lemma_size                       3
% 0.36/1.06  --prop_impl_unit_size                   0
% 0.36/1.06  --prop_impl_unit                        []
% 0.36/1.06  --share_sel_clauses                     true
% 0.36/1.06  --reset_solvers                         false
% 0.36/1.06  --bc_imp_inh                            [conj_cone]
% 0.36/1.06  --conj_cone_tolerance                   3.
% 0.36/1.06  --extra_neg_conj                        none
% 0.36/1.06  --large_theory_mode                     true
% 0.36/1.06  --prolific_symb_bound                   200
% 0.36/1.06  --lt_threshold                          2000
% 0.36/1.06  --clause_weak_htbl                      true
% 0.36/1.06  --gc_record_bc_elim                     false
% 0.36/1.06  
% 0.36/1.06  ------ Preprocessing Options
% 0.36/1.06  
% 0.36/1.06  --preprocessing_flag                    true
% 0.36/1.06  --time_out_prep_mult                    0.1
% 0.36/1.06  --splitting_mode                        input
% 0.36/1.06  --splitting_grd                         true
% 0.36/1.06  --splitting_cvd                         false
% 0.36/1.06  --splitting_cvd_svl                     false
% 0.36/1.06  --splitting_nvd                         32
% 0.36/1.06  --sub_typing                            true
% 0.36/1.06  --prep_gs_sim                           true
% 0.36/1.06  --prep_unflatten                        true
% 0.36/1.06  --prep_res_sim                          true
% 0.36/1.06  --prep_upred                            true
% 0.36/1.06  --prep_sem_filter                       exhaustive
% 0.36/1.06  --prep_sem_filter_out                   false
% 0.36/1.06  --pred_elim                             true
% 0.36/1.06  --res_sim_input                         true
% 0.36/1.06  --eq_ax_congr_red                       true
% 0.36/1.06  --pure_diseq_elim                       true
% 0.36/1.06  --brand_transform                       false
% 0.36/1.06  --non_eq_to_eq                          false
% 0.36/1.06  --prep_def_merge                        true
% 0.36/1.06  --prep_def_merge_prop_impl              false
% 0.36/1.06  --prep_def_merge_mbd                    true
% 0.36/1.06  --prep_def_merge_tr_red                 false
% 0.36/1.06  --prep_def_merge_tr_cl                  false
% 0.36/1.06  --smt_preprocessing                     true
% 0.36/1.06  --smt_ac_axioms                         fast
% 0.36/1.06  --preprocessed_out                      false
% 0.36/1.06  --preprocessed_stats                    false
% 0.36/1.06  
% 0.36/1.06  ------ Abstraction refinement Options
% 0.36/1.06  
% 0.36/1.06  --abstr_ref                             []
% 0.36/1.06  --abstr_ref_prep                        false
% 0.36/1.06  --abstr_ref_until_sat                   false
% 0.36/1.06  --abstr_ref_sig_restrict                funpre
% 0.36/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.06  --abstr_ref_under                       []
% 0.36/1.06  
% 0.36/1.06  ------ SAT Options
% 0.36/1.06  
% 0.36/1.06  --sat_mode                              false
% 0.36/1.06  --sat_fm_restart_options                ""
% 0.36/1.06  --sat_gr_def                            false
% 0.36/1.06  --sat_epr_types                         true
% 0.36/1.06  --sat_non_cyclic_types                  false
% 0.36/1.06  --sat_finite_models                     false
% 0.36/1.06  --sat_fm_lemmas                         false
% 0.36/1.06  --sat_fm_prep                           false
% 0.36/1.06  --sat_fm_uc_incr                        true
% 0.36/1.06  --sat_out_model                         small
% 0.36/1.06  --sat_out_clauses                       false
% 0.36/1.06  
% 0.36/1.06  ------ QBF Options
% 0.36/1.06  
% 0.36/1.06  --qbf_mode                              false
% 0.36/1.06  --qbf_elim_univ                         false
% 0.36/1.06  --qbf_dom_inst                          none
% 0.36/1.06  --qbf_dom_pre_inst                      false
% 0.36/1.06  --qbf_sk_in                             false
% 0.36/1.06  --qbf_pred_elim                         true
% 0.36/1.06  --qbf_split                             512
% 0.36/1.06  
% 0.36/1.06  ------ BMC1 Options
% 0.36/1.06  
% 0.36/1.06  --bmc1_incremental                      false
% 0.36/1.06  --bmc1_axioms                           reachable_all
% 0.36/1.06  --bmc1_min_bound                        0
% 0.36/1.06  --bmc1_max_bound                        -1
% 0.36/1.06  --bmc1_max_bound_default                -1
% 0.36/1.06  --bmc1_symbol_reachability              true
% 0.36/1.06  --bmc1_property_lemmas                  false
% 0.36/1.06  --bmc1_k_induction                      false
% 0.36/1.06  --bmc1_non_equiv_states                 false
% 0.36/1.06  --bmc1_deadlock                         false
% 0.36/1.06  --bmc1_ucm                              false
% 0.36/1.06  --bmc1_add_unsat_core                   none
% 0.36/1.06  --bmc1_unsat_core_children              false
% 0.36/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.06  --bmc1_out_stat                         full
% 0.36/1.06  --bmc1_ground_init                      false
% 0.36/1.06  --bmc1_pre_inst_next_state              false
% 0.36/1.06  --bmc1_pre_inst_state                   false
% 0.36/1.06  --bmc1_pre_inst_reach_state             false
% 0.36/1.06  --bmc1_out_unsat_core                   false
% 0.36/1.06  --bmc1_aig_witness_out                  false
% 0.36/1.06  --bmc1_verbose                          false
% 0.36/1.06  --bmc1_dump_clauses_tptp                false
% 0.36/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.06  --bmc1_dump_file                        -
% 0.36/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.06  --bmc1_ucm_extend_mode                  1
% 0.36/1.06  --bmc1_ucm_init_mode                    2
% 0.36/1.06  --bmc1_ucm_cone_mode                    none
% 0.36/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.06  --bmc1_ucm_relax_model                  4
% 0.36/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.06  --bmc1_ucm_layered_model                none
% 0.36/1.06  --bmc1_ucm_max_lemma_size               10
% 0.36/1.06  
% 0.36/1.06  ------ AIG Options
% 0.36/1.06  
% 0.36/1.06  --aig_mode                              false
% 0.36/1.06  
% 0.36/1.06  ------ Instantiation Options
% 0.36/1.06  
% 0.36/1.06  --instantiation_flag                    true
% 0.36/1.06  --inst_sos_flag                         false
% 0.36/1.06  --inst_sos_phase                        true
% 0.36/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.06  --inst_lit_sel_side                     num_symb
% 0.36/1.06  --inst_solver_per_active                1400
% 0.36/1.06  --inst_solver_calls_frac                1.
% 0.36/1.06  --inst_passive_queue_type               priority_queues
% 0.36/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.06  --inst_passive_queues_freq              [25;2]
% 0.36/1.06  --inst_dismatching                      true
% 0.36/1.06  --inst_eager_unprocessed_to_passive     true
% 0.36/1.06  --inst_prop_sim_given                   true
% 0.36/1.06  --inst_prop_sim_new                     false
% 0.36/1.06  --inst_subs_new                         false
% 0.36/1.06  --inst_eq_res_simp                      false
% 0.36/1.06  --inst_subs_given                       false
% 0.36/1.06  --inst_orphan_elimination               true
% 0.36/1.06  --inst_learning_loop_flag               true
% 0.36/1.06  --inst_learning_start                   3000
% 0.36/1.06  --inst_learning_factor                  2
% 0.36/1.06  --inst_start_prop_sim_after_learn       3
% 0.36/1.06  --inst_sel_renew                        solver
% 0.36/1.06  --inst_lit_activity_flag                true
% 0.36/1.06  --inst_restr_to_given                   false
% 0.36/1.06  --inst_activity_threshold               500
% 0.36/1.06  --inst_out_proof                        true
% 0.36/1.06  
% 0.36/1.06  ------ Resolution Options
% 0.36/1.06  
% 0.36/1.06  --resolution_flag                       true
% 0.36/1.06  --res_lit_sel                           adaptive
% 0.36/1.06  --res_lit_sel_side                      none
% 0.36/1.06  --res_ordering                          kbo
% 0.36/1.06  --res_to_prop_solver                    active
% 0.36/1.06  --res_prop_simpl_new                    false
% 0.36/1.06  --res_prop_simpl_given                  true
% 0.36/1.06  --res_passive_queue_type                priority_queues
% 0.36/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.06  --res_passive_queues_freq               [15;5]
% 0.36/1.06  --res_forward_subs                      full
% 0.36/1.06  --res_backward_subs                     full
% 0.36/1.06  --res_forward_subs_resolution           true
% 0.36/1.06  --res_backward_subs_resolution          true
% 0.36/1.06  --res_orphan_elimination                true
% 0.36/1.06  --res_time_limit                        2.
% 0.36/1.06  --res_out_proof                         true
% 0.36/1.06  
% 0.36/1.06  ------ Superposition Options
% 0.36/1.06  
% 0.36/1.06  --superposition_flag                    true
% 0.36/1.06  --sup_passive_queue_type                priority_queues
% 0.36/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.06  --demod_completeness_check              fast
% 0.36/1.06  --demod_use_ground                      true
% 0.36/1.06  --sup_to_prop_solver                    passive
% 0.36/1.06  --sup_prop_simpl_new                    true
% 0.36/1.06  --sup_prop_simpl_given                  true
% 0.36/1.06  --sup_fun_splitting                     false
% 0.36/1.06  --sup_smt_interval                      50000
% 0.36/1.06  
% 0.36/1.06  ------ Superposition Simplification Setup
% 0.36/1.06  
% 0.36/1.06  --sup_indices_passive                   []
% 0.36/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.06  --sup_full_bw                           [BwDemod]
% 0.36/1.06  --sup_immed_triv                        [TrivRules]
% 0.36/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.06  --sup_immed_bw_main                     []
% 0.36/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.06  
% 0.36/1.06  ------ Combination Options
% 0.36/1.06  
% 0.36/1.06  --comb_res_mult                         3
% 0.36/1.06  --comb_sup_mult                         2
% 0.36/1.06  --comb_inst_mult                        10
% 0.36/1.06  
% 0.36/1.06  ------ Debug Options
% 0.36/1.06  
% 0.36/1.06  --dbg_backtrace                         false
% 0.36/1.06  --dbg_dump_prop_clauses                 false
% 0.36/1.06  --dbg_dump_prop_clauses_file            -
% 0.36/1.06  --dbg_out_stat                          false
% 0.36/1.06  ------ Parsing...
% 0.36/1.06  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 0.36/1.06  
% 0.36/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 0.36/1.06  
% 0.36/1.06  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 0.36/1.06  
% 0.36/1.06  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 0.36/1.06  ------ Proving...
% 0.36/1.06  ------ Problem Properties 
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  clauses                                 27
% 0.36/1.06  conjectures                             7
% 0.36/1.06  EPR                                     4
% 0.36/1.06  Horn                                    27
% 0.36/1.06  unary                                   8
% 0.36/1.06  binary                                  2
% 0.36/1.06  lits                                    101
% 0.36/1.06  lits eq                                 21
% 0.36/1.06  fd_pure                                 0
% 0.36/1.06  fd_pseudo                               0
% 0.36/1.06  fd_cond                                 0
% 0.36/1.06  fd_pseudo_cond                          1
% 0.36/1.06  AC symbols                              0
% 0.36/1.06  
% 0.36/1.06  ------ Schedule dynamic 5 is on 
% 0.36/1.06  
% 0.36/1.06  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  ------ 
% 0.36/1.06  Current options:
% 0.36/1.06  ------ 
% 0.36/1.06  
% 0.36/1.06  ------ Input Options
% 0.36/1.06  
% 0.36/1.06  --out_options                           all
% 0.36/1.06  --tptp_safe_out                         true
% 0.36/1.06  --problem_path                          ""
% 0.36/1.06  --include_path                          ""
% 0.36/1.06  --clausifier                            res/vclausify_rel
% 0.36/1.06  --clausifier_options                    --mode clausify
% 0.36/1.06  --stdin                                 false
% 0.36/1.06  --stats_out                             all
% 0.36/1.06  
% 0.36/1.06  ------ General Options
% 0.36/1.06  
% 0.36/1.06  --fof                                   false
% 0.36/1.06  --time_out_real                         305.
% 0.36/1.06  --time_out_virtual                      -1.
% 0.36/1.06  --symbol_type_check                     false
% 0.36/1.06  --clausify_out                          false
% 0.36/1.06  --sig_cnt_out                           false
% 0.36/1.06  --trig_cnt_out                          false
% 0.36/1.06  --trig_cnt_out_tolerance                1.
% 0.36/1.06  --trig_cnt_out_sk_spl                   false
% 0.36/1.06  --abstr_cl_out                          false
% 0.36/1.06  
% 0.36/1.06  ------ Global Options
% 0.36/1.06  
% 0.36/1.06  --schedule                              default
% 0.36/1.06  --add_important_lit                     false
% 0.36/1.06  --prop_solver_per_cl                    1000
% 0.36/1.06  --min_unsat_core                        false
% 0.36/1.06  --soft_assumptions                      false
% 0.36/1.06  --soft_lemma_size                       3
% 0.36/1.06  --prop_impl_unit_size                   0
% 0.36/1.06  --prop_impl_unit                        []
% 0.36/1.06  --share_sel_clauses                     true
% 0.36/1.06  --reset_solvers                         false
% 0.36/1.06  --bc_imp_inh                            [conj_cone]
% 0.36/1.06  --conj_cone_tolerance                   3.
% 0.36/1.06  --extra_neg_conj                        none
% 0.36/1.06  --large_theory_mode                     true
% 0.36/1.06  --prolific_symb_bound                   200
% 0.36/1.06  --lt_threshold                          2000
% 0.36/1.06  --clause_weak_htbl                      true
% 0.36/1.06  --gc_record_bc_elim                     false
% 0.36/1.06  
% 0.36/1.06  ------ Preprocessing Options
% 0.36/1.06  
% 0.36/1.06  --preprocessing_flag                    true
% 0.36/1.06  --time_out_prep_mult                    0.1
% 0.36/1.06  --splitting_mode                        input
% 0.36/1.06  --splitting_grd                         true
% 0.36/1.06  --splitting_cvd                         false
% 0.36/1.06  --splitting_cvd_svl                     false
% 0.36/1.06  --splitting_nvd                         32
% 0.36/1.06  --sub_typing                            true
% 0.36/1.06  --prep_gs_sim                           true
% 0.36/1.06  --prep_unflatten                        true
% 0.36/1.06  --prep_res_sim                          true
% 0.36/1.06  --prep_upred                            true
% 0.36/1.06  --prep_sem_filter                       exhaustive
% 0.36/1.06  --prep_sem_filter_out                   false
% 0.36/1.06  --pred_elim                             true
% 0.36/1.06  --res_sim_input                         true
% 0.36/1.06  --eq_ax_congr_red                       true
% 0.36/1.06  --pure_diseq_elim                       true
% 0.36/1.06  --brand_transform                       false
% 0.36/1.06  --non_eq_to_eq                          false
% 0.36/1.06  --prep_def_merge                        true
% 0.36/1.06  --prep_def_merge_prop_impl              false
% 0.36/1.06  --prep_def_merge_mbd                    true
% 0.36/1.06  --prep_def_merge_tr_red                 false
% 0.36/1.06  --prep_def_merge_tr_cl                  false
% 0.36/1.06  --smt_preprocessing                     true
% 0.36/1.06  --smt_ac_axioms                         fast
% 0.36/1.06  --preprocessed_out                      false
% 0.36/1.06  --preprocessed_stats                    false
% 0.36/1.06  
% 0.36/1.06  ------ Abstraction refinement Options
% 0.36/1.06  
% 0.36/1.06  --abstr_ref                             []
% 0.36/1.06  --abstr_ref_prep                        false
% 0.36/1.06  --abstr_ref_until_sat                   false
% 0.36/1.06  --abstr_ref_sig_restrict                funpre
% 0.36/1.06  --abstr_ref_af_restrict_to_split_sk     false
% 0.36/1.06  --abstr_ref_under                       []
% 0.36/1.06  
% 0.36/1.06  ------ SAT Options
% 0.36/1.06  
% 0.36/1.06  --sat_mode                              false
% 0.36/1.06  --sat_fm_restart_options                ""
% 0.36/1.06  --sat_gr_def                            false
% 0.36/1.06  --sat_epr_types                         true
% 0.36/1.06  --sat_non_cyclic_types                  false
% 0.36/1.06  --sat_finite_models                     false
% 0.36/1.06  --sat_fm_lemmas                         false
% 0.36/1.06  --sat_fm_prep                           false
% 0.36/1.06  --sat_fm_uc_incr                        true
% 0.36/1.06  --sat_out_model                         small
% 0.36/1.06  --sat_out_clauses                       false
% 0.36/1.06  
% 0.36/1.06  ------ QBF Options
% 0.36/1.06  
% 0.36/1.06  --qbf_mode                              false
% 0.36/1.06  --qbf_elim_univ                         false
% 0.36/1.06  --qbf_dom_inst                          none
% 0.36/1.06  --qbf_dom_pre_inst                      false
% 0.36/1.06  --qbf_sk_in                             false
% 0.36/1.06  --qbf_pred_elim                         true
% 0.36/1.06  --qbf_split                             512
% 0.36/1.06  
% 0.36/1.06  ------ BMC1 Options
% 0.36/1.06  
% 0.36/1.06  --bmc1_incremental                      false
% 0.36/1.06  --bmc1_axioms                           reachable_all
% 0.36/1.06  --bmc1_min_bound                        0
% 0.36/1.06  --bmc1_max_bound                        -1
% 0.36/1.06  --bmc1_max_bound_default                -1
% 0.36/1.06  --bmc1_symbol_reachability              true
% 0.36/1.06  --bmc1_property_lemmas                  false
% 0.36/1.06  --bmc1_k_induction                      false
% 0.36/1.06  --bmc1_non_equiv_states                 false
% 0.36/1.06  --bmc1_deadlock                         false
% 0.36/1.06  --bmc1_ucm                              false
% 0.36/1.06  --bmc1_add_unsat_core                   none
% 0.36/1.06  --bmc1_unsat_core_children              false
% 0.36/1.06  --bmc1_unsat_core_extrapolate_axioms    false
% 0.36/1.06  --bmc1_out_stat                         full
% 0.36/1.06  --bmc1_ground_init                      false
% 0.36/1.06  --bmc1_pre_inst_next_state              false
% 0.36/1.06  --bmc1_pre_inst_state                   false
% 0.36/1.06  --bmc1_pre_inst_reach_state             false
% 0.36/1.06  --bmc1_out_unsat_core                   false
% 0.36/1.06  --bmc1_aig_witness_out                  false
% 0.36/1.06  --bmc1_verbose                          false
% 0.36/1.06  --bmc1_dump_clauses_tptp                false
% 0.36/1.06  --bmc1_dump_unsat_core_tptp             false
% 0.36/1.06  --bmc1_dump_file                        -
% 0.36/1.06  --bmc1_ucm_expand_uc_limit              128
% 0.36/1.06  --bmc1_ucm_n_expand_iterations          6
% 0.36/1.06  --bmc1_ucm_extend_mode                  1
% 0.36/1.06  --bmc1_ucm_init_mode                    2
% 0.36/1.06  --bmc1_ucm_cone_mode                    none
% 0.36/1.06  --bmc1_ucm_reduced_relation_type        0
% 0.36/1.06  --bmc1_ucm_relax_model                  4
% 0.36/1.06  --bmc1_ucm_full_tr_after_sat            true
% 0.36/1.06  --bmc1_ucm_expand_neg_assumptions       false
% 0.36/1.06  --bmc1_ucm_layered_model                none
% 0.36/1.06  --bmc1_ucm_max_lemma_size               10
% 0.36/1.06  
% 0.36/1.06  ------ AIG Options
% 0.36/1.06  
% 0.36/1.06  --aig_mode                              false
% 0.36/1.06  
% 0.36/1.06  ------ Instantiation Options
% 0.36/1.06  
% 0.36/1.06  --instantiation_flag                    true
% 0.36/1.06  --inst_sos_flag                         false
% 0.36/1.06  --inst_sos_phase                        true
% 0.36/1.06  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 0.36/1.06  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 0.36/1.06  --inst_lit_sel_side                     none
% 0.36/1.06  --inst_solver_per_active                1400
% 0.36/1.06  --inst_solver_calls_frac                1.
% 0.36/1.06  --inst_passive_queue_type               priority_queues
% 0.36/1.06  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 0.36/1.06  --inst_passive_queues_freq              [25;2]
% 0.36/1.06  --inst_dismatching                      true
% 0.36/1.06  --inst_eager_unprocessed_to_passive     true
% 0.36/1.06  --inst_prop_sim_given                   true
% 0.36/1.06  --inst_prop_sim_new                     false
% 0.36/1.06  --inst_subs_new                         false
% 0.36/1.06  --inst_eq_res_simp                      false
% 0.36/1.06  --inst_subs_given                       false
% 0.36/1.06  --inst_orphan_elimination               true
% 0.36/1.06  --inst_learning_loop_flag               true
% 0.36/1.06  --inst_learning_start                   3000
% 0.36/1.06  --inst_learning_factor                  2
% 0.36/1.06  --inst_start_prop_sim_after_learn       3
% 0.36/1.06  --inst_sel_renew                        solver
% 0.36/1.06  --inst_lit_activity_flag                true
% 0.36/1.06  --inst_restr_to_given                   false
% 0.36/1.06  --inst_activity_threshold               500
% 0.36/1.06  --inst_out_proof                        true
% 0.36/1.06  
% 0.36/1.06  ------ Resolution Options
% 0.36/1.06  
% 0.36/1.06  --resolution_flag                       false
% 0.36/1.06  --res_lit_sel                           adaptive
% 0.36/1.06  --res_lit_sel_side                      none
% 0.36/1.06  --res_ordering                          kbo
% 0.36/1.06  --res_to_prop_solver                    active
% 0.36/1.06  --res_prop_simpl_new                    false
% 0.36/1.06  --res_prop_simpl_given                  true
% 0.36/1.06  --res_passive_queue_type                priority_queues
% 0.36/1.06  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 0.36/1.06  --res_passive_queues_freq               [15;5]
% 0.36/1.06  --res_forward_subs                      full
% 0.36/1.06  --res_backward_subs                     full
% 0.36/1.06  --res_forward_subs_resolution           true
% 0.36/1.06  --res_backward_subs_resolution          true
% 0.36/1.06  --res_orphan_elimination                true
% 0.36/1.06  --res_time_limit                        2.
% 0.36/1.06  --res_out_proof                         true
% 0.36/1.06  
% 0.36/1.06  ------ Superposition Options
% 0.36/1.06  
% 0.36/1.06  --superposition_flag                    true
% 0.36/1.06  --sup_passive_queue_type                priority_queues
% 0.36/1.06  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 0.36/1.06  --sup_passive_queues_freq               [8;1;4]
% 0.36/1.06  --demod_completeness_check              fast
% 0.36/1.06  --demod_use_ground                      true
% 0.36/1.06  --sup_to_prop_solver                    passive
% 0.36/1.06  --sup_prop_simpl_new                    true
% 0.36/1.06  --sup_prop_simpl_given                  true
% 0.36/1.06  --sup_fun_splitting                     false
% 0.36/1.06  --sup_smt_interval                      50000
% 0.36/1.06  
% 0.36/1.06  ------ Superposition Simplification Setup
% 0.36/1.06  
% 0.36/1.06  --sup_indices_passive                   []
% 0.36/1.06  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.06  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.06  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 0.36/1.06  --sup_full_triv                         [TrivRules;PropSubs]
% 0.36/1.06  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.06  --sup_full_bw                           [BwDemod]
% 0.36/1.06  --sup_immed_triv                        [TrivRules]
% 0.36/1.06  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 0.36/1.06  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.06  --sup_immed_bw_main                     []
% 0.36/1.06  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.06  --sup_input_triv                        [Unflattening;TrivRules]
% 0.36/1.06  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 0.36/1.06  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 0.36/1.06  
% 0.36/1.06  ------ Combination Options
% 0.36/1.06  
% 0.36/1.06  --comb_res_mult                         3
% 0.36/1.06  --comb_sup_mult                         2
% 0.36/1.06  --comb_inst_mult                        10
% 0.36/1.06  
% 0.36/1.06  ------ Debug Options
% 0.36/1.06  
% 0.36/1.06  --dbg_backtrace                         false
% 0.36/1.06  --dbg_dump_prop_clauses                 false
% 0.36/1.06  --dbg_dump_prop_clauses_file            -
% 0.36/1.06  --dbg_out_stat                          false
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  ------ Proving...
% 0.36/1.06  
% 0.36/1.06  
% 0.36/1.06  % SZS status Theorem for theBenchmark.p
% 0.36/1.06  
% 0.36/1.06   Resolution empty clause
% 0.36/1.06  
% 0.36/1.06  % SZS output start CNFRefutation for theBenchmark.p
% 0.36/1.06  
% 0.36/1.06  fof(f14,conjecture,(
% 0.36/1.06    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f15,negated_conjecture,(
% 0.36/1.06    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.36/1.06    inference(negated_conjecture,[],[f14])).
% 0.36/1.06  
% 0.36/1.06  fof(f37,plain,(
% 0.36/1.06    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.36/1.06    inference(ennf_transformation,[],[f15])).
% 0.36/1.06  
% 0.36/1.06  fof(f38,plain,(
% 0.36/1.06    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.36/1.06    inference(flattening,[],[f37])).
% 0.36/1.06  
% 0.36/1.06  fof(f42,plain,(
% 0.36/1.06    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 0.36/1.06    introduced(choice_axiom,[])).
% 0.36/1.06  
% 0.36/1.06  fof(f41,plain,(
% 0.36/1.06    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 0.36/1.06    introduced(choice_axiom,[])).
% 0.36/1.06  
% 0.36/1.06  fof(f40,plain,(
% 0.36/1.06    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.36/1.06    introduced(choice_axiom,[])).
% 0.36/1.06  
% 0.36/1.06  fof(f43,plain,(
% 0.36/1.06    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.36/1.06    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f38,f42,f41,f40])).
% 0.36/1.06  
% 0.36/1.06  fof(f65,plain,(
% 0.36/1.06    l1_struct_0(sK0)),
% 0.36/1.06    inference(cnf_transformation,[],[f43])).
% 0.36/1.06  
% 0.36/1.06  fof(f9,axiom,(
% 0.36/1.06    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f28,plain,(
% 0.36/1.06    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.36/1.06    inference(ennf_transformation,[],[f9])).
% 0.36/1.06  
% 0.36/1.06  fof(f57,plain,(
% 0.36/1.06    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f28])).
% 0.36/1.06  
% 0.36/1.06  fof(f67,plain,(
% 0.36/1.06    l1_struct_0(sK1)),
% 0.36/1.06    inference(cnf_transformation,[],[f43])).
% 0.36/1.06  
% 0.36/1.06  fof(f71,plain,(
% 0.36/1.06    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.36/1.06    inference(cnf_transformation,[],[f43])).
% 0.36/1.06  
% 0.36/1.06  fof(f70,plain,(
% 0.36/1.06    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.36/1.06    inference(cnf_transformation,[],[f43])).
% 0.36/1.06  
% 0.36/1.06  fof(f6,axiom,(
% 0.36/1.06    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f23,plain,(
% 0.36/1.06    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.36/1.06    inference(ennf_transformation,[],[f6])).
% 0.36/1.06  
% 0.36/1.06  fof(f51,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.36/1.06    inference(cnf_transformation,[],[f23])).
% 0.36/1.06  
% 0.36/1.06  fof(f12,axiom,(
% 0.36/1.06    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f33,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (! [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.36/1.06    inference(ennf_transformation,[],[f12])).
% 0.36/1.06  
% 0.36/1.06  fof(f34,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (! [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.36/1.06    inference(flattening,[],[f33])).
% 0.36/1.06  
% 0.36/1.06  fof(f63,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f34])).
% 0.36/1.06  
% 0.36/1.06  fof(f66,plain,(
% 0.36/1.06    ~v2_struct_0(sK1)),
% 0.36/1.06    inference(cnf_transformation,[],[f43])).
% 0.36/1.06  
% 0.36/1.06  fof(f68,plain,(
% 0.36/1.06    v1_funct_1(sK2)),
% 0.36/1.06    inference(cnf_transformation,[],[f43])).
% 0.36/1.06  
% 0.36/1.06  fof(f72,plain,(
% 0.36/1.06    v2_funct_1(sK2)),
% 0.36/1.06    inference(cnf_transformation,[],[f43])).
% 0.36/1.06  
% 0.36/1.06  fof(f69,plain,(
% 0.36/1.06    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.36/1.06    inference(cnf_transformation,[],[f43])).
% 0.36/1.06  
% 0.36/1.06  fof(f10,axiom,(
% 0.36/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f29,plain,(
% 0.36/1.06    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.36/1.06    inference(ennf_transformation,[],[f10])).
% 0.36/1.06  
% 0.36/1.06  fof(f30,plain,(
% 0.36/1.06    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.36/1.06    inference(flattening,[],[f29])).
% 0.36/1.06  
% 0.36/1.06  fof(f58,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f30])).
% 0.36/1.06  
% 0.36/1.06  fof(f11,axiom,(
% 0.36/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f31,plain,(
% 0.36/1.06    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.36/1.06    inference(ennf_transformation,[],[f11])).
% 0.36/1.06  
% 0.36/1.06  fof(f32,plain,(
% 0.36/1.06    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.36/1.06    inference(flattening,[],[f31])).
% 0.36/1.06  
% 0.36/1.06  fof(f61,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f32])).
% 0.36/1.06  
% 0.36/1.06  fof(f3,axiom,(
% 0.36/1.06    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f17,plain,(
% 0.36/1.06    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.36/1.06    inference(ennf_transformation,[],[f3])).
% 0.36/1.06  
% 0.36/1.06  fof(f18,plain,(
% 0.36/1.06    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.36/1.06    inference(flattening,[],[f17])).
% 0.36/1.06  
% 0.36/1.06  fof(f47,plain,(
% 0.36/1.06    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f18])).
% 0.36/1.06  
% 0.36/1.06  fof(f1,axiom,(
% 0.36/1.06    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f16,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.36/1.06    inference(ennf_transformation,[],[f1])).
% 0.36/1.06  
% 0.36/1.06  fof(f44,plain,(
% 0.36/1.06    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f16])).
% 0.36/1.06  
% 0.36/1.06  fof(f2,axiom,(
% 0.36/1.06    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f45,plain,(
% 0.36/1.06    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.36/1.06    inference(cnf_transformation,[],[f2])).
% 0.36/1.06  
% 0.36/1.06  fof(f13,axiom,(
% 0.36/1.06    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f35,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.36/1.06    inference(ennf_transformation,[],[f13])).
% 0.36/1.06  
% 0.36/1.06  fof(f36,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.36/1.06    inference(flattening,[],[f35])).
% 0.36/1.06  
% 0.36/1.06  fof(f64,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f36])).
% 0.36/1.06  
% 0.36/1.06  fof(f4,axiom,(
% 0.36/1.06    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f19,plain,(
% 0.36/1.06    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.36/1.06    inference(ennf_transformation,[],[f4])).
% 0.36/1.06  
% 0.36/1.06  fof(f20,plain,(
% 0.36/1.06    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.36/1.06    inference(flattening,[],[f19])).
% 0.36/1.06  
% 0.36/1.06  fof(f48,plain,(
% 0.36/1.06    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f20])).
% 0.36/1.06  
% 0.36/1.06  fof(f5,axiom,(
% 0.36/1.06    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f21,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.36/1.06    inference(ennf_transformation,[],[f5])).
% 0.36/1.06  
% 0.36/1.06  fof(f22,plain,(
% 0.36/1.06    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.36/1.06    inference(flattening,[],[f21])).
% 0.36/1.06  
% 0.36/1.06  fof(f50,plain,(
% 0.36/1.06    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f22])).
% 0.36/1.06  
% 0.36/1.06  fof(f46,plain,(
% 0.36/1.06    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f18])).
% 0.36/1.06  
% 0.36/1.06  fof(f8,axiom,(
% 0.36/1.06    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f26,plain,(
% 0.36/1.06    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.36/1.06    inference(ennf_transformation,[],[f8])).
% 0.36/1.06  
% 0.36/1.06  fof(f27,plain,(
% 0.36/1.06    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.36/1.06    inference(flattening,[],[f26])).
% 0.36/1.06  
% 0.36/1.06  fof(f54,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f27])).
% 0.36/1.06  
% 0.36/1.06  fof(f56,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f27])).
% 0.36/1.06  
% 0.36/1.06  fof(f55,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f27])).
% 0.36/1.06  
% 0.36/1.06  fof(f7,axiom,(
% 0.36/1.06    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.36/1.06    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 0.36/1.06  
% 0.36/1.06  fof(f24,plain,(
% 0.36/1.06    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.36/1.06    inference(ennf_transformation,[],[f7])).
% 0.36/1.06  
% 0.36/1.06  fof(f25,plain,(
% 0.36/1.06    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.36/1.06    inference(flattening,[],[f24])).
% 0.36/1.06  
% 0.36/1.06  fof(f39,plain,(
% 0.36/1.06    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.36/1.06    inference(nnf_transformation,[],[f25])).
% 0.36/1.06  
% 0.36/1.06  fof(f53,plain,(
% 0.36/1.06    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f39])).
% 0.36/1.06  
% 0.36/1.06  fof(f74,plain,(
% 0.36/1.06    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.36/1.06    inference(equality_resolution,[],[f53])).
% 0.36/1.06  
% 0.36/1.06  fof(f73,plain,(
% 0.36/1.06    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.36/1.06    inference(cnf_transformation,[],[f43])).
% 0.36/1.06  
% 0.36/1.06  fof(f59,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f32])).
% 0.36/1.06  
% 0.36/1.06  fof(f60,plain,(
% 0.36/1.06    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.36/1.06    inference(cnf_transformation,[],[f32])).
% 0.36/1.06  
% 0.36/1.06  cnf(c_29,negated_conjecture,
% 0.36/1.06      ( l1_struct_0(sK0) ),
% 0.36/1.06      inference(cnf_transformation,[],[f65]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_608,negated_conjecture,
% 0.36/1.06      ( l1_struct_0(sK0) ),
% 0.36/1.06      inference(subtyping,[status(esa)],[c_29]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1164,plain,
% 0.36/1.06      ( l1_struct_0(sK0) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_608]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_13,plain,
% 0.36/1.06      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 0.36/1.06      inference(cnf_transformation,[],[f57]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_620,plain,
% 0.36/1.06      ( ~ l1_struct_0(X0_53) | u1_struct_0(X0_53) = k2_struct_0(X0_53) ),
% 0.36/1.06      inference(subtyping,[status(esa)],[c_13]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1153,plain,
% 0.36/1.06      ( u1_struct_0(X0_53) = k2_struct_0(X0_53)
% 0.36/1.06      | l1_struct_0(X0_53) != iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_620]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1598,plain,
% 0.36/1.06      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1164,c_1153]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_27,negated_conjecture,
% 0.36/1.06      ( l1_struct_0(sK1) ),
% 0.36/1.06      inference(cnf_transformation,[],[f67]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_609,negated_conjecture,
% 0.36/1.06      ( l1_struct_0(sK1) ),
% 0.36/1.06      inference(subtyping,[status(esa)],[c_27]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1163,plain,
% 0.36/1.06      ( l1_struct_0(sK1) = iProver_top ),
% 0.36/1.06      inference(predicate_to_equality,[status(thm)],[c_609]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1597,plain,
% 0.36/1.06      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 0.36/1.06      inference(superposition,[status(thm)],[c_1163,c_1153]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_23,negated_conjecture,
% 0.36/1.06      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 0.36/1.06      inference(cnf_transformation,[],[f71]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_613,negated_conjecture,
% 0.36/1.06      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 0.36/1.06      inference(subtyping,[status(esa)],[c_23]) ).
% 0.36/1.06  
% 0.36/1.06  cnf(c_1720,plain,
% 0.36/1.06      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 0.36/1.06      inference(demodulation,[status(thm)],[c_1597,c_613]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1779,plain,
% 1.73/1.06      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.73/1.06      inference(demodulation,[status(thm)],[c_1598,c_1720]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_24,negated_conjecture,
% 1.73/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.73/1.06      inference(cnf_transformation,[],[f70]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_612,negated_conjecture,
% 1.73/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_24]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1160,plain,
% 1.73/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_612]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_7,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.06      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.73/1.06      inference(cnf_transformation,[],[f51]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_624,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.73/1.06      | k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_7]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1149,plain,
% 1.73/1.06      ( k2_relset_1(X0_52,X1_52,X0_51) = k2_relat_1(X0_51)
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_624]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1606,plain,
% 1.73/1.06      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1160,c_1149]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1834,plain,
% 1.73/1.06      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_1606,c_1597,c_1598]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1836,plain,
% 1.73/1.06      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_1779,c_1834]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1838,plain,
% 1.73/1.06      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 1.73/1.06      inference(demodulation,[status(thm)],[c_1836,c_1834]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_18,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.73/1.06      | v2_struct_0(X2)
% 1.73/1.06      | ~ l1_struct_0(X1)
% 1.73/1.06      | ~ l1_struct_0(X2)
% 1.73/1.06      | ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 1.73/1.06      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f63]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_28,negated_conjecture,
% 1.73/1.06      ( ~ v2_struct_0(sK1) ),
% 1.73/1.06      inference(cnf_transformation,[],[f66]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_380,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.73/1.06      | ~ l1_struct_0(X1)
% 1.73/1.06      | ~ l1_struct_0(X2)
% 1.73/1.06      | ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 1.73/1.06      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 1.73/1.06      | sK1 != X2 ),
% 1.73/1.06      inference(resolution_lifted,[status(thm)],[c_18,c_28]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_381,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 1.73/1.06      | ~ l1_struct_0(X1)
% 1.73/1.06      | ~ l1_struct_0(sK1)
% 1.73/1.06      | ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 1.73/1.06      inference(unflattening,[status(thm)],[c_380]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_385,plain,
% 1.73/1.06      ( ~ l1_struct_0(X1)
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 1.73/1.06      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 1.73/1.06      | ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 1.73/1.06      inference(global_propositional_subsumption,[status(thm)],[c_381,c_27]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_386,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 1.73/1.06      | ~ l1_struct_0(X1)
% 1.73/1.06      | ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 1.73/1.06      inference(renaming,[status(thm)],[c_385]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_605,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1))))
% 1.73/1.06      | ~ l1_struct_0(X0_53)
% 1.73/1.06      | ~ v1_funct_1(X0_51)
% 1.73/1.06      | ~ v2_funct_1(X0_51)
% 1.73/1.06      | k2_relset_1(u1_struct_0(X0_53),u1_struct_0(sK1),X0_51) != k2_struct_0(sK1)
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_53),k2_tops_2(u1_struct_0(X0_53),u1_struct_0(sK1),X0_51)) = k2_struct_0(X0_53) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_386]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1167,plain,
% 1.73/1.06      ( k2_relset_1(u1_struct_0(X0_53),u1_struct_0(sK1),X0_51) != k2_struct_0(sK1)
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_53),k2_tops_2(u1_struct_0(X0_53),u1_struct_0(sK1),X0_51)) = k2_struct_0(X0_53)
% 1.73/1.06      | v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 1.73/1.06      | l1_struct_0(X0_53) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_605]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2325,plain,
% 1.73/1.06      ( k2_relset_1(u1_struct_0(X0_53),u1_struct_0(sK1),X0_51) != k2_relat_1(sK2)
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_53),k2_tops_2(u1_struct_0(X0_53),u1_struct_0(sK1),X0_51)) = k2_struct_0(X0_53)
% 1.73/1.06      | v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(sK1)))) != iProver_top
% 1.73/1.06      | l1_struct_0(X0_53) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_1167,c_1836]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2336,plain,
% 1.73/1.06      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
% 1.73/1.06      | k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_relat_1(sK2)
% 1.73/1.06      | v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.73/1.06      | l1_struct_0(sK0) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1598,c_2325]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2337,plain,
% 1.73/1.06      ( k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
% 1.73/1.06      | k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_relat_1(sK2)
% 1.73/1.06      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.73/1.06      | l1_struct_0(sK0) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_2336,c_1598]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_30,plain,
% 1.73/1.06      ( l1_struct_0(sK0) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2669,plain,
% 1.73/1.06      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.73/1.06      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_relat_1(sK2)
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(global_propositional_subsumption,[status(thm)],[c_2337,c_30]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2670,plain,
% 1.73/1.06      ( k2_relset_1(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0_51)) = k2_struct_0(sK0)
% 1.73/1.06      | k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),X0_51) != k2_relat_1(sK2)
% 1.73/1.06      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(renaming,[status(thm)],[c_2669]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1840,plain,
% 1.73/1.06      ( u1_struct_0(sK1) = k2_relat_1(sK2) ),
% 1.73/1.06      inference(demodulation,[status(thm)],[c_1836,c_1597]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2675,plain,
% 1.73/1.06      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
% 1.73/1.06      | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = k2_struct_0(sK0)
% 1.73/1.06      | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_2670,c_1840]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2838,plain,
% 1.73/1.06      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_struct_0(sK0)
% 1.73/1.06      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.73/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1838,c_2675]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_26,negated_conjecture,
% 1.73/1.06      ( v1_funct_1(sK2) ),
% 1.73/1.06      inference(cnf_transformation,[],[f68]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_33,plain,
% 1.73/1.06      ( v1_funct_1(sK2) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_22,negated_conjecture,
% 1.73/1.06      ( v2_funct_1(sK2) ),
% 1.73/1.06      inference(cnf_transformation,[],[f72]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_36,plain,
% 1.73/1.06      ( v2_funct_1(sK2) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_25,negated_conjecture,
% 1.73/1.06      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.73/1.06      inference(cnf_transformation,[],[f69]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_611,negated_conjecture,
% 1.73/1.06      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_25]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1161,plain,
% 1.73/1.06      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_611]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1719,plain,
% 1.73/1.06      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 1.73/1.06      inference(demodulation,[status(thm)],[c_1597,c_1161]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1781,plain,
% 1.73/1.06      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_1719,c_1598]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1839,plain,
% 1.73/1.06      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 1.73/1.06      inference(demodulation,[status(thm)],[c_1836,c_1781]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1718,plain,
% 1.73/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 1.73/1.06      inference(demodulation,[status(thm)],[c_1597,c_1160]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1867,plain,
% 1.73/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_1718,c_1598,c_1836]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2683,plain,
% 1.73/1.06      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 1.73/1.06      | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_struct_0(sK0)
% 1.73/1.06      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.73/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2675]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_5988,plain,
% 1.73/1.06      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_struct_0(sK0) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_2838,c_33,c_36,c_1838,c_1839,c_1867,c_2683]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_14,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.06      | ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 1.73/1.06      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.73/1.06      inference(cnf_transformation,[],[f58]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_619,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 1.73/1.06      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.73/1.06      | ~ v1_funct_1(X0_51)
% 1.73/1.06      | ~ v2_funct_1(X0_51)
% 1.73/1.06      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 1.73/1.06      | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_14]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1154,plain,
% 1.73/1.06      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 1.73/1.06      | k2_tops_2(X0_52,X1_52,X0_51) = k2_funct_1(X0_51)
% 1.73/1.06      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_619]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2834,plain,
% 1.73/1.06      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 1.73/1.06      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.73/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1838,c_1154]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_4402,plain,
% 1.73/1.06      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_2834,c_33,c_36,c_1839,c_1867]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_15,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.06      | m1_subset_1(k2_tops_2(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.73/1.06      | ~ v1_funct_1(X0) ),
% 1.73/1.06      inference(cnf_transformation,[],[f61]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_618,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 1.73/1.06      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.73/1.06      | m1_subset_1(k2_tops_2(X0_52,X1_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
% 1.73/1.06      | ~ v1_funct_1(X0_51) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_15]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1155,plain,
% 1.73/1.06      ( v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 1.73/1.06      | m1_subset_1(k2_tops_2(X0_52,X1_52,X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2408,plain,
% 1.73/1.06      ( k2_relset_1(X0_52,X1_52,k2_tops_2(X1_52,X0_52,X0_51)) = k2_relat_1(k2_tops_2(X1_52,X0_52,X0_51))
% 1.73/1.06      | v1_funct_2(X0_51,X1_52,X0_52) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1155,c_1149]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3280,plain,
% 1.73/1.06      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
% 1.73/1.06      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1867,c_2408]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3711,plain,
% 1.73/1.06      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_relat_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_3280,c_33,c_1839]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_4406,plain,
% 1.73/1.06      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 1.73/1.06      inference(demodulation,[status(thm)],[c_4402,c_3711]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_610,negated_conjecture,
% 1.73/1.06      ( v1_funct_1(sK2) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_26]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1162,plain,
% 1.73/1.06      ( v1_funct_1(sK2) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_610]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2,plain,
% 1.73/1.06      ( ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | ~ v1_relat_1(X0)
% 1.73/1.06      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 1.73/1.06      inference(cnf_transformation,[],[f47]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_629,plain,
% 1.73/1.06      ( ~ v1_funct_1(X0_51)
% 1.73/1.06      | ~ v2_funct_1(X0_51)
% 1.73/1.06      | ~ v1_relat_1(X0_51)
% 1.73/1.06      | k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_2]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1144,plain,
% 1.73/1.06      ( k2_relat_1(k2_funct_1(X0_51)) = k1_relat_1(X0_51)
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v1_relat_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1654,plain,
% 1.73/1.06      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top
% 1.73/1.06      | v1_relat_1(sK2) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1162,c_1144]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_0,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 1.73/1.06      inference(cnf_transformation,[],[f44]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_631,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(X1_51))
% 1.73/1.06      | ~ v1_relat_1(X1_51)
% 1.73/1.06      | v1_relat_1(X0_51) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_0]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1142,plain,
% 1.73/1.06      ( m1_subset_1(X0_51,k1_zfmisc_1(X1_51)) != iProver_top
% 1.73/1.06      | v1_relat_1(X1_51) != iProver_top
% 1.73/1.06      | v1_relat_1(X0_51) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1537,plain,
% 1.73/1.06      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 1.73/1.06      | v1_relat_1(sK2) = iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1160,c_1142]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1538,plain,
% 1.73/1.06      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 1.73/1.06      | v1_relat_1(sK2) ),
% 1.73/1.06      inference(predicate_to_equality_rev,[status(thm)],[c_1537]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1655,plain,
% 1.73/1.06      ( ~ v2_funct_1(sK2)
% 1.73/1.06      | ~ v1_relat_1(sK2)
% 1.73/1.06      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.73/1.06      inference(predicate_to_equality_rev,[status(thm)],[c_1654]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1,plain,
% 1.73/1.06      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.73/1.06      inference(cnf_transformation,[],[f45]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_630,plain,
% 1.73/1.06      ( v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_1]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1660,plain,
% 1.73/1.06      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_630]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2199,plain,
% 1.73/1.06      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_1654,c_22,c_1538,c_1655,c_1660]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_4416,plain,
% 1.73/1.06      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_4406,c_2199]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_5990,plain,
% 1.73/1.06      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_5988,c_4402,c_4416]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_20,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 1.73/1.06      | ~ l1_struct_0(X1)
% 1.73/1.06      | ~ l1_struct_0(X2)
% 1.73/1.06      | ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 1.73/1.06      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 1.73/1.06      inference(cnf_transformation,[],[f64]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_615,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53))
% 1.73/1.06      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53))))
% 1.73/1.06      | ~ l1_struct_0(X1_53)
% 1.73/1.06      | ~ l1_struct_0(X0_53)
% 1.73/1.06      | ~ v1_funct_1(X0_51)
% 1.73/1.06      | ~ v2_funct_1(X0_51)
% 1.73/1.06      | v2_funct_1(k2_tops_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51))
% 1.73/1.06      | k2_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51) != k2_struct_0(X1_53) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_20]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1158,plain,
% 1.73/1.06      ( k2_relset_1(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51) != k2_struct_0(X1_53)
% 1.73/1.06      | v1_funct_2(X0_51,u1_struct_0(X0_53),u1_struct_0(X1_53)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_53),u1_struct_0(X1_53)))) != iProver_top
% 1.73/1.06      | l1_struct_0(X0_53) != iProver_top
% 1.73/1.06      | l1_struct_0(X1_53) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_tops_2(u1_struct_0(X0_53),u1_struct_0(X1_53),X0_51)) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_615]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3017,plain,
% 1.73/1.06      ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
% 1.73/1.06      | v1_funct_2(X0_51,u1_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 1.73/1.06      | l1_struct_0(X0_53) != iProver_top
% 1.73/1.06      | l1_struct_0(sK0) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1598,c_1158]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3080,plain,
% 1.73/1.06      ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
% 1.73/1.06      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 1.73/1.06      | l1_struct_0(X0_53) != iProver_top
% 1.73/1.06      | l1_struct_0(sK0) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_3017,c_1598]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3538,plain,
% 1.73/1.06      ( l1_struct_0(X0_53) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 1.73/1.06      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 1.73/1.06      | k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
% 1.73/1.06      inference(global_propositional_subsumption,[status(thm)],[c_3080,c_30]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3539,plain,
% 1.73/1.06      ( k2_relset_1(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51) != k2_struct_0(X0_53)
% 1.73/1.06      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(X0_53)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0_53)))) != iProver_top
% 1.73/1.06      | l1_struct_0(X0_53) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X0_53),X0_51)) = iProver_top ),
% 1.73/1.06      inference(renaming,[status(thm)],[c_3538]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3552,plain,
% 1.73/1.06      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_struct_0(sK1)
% 1.73/1.06      | v1_funct_2(X0_51,k2_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.73/1.06      | l1_struct_0(sK1) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),X0_51)) = iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1840,c_3539]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3560,plain,
% 1.73/1.06      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
% 1.73/1.06      | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.73/1.06      | l1_struct_0(sK1) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_3552,c_1836,c_1840]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_32,plain,
% 1.73/1.06      ( l1_struct_0(sK1) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3881,plain,
% 1.73/1.06      ( m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.73/1.06      | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.73/1.06      | k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
% 1.73/1.06      inference(global_propositional_subsumption,[status(thm)],[c_3560,c_32]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3882,plain,
% 1.73/1.06      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),X0_51) != k2_relat_1(sK2)
% 1.73/1.06      | v1_funct_2(X0_51,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),X0_51)) = iProver_top ),
% 1.73/1.06      inference(renaming,[status(thm)],[c_3881]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3893,plain,
% 1.73/1.06      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.73/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = iProver_top
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1838,c_3882]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3577,plain,
% 1.73/1.06      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 1.73/1.06      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.73/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.73/1.06      | l1_struct_0(sK1) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = iProver_top
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_3560]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_5875,plain,
% 1.73/1.06      ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = iProver_top ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_3893,c_32,c_33,c_36,c_1838,c_1839,c_1867,c_3577]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_5879,plain,
% 1.73/1.06      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_5875,c_4402]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_5,plain,
% 1.73/1.06      ( ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | ~ v1_relat_1(X0)
% 1.73/1.06      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 1.73/1.06      inference(cnf_transformation,[],[f48]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_626,plain,
% 1.73/1.06      ( ~ v1_funct_1(X0_51)
% 1.73/1.06      | ~ v2_funct_1(X0_51)
% 1.73/1.06      | ~ v1_relat_1(X0_51)
% 1.73/1.06      | k5_relat_1(X0_51,k2_funct_1(X0_51)) = k6_relat_1(k1_relat_1(X0_51)) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_5]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1147,plain,
% 1.73/1.06      ( k5_relat_1(X0_51,k2_funct_1(X0_51)) = k6_relat_1(k1_relat_1(X0_51))
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v1_relat_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1940,plain,
% 1.73/1.06      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top
% 1.73/1.06      | v1_relat_1(sK2) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1162,c_1147]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_687,plain,
% 1.73/1.06      ( ~ v1_funct_1(sK2)
% 1.73/1.06      | ~ v2_funct_1(sK2)
% 1.73/1.06      | ~ v1_relat_1(sK2)
% 1.73/1.06      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_626]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2262,plain,
% 1.73/1.06      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_1940,c_26,c_22,c_687,c_1538,c_1660]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_6,plain,
% 1.73/1.06      ( ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v1_funct_1(X1)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | ~ v1_relat_1(X0)
% 1.73/1.06      | ~ v1_relat_1(X1)
% 1.73/1.06      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
% 1.73/1.06      | k1_relat_1(X0) != k2_relat_1(X1)
% 1.73/1.06      | k2_funct_1(X0) = X1 ),
% 1.73/1.06      inference(cnf_transformation,[],[f50]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_625,plain,
% 1.73/1.06      ( ~ v1_funct_1(X0_51)
% 1.73/1.06      | ~ v1_funct_1(X1_51)
% 1.73/1.06      | ~ v2_funct_1(X0_51)
% 1.73/1.06      | ~ v1_relat_1(X0_51)
% 1.73/1.06      | ~ v1_relat_1(X1_51)
% 1.73/1.06      | k5_relat_1(X1_51,X0_51) != k6_relat_1(k2_relat_1(X0_51))
% 1.73/1.06      | k1_relat_1(X0_51) != k2_relat_1(X1_51)
% 1.73/1.06      | k2_funct_1(X0_51) = X1_51 ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_6]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1148,plain,
% 1.73/1.06      ( k5_relat_1(X0_51,X1_51) != k6_relat_1(k2_relat_1(X1_51))
% 1.73/1.06      | k1_relat_1(X1_51) != k2_relat_1(X0_51)
% 1.73/1.06      | k2_funct_1(X1_51) = X0_51
% 1.73/1.06      | v1_funct_1(X1_51) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X1_51) != iProver_top
% 1.73/1.06      | v1_relat_1(X0_51) != iProver_top
% 1.73/1.06      | v1_relat_1(X1_51) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2384,plain,
% 1.73/1.06      ( k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
% 1.73/1.06      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 1.73/1.06      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 1.73/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.73/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 1.73/1.06      | v1_relat_1(sK2) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_2262,c_1148]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3,plain,
% 1.73/1.06      ( ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | ~ v1_relat_1(X0)
% 1.73/1.06      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 1.73/1.06      inference(cnf_transformation,[],[f46]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_628,plain,
% 1.73/1.06      ( ~ v1_funct_1(X0_51)
% 1.73/1.06      | ~ v2_funct_1(X0_51)
% 1.73/1.06      | ~ v1_relat_1(X0_51)
% 1.73/1.06      | k1_relat_1(k2_funct_1(X0_51)) = k2_relat_1(X0_51) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_3]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1145,plain,
% 1.73/1.06      ( k1_relat_1(k2_funct_1(X0_51)) = k2_relat_1(X0_51)
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v1_relat_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_628]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1882,plain,
% 1.73/1.06      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top
% 1.73/1.06      | v1_relat_1(sK2) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1162,c_1145]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_681,plain,
% 1.73/1.06      ( ~ v1_funct_1(sK2)
% 1.73/1.06      | ~ v2_funct_1(sK2)
% 1.73/1.06      | ~ v1_relat_1(sK2)
% 1.73/1.06      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_628]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2203,plain,
% 1.73/1.06      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_1882,c_26,c_22,c_681,c_1538,c_1660]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2393,plain,
% 1.73/1.06      ( k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
% 1.73/1.06      | k2_relat_1(sK2) != k2_relat_1(sK2)
% 1.73/1.06      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 1.73/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.73/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 1.73/1.06      | v1_relat_1(sK2) != iProver_top ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_2384,c_2199,c_2203]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2394,plain,
% 1.73/1.06      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 1.73/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.73/1.06      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 1.73/1.06      | v1_relat_1(sK2) != iProver_top ),
% 1.73/1.06      inference(equality_resolution_simp,[status(thm)],[c_2393]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_34,plain,
% 1.73/1.06      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_35,plain,
% 1.73/1.06      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_705,plain,
% 1.73/1.06      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_620]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_12,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.06      | ~ v1_funct_1(X0)
% 1.73/1.06      | v1_funct_1(k2_funct_1(X0))
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.73/1.06      inference(cnf_transformation,[],[f54]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_621,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 1.73/1.06      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.73/1.06      | ~ v1_funct_1(X0_51)
% 1.73/1.06      | v1_funct_1(k2_funct_1(X0_51))
% 1.73/1.06      | ~ v2_funct_1(X0_51)
% 1.73/1.06      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_12]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1518,plain,
% 1.73/1.06      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.73/1.06      | v1_funct_1(k2_funct_1(sK2))
% 1.73/1.06      | ~ v1_funct_1(sK2)
% 1.73/1.06      | ~ v2_funct_1(sK2)
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_621]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1519,plain,
% 1.73/1.06      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 1.73/1.06      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.73/1.06      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_1518]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_10,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.06      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.73/1.06      | ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.73/1.06      inference(cnf_transformation,[],[f56]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_623,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 1.73/1.06      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.73/1.06      | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52)))
% 1.73/1.06      | ~ v1_funct_1(X0_51)
% 1.73/1.06      | ~ v2_funct_1(X0_51)
% 1.73/1.06      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_10]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1524,plain,
% 1.73/1.06      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.73/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.73/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.73/1.06      | ~ v1_funct_1(sK2)
% 1.73/1.06      | ~ v2_funct_1(sK2)
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_623]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1525,plain,
% 1.73/1.06      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 1.73/1.06      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 1.73/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_1524]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1661,plain,
% 1.73/1.06      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_1660]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1753,plain,
% 1.73/1.06      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_630]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1754,plain,
% 1.73/1.06      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_1753]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_638,plain,
% 1.73/1.06      ( X0_52 != X1_52 | X2_52 != X1_52 | X2_52 = X0_52 ),
% 1.73/1.06      theory(equality) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1590,plain,
% 1.73/1.06      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_52
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 1.73/1.06      | u1_struct_0(sK1) != X0_52 ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_638]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1756,plain,
% 1.73/1.06      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 1.73/1.06      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_1590]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1436,plain,
% 1.73/1.06      ( ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.73/1.06      | v1_relat_1(X0_51)
% 1.73/1.06      | ~ v1_relat_1(k2_zfmisc_1(X0_52,X1_52)) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_631]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2021,plain,
% 1.73/1.06      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.73/1.06      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 1.73/1.06      | v1_relat_1(k2_funct_1(sK2)) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_1436]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2025,plain,
% 1.73/1.06      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 1.73/1.06      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 1.73/1.06      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_2021]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3771,plain,
% 1.73/1.06      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 1.73/1.06      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_2394,c_27,c_33,c_34,c_35,c_36,c_705,c_613,c_1519,c_1525,
% 1.73/1.06                 c_1537,c_1661,c_1754,c_1756,c_2025]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_5882,plain,
% 1.73/1.06      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_5879,c_3771]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_4540,plain,
% 1.73/1.06      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 1.73/1.06      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 1.73/1.06      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 1.73/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 1.73/1.06      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_4416,c_1154]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1527,plain,
% 1.73/1.06      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.73/1.06      | ~ v1_funct_1(sK2)
% 1.73/1.06      | ~ v2_funct_1(sK2)
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 1.73/1.06      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_619]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1530,plain,
% 1.73/1.06      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.73/1.06      | ~ l1_struct_0(sK1)
% 1.73/1.06      | ~ l1_struct_0(sK0)
% 1.73/1.06      | ~ v1_funct_1(sK2)
% 1.73/1.06      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.73/1.06      | ~ v2_funct_1(sK2)
% 1.73/1.06      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_615]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1531,plain,
% 1.73/1.06      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 1.73/1.06      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.73/1.06      | l1_struct_0(sK1) != iProver_top
% 1.73/1.06      | l1_struct_0(sK0) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = iProver_top
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_1530]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_633,plain,( X0_51 = X0_51 ),theory(equality) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2215,plain,
% 1.73/1.06      ( k2_funct_1(sK2) = k2_funct_1(sK2) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_633]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_11,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 1.73/1.06      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.06      | ~ v1_funct_1(X0)
% 1.73/1.06      | ~ v2_funct_1(X0)
% 1.73/1.06      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.73/1.06      inference(cnf_transformation,[],[f55]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_622,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 1.73/1.06      | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52)
% 1.73/1.06      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.73/1.06      | ~ v1_funct_1(X0_51)
% 1.73/1.06      | ~ v2_funct_1(X0_51)
% 1.73/1.06      | k2_relset_1(X0_52,X1_52,X0_51) != X1_52 ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_11]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1151,plain,
% 1.73/1.06      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 1.73/1.06      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 1.73/1.06      | v1_funct_2(k2_funct_1(X0_51),X1_52,X0_52) = iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2835,plain,
% 1.73/1.06      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 1.73/1.06      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.73/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1838,c_1151]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_637,plain,
% 1.73/1.06      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 1.73/1.06      theory(equality) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2071,plain,
% 1.73/1.06      ( X0_51 != X1_51
% 1.73/1.06      | X0_51 = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 1.73/1.06      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X1_51 ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_637]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2618,plain,
% 1.73/1.06      ( X0_51 = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 1.73/1.06      | X0_51 != k2_funct_1(sK2)
% 1.73/1.06      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2071]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2951,plain,
% 1.73/1.06      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_funct_1(sK2)
% 1.73/1.06      | k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 1.73/1.06      | k2_funct_1(sK2) != k2_funct_1(sK2) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2618]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1150,plain,
% 1.73/1.06      ( k2_relset_1(X0_52,X1_52,X0_51) != X1_52
% 1.73/1.06      | v1_funct_2(X0_51,X0_52,X1_52) != iProver_top
% 1.73/1.06      | m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52))) != iProver_top
% 1.73/1.06      | m1_subset_1(k2_funct_1(X0_51),k1_zfmisc_1(k2_zfmisc_1(X1_52,X0_52))) = iProver_top
% 1.73/1.06      | v1_funct_1(X0_51) != iProver_top
% 1.73/1.06      | v2_funct_1(X0_51) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_623]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3006,plain,
% 1.73/1.06      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.73/1.06      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 1.73/1.06      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.73/1.06      | v1_funct_1(sK2) != iProver_top
% 1.73/1.06      | v2_funct_1(sK2) != iProver_top ),
% 1.73/1.06      inference(superposition,[status(thm)],[c_1838,c_1150]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_646,plain,
% 1.73/1.06      ( ~ v2_funct_1(X0_51) | v2_funct_1(X1_51) | X1_51 != X0_51 ),
% 1.73/1.06      theory(equality) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2065,plain,
% 1.73/1.06      ( ~ v2_funct_1(X0_51)
% 1.73/1.06      | v2_funct_1(k2_funct_1(X1_51))
% 1.73/1.06      | k2_funct_1(X1_51) != X0_51 ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_646]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3829,plain,
% 1.73/1.06      ( ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.73/1.06      | v2_funct_1(k2_funct_1(sK2))
% 1.73/1.06      | k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_2065]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_3830,plain,
% 1.73/1.06      ( k2_funct_1(sK2) != k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
% 1.73/1.06      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != iProver_top
% 1.73/1.06      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_3829]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_5451,plain,
% 1.73/1.06      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 1.73/1.06      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_4540,c_30,c_27,c_32,c_26,c_33,c_25,c_34,c_24,c_35,c_22,
% 1.73/1.06                 c_36,c_705,c_613,c_1519,c_1527,c_1531,c_1756,c_1839,c_1867,
% 1.73/1.06                 c_2215,c_2835,c_2951,c_3006,c_3830]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_5885,plain,
% 1.73/1.06      ( k2_struct_0(sK0) != k1_relat_1(sK2)
% 1.73/1.06      | k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 1.73/1.06      inference(demodulation,[status(thm)],[c_5882,c_5451]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_8,plain,
% 1.73/1.06      ( r2_funct_2(X0,X1,X2,X2)
% 1.73/1.06      | ~ v1_funct_2(X2,X0,X1)
% 1.73/1.06      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.73/1.06      | ~ v1_funct_1(X2) ),
% 1.73/1.06      inference(cnf_transformation,[],[f74]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_21,negated_conjecture,
% 1.73/1.06      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 1.73/1.06      inference(cnf_transformation,[],[f73]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_328,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.06      | ~ v1_funct_1(X0)
% 1.73/1.06      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 1.73/1.06      | u1_struct_0(sK1) != X2
% 1.73/1.06      | u1_struct_0(sK0) != X1
% 1.73/1.06      | sK2 != X0 ),
% 1.73/1.06      inference(resolution_lifted,[status(thm)],[c_8,c_21]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_329,plain,
% 1.73/1.06      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.73/1.06      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 1.73/1.06      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 1.73/1.06      inference(unflattening,[status(thm)],[c_328]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_607,plain,
% 1.73/1.06      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.73/1.06      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 1.73/1.06      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_329]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1165,plain,
% 1.73/1.06      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.73/1.06      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.73/1.06      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.73/1.06      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 1.73/1.06      inference(predicate_to_equality,[status(thm)],[c_607]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_17,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.06      | ~ v1_funct_1(X0)
% 1.73/1.06      | v1_funct_1(k2_tops_2(X1,X2,X0)) ),
% 1.73/1.06      inference(cnf_transformation,[],[f59]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_616,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 1.73/1.06      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.73/1.06      | ~ v1_funct_1(X0_51)
% 1.73/1.06      | v1_funct_1(k2_tops_2(X0_52,X1_52,X0_51)) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_17]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1487,plain,
% 1.73/1.06      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.73/1.06      | v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 1.73/1.06      | ~ v1_funct_1(sK2) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_616]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_16,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0,X1,X2)
% 1.73/1.06      | v1_funct_2(k2_tops_2(X1,X2,X0),X2,X1)
% 1.73/1.06      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.73/1.06      | ~ v1_funct_1(X0) ),
% 1.73/1.06      inference(cnf_transformation,[],[f60]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_617,plain,
% 1.73/1.06      ( ~ v1_funct_2(X0_51,X0_52,X1_52)
% 1.73/1.06      | v1_funct_2(k2_tops_2(X0_52,X1_52,X0_51),X1_52,X0_52)
% 1.73/1.06      | ~ m1_subset_1(X0_51,k1_zfmisc_1(k2_zfmisc_1(X0_52,X1_52)))
% 1.73/1.06      | ~ v1_funct_1(X0_51) ),
% 1.73/1.06      inference(subtyping,[status(esa)],[c_16]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1490,plain,
% 1.73/1.06      ( v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.73/1.06      | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.73/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.73/1.06      | ~ v1_funct_1(sK2) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_617]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1493,plain,
% 1.73/1.06      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.73/1.06      | m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.73/1.06      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.73/1.06      | ~ v1_funct_1(sK2) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_618]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1560,plain,
% 1.73/1.06      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.73/1.06      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.73/1.06      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 1.73/1.06      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_616]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1559,plain,
% 1.73/1.06      ( v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 1.73/1.06      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.73/1.06      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.73/1.06      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_617]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_1558,plain,
% 1.73/1.06      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
% 1.73/1.06      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.73/1.06      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 1.73/1.06      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 1.73/1.06      inference(instantiation,[status(thm)],[c_618]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2342,plain,
% 1.73/1.06      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 1.73/1.06      inference(global_propositional_subsumption,
% 1.73/1.06                [status(thm)],
% 1.73/1.06                [c_1165,c_26,c_25,c_24,c_607,c_1487,c_1490,c_1493,c_1560,
% 1.73/1.06                 c_1559,c_1558]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2344,plain,
% 1.73/1.06      ( k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)) != sK2 ),
% 1.73/1.06      inference(light_normalisation,[status(thm)],[c_2342,c_1598]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_2538,plain,
% 1.73/1.06      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != sK2 ),
% 1.73/1.06      inference(demodulation,[status(thm)],[c_1840,c_2344]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_4409,plain,
% 1.73/1.06      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2 ),
% 1.73/1.06      inference(demodulation,[status(thm)],[c_4402,c_2538]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_5984,plain,
% 1.73/1.06      ( k2_struct_0(sK0) != k1_relat_1(sK2) ),
% 1.73/1.06      inference(global_propositional_subsumption,[status(thm)],[c_5885,c_4409]) ).
% 1.73/1.06  
% 1.73/1.06  cnf(c_5992,plain,
% 1.73/1.06      ( $false ),
% 1.73/1.06      inference(forward_subsumption_resolution,[status(thm)],[c_5990,c_5984]) ).
% 1.73/1.06  
% 1.73/1.06  
% 1.73/1.06  % SZS output end CNFRefutation for theBenchmark.p
% 1.73/1.06  
% 1.73/1.06  ------                               Statistics
% 1.73/1.06  
% 1.73/1.06  ------ General
% 1.73/1.06  
% 1.73/1.06  abstr_ref_over_cycles:                  0
% 1.73/1.06  abstr_ref_under_cycles:                 0
% 1.73/1.06  gc_basic_clause_elim:                   0
% 1.73/1.06  forced_gc_time:                         0
% 1.73/1.06  parsing_time:                           0.008
% 1.73/1.06  unif_index_cands_time:                  0.
% 1.73/1.06  unif_index_add_time:                    0.
% 1.73/1.06  orderings_time:                         0.
% 1.73/1.06  out_proof_time:                         0.024
% 1.73/1.06  total_time:                             0.315
% 1.73/1.06  num_of_symbols:                         56
% 1.73/1.06  num_of_terms:                           5180
% 1.73/1.06  
% 1.73/1.06  ------ Preprocessing
% 1.73/1.06  
% 1.73/1.06  num_of_splits:                          0
% 1.73/1.06  num_of_split_atoms:                     0
% 1.73/1.06  num_of_reused_defs:                     0
% 1.73/1.06  num_eq_ax_congr_red:                    6
% 1.73/1.06  num_of_sem_filtered_clauses:            1
% 1.73/1.06  num_of_subtypes:                        5
% 1.73/1.06  monotx_restored_types:                  0
% 1.73/1.06  sat_num_of_epr_types:                   0
% 1.73/1.06  sat_num_of_non_cyclic_types:            0
% 1.73/1.06  sat_guarded_non_collapsed_types:        1
% 1.73/1.06  num_pure_diseq_elim:                    0
% 1.73/1.06  simp_replaced_by:                       0
% 1.73/1.06  res_preprocessed:                       154
% 1.73/1.06  prep_upred:                             0
% 1.73/1.06  prep_unflattend:                        9
% 1.73/1.06  smt_new_axioms:                         0
% 1.73/1.06  pred_elim_cands:                        6
% 1.73/1.06  pred_elim:                              2
% 1.73/1.06  pred_elim_cl:                           3
% 1.73/1.06  pred_elim_cycles:                       4
% 1.73/1.06  merged_defs:                            0
% 1.73/1.06  merged_defs_ncl:                        0
% 1.73/1.06  bin_hyper_res:                          0
% 1.73/1.06  prep_cycles:                            4
% 1.73/1.06  pred_elim_time:                         0.005
% 1.73/1.06  splitting_time:                         0.
% 1.73/1.06  sem_filter_time:                        0.
% 1.73/1.06  monotx_time:                            0.
% 1.73/1.06  subtype_inf_time:                       0.
% 1.73/1.06  
% 1.73/1.06  ------ Problem properties
% 1.73/1.06  
% 1.73/1.06  clauses:                                27
% 1.73/1.06  conjectures:                            7
% 1.73/1.06  epr:                                    4
% 1.73/1.06  horn:                                   27
% 1.73/1.06  ground:                                 8
% 1.73/1.06  unary:                                  8
% 1.73/1.06  binary:                                 2
% 1.73/1.06  lits:                                   101
% 1.73/1.06  lits_eq:                                21
% 1.73/1.06  fd_pure:                                0
% 1.73/1.06  fd_pseudo:                              0
% 1.73/1.06  fd_cond:                                0
% 1.73/1.06  fd_pseudo_cond:                         1
% 1.73/1.06  ac_symbols:                             0
% 1.73/1.06  
% 1.73/1.06  ------ Propositional Solver
% 1.73/1.06  
% 1.73/1.06  prop_solver_calls:                      29
% 1.73/1.06  prop_fast_solver_calls:                 1628
% 1.73/1.06  smt_solver_calls:                       0
% 1.73/1.06  smt_fast_solver_calls:                  0
% 1.73/1.06  prop_num_of_clauses:                    2180
% 1.73/1.06  prop_preprocess_simplified:             6811
% 1.73/1.06  prop_fo_subsumed:                       105
% 1.73/1.06  prop_solver_time:                       0.
% 1.73/1.06  smt_solver_time:                        0.
% 1.73/1.06  smt_fast_solver_time:                   0.
% 1.73/1.06  prop_fast_solver_time:                  0.
% 1.73/1.06  prop_unsat_core_time:                   0.
% 1.73/1.06  
% 1.73/1.06  ------ QBF
% 1.73/1.06  
% 1.73/1.06  qbf_q_res:                              0
% 1.73/1.06  qbf_num_tautologies:                    0
% 1.73/1.06  qbf_prep_cycles:                        0
% 1.73/1.06  
% 1.73/1.06  ------ BMC1
% 1.73/1.06  
% 1.73/1.06  bmc1_current_bound:                     -1
% 1.73/1.06  bmc1_last_solved_bound:                 -1
% 1.73/1.06  bmc1_unsat_core_size:                   -1
% 1.73/1.06  bmc1_unsat_core_parents_size:           -1
% 1.73/1.06  bmc1_merge_next_fun:                    0
% 1.73/1.06  bmc1_unsat_core_clauses_time:           0.
% 1.73/1.06  
% 1.73/1.06  ------ Instantiation
% 1.73/1.06  
% 1.73/1.06  inst_num_of_clauses:                    809
% 1.73/1.06  inst_num_in_passive:                    348
% 1.73/1.06  inst_num_in_active:                     428
% 1.73/1.06  inst_num_in_unprocessed:                33
% 1.73/1.06  inst_num_of_loops:                      460
% 1.73/1.06  inst_num_of_learning_restarts:          0
% 1.73/1.06  inst_num_moves_active_passive:          27
% 1.73/1.06  inst_lit_activity:                      0
% 1.73/1.06  inst_lit_activity_moves:                0
% 1.73/1.06  inst_num_tautologies:                   0
% 1.73/1.06  inst_num_prop_implied:                  0
% 1.73/1.06  inst_num_existing_simplified:           0
% 1.73/1.06  inst_num_eq_res_simplified:             0
% 1.73/1.06  inst_num_child_elim:                    0
% 1.73/1.06  inst_num_of_dismatching_blockings:      175
% 1.73/1.06  inst_num_of_non_proper_insts:           759
% 1.73/1.06  inst_num_of_duplicates:                 0
% 1.73/1.06  inst_inst_num_from_inst_to_res:         0
% 1.73/1.06  inst_dismatching_checking_time:         0.
% 1.73/1.06  
% 1.73/1.06  ------ Resolution
% 1.73/1.06  
% 1.73/1.06  res_num_of_clauses:                     0
% 1.73/1.06  res_num_in_passive:                     0
% 1.73/1.06  res_num_in_active:                      0
% 1.73/1.06  res_num_of_loops:                       158
% 1.73/1.06  res_forward_subset_subsumed:            58
% 1.73/1.06  res_backward_subset_subsumed:           0
% 1.73/1.06  res_forward_subsumed:                   0
% 1.73/1.06  res_backward_subsumed:                  0
% 1.73/1.06  res_forward_subsumption_resolution:     0
% 1.73/1.06  res_backward_subsumption_resolution:    0
% 1.73/1.06  res_clause_to_clause_subsumption:       186
% 1.73/1.06  res_orphan_elimination:                 0
% 1.73/1.06  res_tautology_del:                      84
% 1.73/1.06  res_num_eq_res_simplified:              0
% 1.73/1.06  res_num_sel_changes:                    0
% 1.73/1.06  res_moves_from_active_to_pass:          0
% 1.73/1.06  
% 1.73/1.06  ------ Superposition
% 1.73/1.06  
% 1.73/1.06  sup_time_total:                         0.
% 1.73/1.06  sup_time_generating:                    0.
% 1.73/1.06  sup_time_sim_full:                      0.
% 1.73/1.06  sup_time_sim_immed:                     0.
% 1.73/1.06  
% 1.73/1.06  sup_num_of_clauses:                     79
% 1.73/1.06  sup_num_in_active:                      63
% 1.73/1.06  sup_num_in_passive:                     16
% 1.73/1.06  sup_num_of_loops:                       91
% 1.73/1.06  sup_fw_superposition:                   36
% 1.73/1.06  sup_bw_superposition:                   46
% 1.73/1.06  sup_immediate_simplified:               31
% 1.73/1.06  sup_given_eliminated:                   0
% 1.73/1.06  comparisons_done:                       0
% 1.73/1.06  comparisons_avoided:                    0
% 1.73/1.06  
% 1.73/1.06  ------ Simplifications
% 1.73/1.06  
% 1.73/1.06  
% 1.73/1.06  sim_fw_subset_subsumed:                 5
% 1.73/1.06  sim_bw_subset_subsumed:                 5
% 1.73/1.06  sim_fw_subsumed:                        3
% 1.73/1.06  sim_bw_subsumed:                        0
% 1.73/1.06  sim_fw_subsumption_res:                 2
% 1.73/1.06  sim_bw_subsumption_res:                 0
% 1.73/1.06  sim_tautology_del:                      0
% 1.73/1.06  sim_eq_tautology_del:                   7
% 1.73/1.06  sim_eq_res_simp:                        2
% 1.73/1.06  sim_fw_demodulated:                     0
% 1.73/1.06  sim_bw_demodulated:                     26
% 1.73/1.06  sim_light_normalised:                   40
% 1.73/1.06  sim_joinable_taut:                      0
% 1.73/1.06  sim_joinable_simp:                      0
% 1.73/1.06  sim_ac_normalised:                      0
% 1.73/1.06  sim_smt_subsumption:                    0
% 1.73/1.06  
%------------------------------------------------------------------------------
