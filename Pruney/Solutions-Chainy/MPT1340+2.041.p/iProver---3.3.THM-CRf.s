%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:29 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.46s
% Verified   : 
% Statistics : Number of formulae       :  138 (2161 expanded)
%              Number of clauses        :   87 ( 652 expanded)
%              Number of leaves         :   12 ( 628 expanded)
%              Depth                    :   23
%              Number of atoms          :  598 (14642 expanded)
%              Number of equality atoms :  220 (2605 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f30,plain,(
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

fof(f29,plain,(
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

fof(f28,plain,
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

fof(f31,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30,f29,f28])).

fof(f52,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f46,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f48,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f53,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f50,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f31])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f31])).

fof(f8,axiom,(
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

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f45,plain,(
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
    inference(cnf_transformation,[],[f24])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f14,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f13])).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f12,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f11])).

fof(f34,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f33,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f5,axiom,(
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

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f18])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f4,axiom,(
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

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

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
    inference(flattening,[],[f16])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f38])).

fof(f54,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_16,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_627,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_10,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_22,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_360,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_22])).

cnf(c_361,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_360])).

cnf(c_620,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_361])).

cnf(c_20,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_355,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_356,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_355])).

cnf(c_621,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_356])).

cnf(c_1045,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_627,c_620,c_621])).

cnf(c_11,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f43])).

cnf(c_629,plain,
    ( ~ v1_funct_2(X0_47,X0_48,X1_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ v1_funct_1(X0_47)
    | ~ v2_funct_1(X0_47)
    | k2_relset_1(X0_48,X1_48,X0_47) != X1_48
    | k2_tops_2(X0_48,X1_48,X0_47) = k2_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1023,plain,
    ( k2_relset_1(X0_48,X1_48,X0_47) != X1_48
    | k2_tops_2(X0_48,X1_48,X0_47) = k2_funct_1(X0_47)
    | v1_funct_2(X0_47,X0_48,X1_48) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_629])).

cnf(c_1918,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1023])).

cnf(c_19,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_26,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_15,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_29,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_625,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_1026,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_625])).

cnf(c_1042,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1026,c_620,c_621])).

cnf(c_17,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_626,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1025,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_626])).

cnf(c_1048,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1025,c_620,c_621])).

cnf(c_2132,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1918,c_26,c_29,c_1042,c_1048])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_21,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_308,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_21])).

cnf(c_309,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_308])).

cnf(c_313,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_309,c_20])).

cnf(c_314,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_313])).

cnf(c_413,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_314,c_22])).

cnf(c_414,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_413])).

cnf(c_617,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_47)
    | ~ v2_funct_1(X0_47)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_47) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_414])).

cnf(c_1032,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_2(X0_47,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_617])).

cnf(c_1157,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1032,c_620,c_621])).

cnf(c_1510,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1157])).

cnf(c_1210,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1157])).

cnf(c_1513,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1510,c_26,c_29,c_1042,c_1045,c_1048,c_1210])).

cnf(c_2137,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2132,c_1513])).

cnf(c_2357,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2137,c_1023])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_632,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1020,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_relat_1(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_632])).

cnf(c_1329,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_1020])).

cnf(c_3,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_633,plain,
    ( ~ v1_relat_1(X0_47)
    | ~ v1_funct_1(X0_47)
    | ~ v2_funct_1(X0_47)
    | k2_funct_1(k2_funct_1(X0_47)) = X0_47 ),
    inference(subtyping,[status(esa)],[c_3])).

cnf(c_1019,plain,
    ( k2_funct_1(k2_funct_1(X0_47)) = X0_47
    | v1_relat_1(X0_47) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_633])).

cnf(c_1664,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1329,c_1019])).

cnf(c_681,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_633])).

cnf(c_1245,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_632])).

cnf(c_1738,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1664,c_19,c_17,c_15,c_681,c_1245])).

cnf(c_2377,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2357,c_1738])).

cnf(c_28,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_0,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_636,plain,
    ( ~ v1_relat_1(X0_47)
    | ~ v1_funct_1(X0_47)
    | ~ v2_funct_1(X0_47)
    | v2_funct_1(k2_funct_1(X0_47)) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_671,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top
    | v2_funct_1(k2_funct_1(X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_636])).

cnf(c_673,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_671])).

cnf(c_1,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_635,plain,
    ( ~ v1_relat_1(X0_47)
    | ~ v1_funct_1(X0_47)
    | v1_funct_1(k2_funct_1(X0_47))
    | ~ v2_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_674,plain,
    ( v1_relat_1(X0_47) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(k2_funct_1(X0_47)) = iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_635])).

cnf(c_676,plain,
    ( v1_relat_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_674])).

cnf(c_1246,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1245])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f41])).

cnf(c_631,plain,
    ( ~ v1_funct_2(X0_47,X0_48,X1_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | m1_subset_1(k2_funct_1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48)))
    | ~ v1_funct_1(X0_47)
    | ~ v2_funct_1(X0_47)
    | k2_relset_1(X0_48,X1_48,X0_47) != X1_48 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1021,plain,
    ( k2_relset_1(X0_48,X1_48,X0_47) != X1_48
    | v1_funct_2(X0_47,X0_48,X1_48) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48))) = iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_631])).

cnf(c_1751,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1021])).

cnf(c_8,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_630,plain,
    ( ~ v1_funct_2(X0_47,X0_48,X1_48)
    | v1_funct_2(k2_funct_1(X0_47),X1_48,X0_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ v1_funct_1(X0_47)
    | ~ v2_funct_1(X0_47)
    | k2_relset_1(X0_48,X1_48,X0_47) != X1_48 ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_1022,plain,
    ( k2_relset_1(X0_48,X1_48,X0_47) != X1_48
    | v1_funct_2(X0_47,X0_48,X1_48) != iProver_top
    | v1_funct_2(k2_funct_1(X0_47),X1_48,X0_48) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_630])).

cnf(c_1887,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1045,c_1022])).

cnf(c_2888,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2377,c_26,c_28,c_29,c_673,c_676,c_1042,c_1048,c_1246,c_1751,c_1887])).

cnf(c_5,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_14,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_256,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_5,c_14])).

cnf(c_257,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_256])).

cnf(c_622,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_257])).

cnf(c_1029,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_622])).

cnf(c_1183,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1029,c_620,c_621])).

cnf(c_2135,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2132,c_1183])).

cnf(c_2468,plain,
    ( v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2135,c_26,c_28,c_29,c_673,c_676,c_1042,c_1048,c_1246,c_1751,c_1887,c_2377])).

cnf(c_2891,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2888,c_2468])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_2891,c_1048,c_1042,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 13:07:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.46/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.46/1.03  
% 2.46/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.46/1.03  
% 2.46/1.03  ------  iProver source info
% 2.46/1.03  
% 2.46/1.03  git: date: 2020-06-30 10:37:57 +0100
% 2.46/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.46/1.03  git: non_committed_changes: false
% 2.46/1.03  git: last_make_outside_of_git: false
% 2.46/1.03  
% 2.46/1.03  ------ 
% 2.46/1.03  
% 2.46/1.03  ------ Input Options
% 2.46/1.03  
% 2.46/1.03  --out_options                           all
% 2.46/1.03  --tptp_safe_out                         true
% 2.46/1.03  --problem_path                          ""
% 2.46/1.03  --include_path                          ""
% 2.46/1.03  --clausifier                            res/vclausify_rel
% 2.46/1.03  --clausifier_options                    --mode clausify
% 2.46/1.03  --stdin                                 false
% 2.46/1.03  --stats_out                             all
% 2.46/1.03  
% 2.46/1.03  ------ General Options
% 2.46/1.03  
% 2.46/1.03  --fof                                   false
% 2.46/1.03  --time_out_real                         305.
% 2.46/1.03  --time_out_virtual                      -1.
% 2.46/1.03  --symbol_type_check                     false
% 2.46/1.03  --clausify_out                          false
% 2.46/1.03  --sig_cnt_out                           false
% 2.46/1.03  --trig_cnt_out                          false
% 2.46/1.03  --trig_cnt_out_tolerance                1.
% 2.46/1.03  --trig_cnt_out_sk_spl                   false
% 2.46/1.03  --abstr_cl_out                          false
% 2.46/1.03  
% 2.46/1.03  ------ Global Options
% 2.46/1.03  
% 2.46/1.03  --schedule                              default
% 2.46/1.03  --add_important_lit                     false
% 2.46/1.03  --prop_solver_per_cl                    1000
% 2.46/1.03  --min_unsat_core                        false
% 2.46/1.03  --soft_assumptions                      false
% 2.46/1.03  --soft_lemma_size                       3
% 2.46/1.03  --prop_impl_unit_size                   0
% 2.46/1.03  --prop_impl_unit                        []
% 2.46/1.03  --share_sel_clauses                     true
% 2.46/1.03  --reset_solvers                         false
% 2.46/1.03  --bc_imp_inh                            [conj_cone]
% 2.46/1.03  --conj_cone_tolerance                   3.
% 2.46/1.03  --extra_neg_conj                        none
% 2.46/1.03  --large_theory_mode                     true
% 2.46/1.03  --prolific_symb_bound                   200
% 2.46/1.03  --lt_threshold                          2000
% 2.46/1.03  --clause_weak_htbl                      true
% 2.46/1.03  --gc_record_bc_elim                     false
% 2.46/1.03  
% 2.46/1.03  ------ Preprocessing Options
% 2.46/1.03  
% 2.46/1.03  --preprocessing_flag                    true
% 2.46/1.03  --time_out_prep_mult                    0.1
% 2.46/1.03  --splitting_mode                        input
% 2.46/1.03  --splitting_grd                         true
% 2.46/1.03  --splitting_cvd                         false
% 2.46/1.03  --splitting_cvd_svl                     false
% 2.46/1.03  --splitting_nvd                         32
% 2.46/1.03  --sub_typing                            true
% 2.46/1.03  --prep_gs_sim                           true
% 2.46/1.03  --prep_unflatten                        true
% 2.46/1.03  --prep_res_sim                          true
% 2.46/1.03  --prep_upred                            true
% 2.46/1.03  --prep_sem_filter                       exhaustive
% 2.46/1.03  --prep_sem_filter_out                   false
% 2.46/1.03  --pred_elim                             true
% 2.46/1.03  --res_sim_input                         true
% 2.46/1.03  --eq_ax_congr_red                       true
% 2.46/1.03  --pure_diseq_elim                       true
% 2.46/1.03  --brand_transform                       false
% 2.46/1.03  --non_eq_to_eq                          false
% 2.46/1.03  --prep_def_merge                        true
% 2.46/1.03  --prep_def_merge_prop_impl              false
% 2.46/1.03  --prep_def_merge_mbd                    true
% 2.46/1.03  --prep_def_merge_tr_red                 false
% 2.46/1.03  --prep_def_merge_tr_cl                  false
% 2.46/1.03  --smt_preprocessing                     true
% 2.46/1.03  --smt_ac_axioms                         fast
% 2.46/1.03  --preprocessed_out                      false
% 2.46/1.03  --preprocessed_stats                    false
% 2.46/1.03  
% 2.46/1.03  ------ Abstraction refinement Options
% 2.46/1.03  
% 2.46/1.03  --abstr_ref                             []
% 2.46/1.03  --abstr_ref_prep                        false
% 2.46/1.03  --abstr_ref_until_sat                   false
% 2.46/1.03  --abstr_ref_sig_restrict                funpre
% 2.46/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/1.03  --abstr_ref_under                       []
% 2.46/1.03  
% 2.46/1.03  ------ SAT Options
% 2.46/1.03  
% 2.46/1.03  --sat_mode                              false
% 2.46/1.03  --sat_fm_restart_options                ""
% 2.46/1.03  --sat_gr_def                            false
% 2.46/1.03  --sat_epr_types                         true
% 2.46/1.03  --sat_non_cyclic_types                  false
% 2.46/1.03  --sat_finite_models                     false
% 2.46/1.03  --sat_fm_lemmas                         false
% 2.46/1.03  --sat_fm_prep                           false
% 2.46/1.03  --sat_fm_uc_incr                        true
% 2.46/1.03  --sat_out_model                         small
% 2.46/1.03  --sat_out_clauses                       false
% 2.46/1.03  
% 2.46/1.03  ------ QBF Options
% 2.46/1.03  
% 2.46/1.03  --qbf_mode                              false
% 2.46/1.03  --qbf_elim_univ                         false
% 2.46/1.03  --qbf_dom_inst                          none
% 2.46/1.03  --qbf_dom_pre_inst                      false
% 2.46/1.03  --qbf_sk_in                             false
% 2.46/1.03  --qbf_pred_elim                         true
% 2.46/1.03  --qbf_split                             512
% 2.46/1.03  
% 2.46/1.03  ------ BMC1 Options
% 2.46/1.03  
% 2.46/1.03  --bmc1_incremental                      false
% 2.46/1.03  --bmc1_axioms                           reachable_all
% 2.46/1.03  --bmc1_min_bound                        0
% 2.46/1.03  --bmc1_max_bound                        -1
% 2.46/1.03  --bmc1_max_bound_default                -1
% 2.46/1.03  --bmc1_symbol_reachability              true
% 2.46/1.03  --bmc1_property_lemmas                  false
% 2.46/1.03  --bmc1_k_induction                      false
% 2.46/1.03  --bmc1_non_equiv_states                 false
% 2.46/1.03  --bmc1_deadlock                         false
% 2.46/1.03  --bmc1_ucm                              false
% 2.46/1.03  --bmc1_add_unsat_core                   none
% 2.46/1.03  --bmc1_unsat_core_children              false
% 2.46/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/1.03  --bmc1_out_stat                         full
% 2.46/1.03  --bmc1_ground_init                      false
% 2.46/1.03  --bmc1_pre_inst_next_state              false
% 2.46/1.03  --bmc1_pre_inst_state                   false
% 2.46/1.03  --bmc1_pre_inst_reach_state             false
% 2.46/1.03  --bmc1_out_unsat_core                   false
% 2.46/1.03  --bmc1_aig_witness_out                  false
% 2.46/1.03  --bmc1_verbose                          false
% 2.46/1.03  --bmc1_dump_clauses_tptp                false
% 2.46/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.46/1.03  --bmc1_dump_file                        -
% 2.46/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.46/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.46/1.03  --bmc1_ucm_extend_mode                  1
% 2.46/1.03  --bmc1_ucm_init_mode                    2
% 2.46/1.03  --bmc1_ucm_cone_mode                    none
% 2.46/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.46/1.03  --bmc1_ucm_relax_model                  4
% 2.46/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.46/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/1.03  --bmc1_ucm_layered_model                none
% 2.46/1.03  --bmc1_ucm_max_lemma_size               10
% 2.46/1.03  
% 2.46/1.03  ------ AIG Options
% 2.46/1.03  
% 2.46/1.03  --aig_mode                              false
% 2.46/1.03  
% 2.46/1.03  ------ Instantiation Options
% 2.46/1.03  
% 2.46/1.03  --instantiation_flag                    true
% 2.46/1.03  --inst_sos_flag                         false
% 2.46/1.03  --inst_sos_phase                        true
% 2.46/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/1.03  --inst_lit_sel_side                     num_symb
% 2.46/1.03  --inst_solver_per_active                1400
% 2.46/1.03  --inst_solver_calls_frac                1.
% 2.46/1.03  --inst_passive_queue_type               priority_queues
% 2.46/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/1.03  --inst_passive_queues_freq              [25;2]
% 2.46/1.03  --inst_dismatching                      true
% 2.46/1.03  --inst_eager_unprocessed_to_passive     true
% 2.46/1.03  --inst_prop_sim_given                   true
% 2.46/1.03  --inst_prop_sim_new                     false
% 2.46/1.03  --inst_subs_new                         false
% 2.46/1.03  --inst_eq_res_simp                      false
% 2.46/1.03  --inst_subs_given                       false
% 2.46/1.03  --inst_orphan_elimination               true
% 2.46/1.03  --inst_learning_loop_flag               true
% 2.46/1.03  --inst_learning_start                   3000
% 2.46/1.03  --inst_learning_factor                  2
% 2.46/1.03  --inst_start_prop_sim_after_learn       3
% 2.46/1.03  --inst_sel_renew                        solver
% 2.46/1.03  --inst_lit_activity_flag                true
% 2.46/1.03  --inst_restr_to_given                   false
% 2.46/1.03  --inst_activity_threshold               500
% 2.46/1.03  --inst_out_proof                        true
% 2.46/1.03  
% 2.46/1.03  ------ Resolution Options
% 2.46/1.03  
% 2.46/1.03  --resolution_flag                       true
% 2.46/1.03  --res_lit_sel                           adaptive
% 2.46/1.03  --res_lit_sel_side                      none
% 2.46/1.03  --res_ordering                          kbo
% 2.46/1.03  --res_to_prop_solver                    active
% 2.46/1.03  --res_prop_simpl_new                    false
% 2.46/1.03  --res_prop_simpl_given                  true
% 2.46/1.03  --res_passive_queue_type                priority_queues
% 2.46/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/1.03  --res_passive_queues_freq               [15;5]
% 2.46/1.03  --res_forward_subs                      full
% 2.46/1.03  --res_backward_subs                     full
% 2.46/1.03  --res_forward_subs_resolution           true
% 2.46/1.03  --res_backward_subs_resolution          true
% 2.46/1.03  --res_orphan_elimination                true
% 2.46/1.03  --res_time_limit                        2.
% 2.46/1.03  --res_out_proof                         true
% 2.46/1.03  
% 2.46/1.03  ------ Superposition Options
% 2.46/1.03  
% 2.46/1.03  --superposition_flag                    true
% 2.46/1.03  --sup_passive_queue_type                priority_queues
% 2.46/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.46/1.03  --demod_completeness_check              fast
% 2.46/1.03  --demod_use_ground                      true
% 2.46/1.03  --sup_to_prop_solver                    passive
% 2.46/1.03  --sup_prop_simpl_new                    true
% 2.46/1.03  --sup_prop_simpl_given                  true
% 2.46/1.03  --sup_fun_splitting                     false
% 2.46/1.03  --sup_smt_interval                      50000
% 2.46/1.03  
% 2.46/1.03  ------ Superposition Simplification Setup
% 2.46/1.03  
% 2.46/1.03  --sup_indices_passive                   []
% 2.46/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.03  --sup_full_bw                           [BwDemod]
% 2.46/1.03  --sup_immed_triv                        [TrivRules]
% 2.46/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.03  --sup_immed_bw_main                     []
% 2.46/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.03  
% 2.46/1.03  ------ Combination Options
% 2.46/1.03  
% 2.46/1.03  --comb_res_mult                         3
% 2.46/1.03  --comb_sup_mult                         2
% 2.46/1.03  --comb_inst_mult                        10
% 2.46/1.03  
% 2.46/1.03  ------ Debug Options
% 2.46/1.03  
% 2.46/1.03  --dbg_backtrace                         false
% 2.46/1.03  --dbg_dump_prop_clauses                 false
% 2.46/1.03  --dbg_dump_prop_clauses_file            -
% 2.46/1.03  --dbg_out_stat                          false
% 2.46/1.03  ------ Parsing...
% 2.46/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.46/1.03  
% 2.46/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.46/1.03  
% 2.46/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.46/1.03  
% 2.46/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.46/1.03  ------ Proving...
% 2.46/1.03  ------ Problem Properties 
% 2.46/1.03  
% 2.46/1.03  
% 2.46/1.03  clauses                                 21
% 2.46/1.03  conjectures                             5
% 2.46/1.03  EPR                                     2
% 2.46/1.03  Horn                                    21
% 2.46/1.03  unary                                   7
% 2.46/1.03  binary                                  1
% 2.46/1.03  lits                                    75
% 2.46/1.03  lits eq                                 17
% 2.46/1.03  fd_pure                                 0
% 2.46/1.03  fd_pseudo                               0
% 2.46/1.03  fd_cond                                 0
% 2.46/1.03  fd_pseudo_cond                          0
% 2.46/1.03  AC symbols                              0
% 2.46/1.03  
% 2.46/1.03  ------ Schedule dynamic 5 is on 
% 2.46/1.03  
% 2.46/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.46/1.03  
% 2.46/1.03  
% 2.46/1.03  ------ 
% 2.46/1.03  Current options:
% 2.46/1.03  ------ 
% 2.46/1.03  
% 2.46/1.03  ------ Input Options
% 2.46/1.03  
% 2.46/1.03  --out_options                           all
% 2.46/1.03  --tptp_safe_out                         true
% 2.46/1.03  --problem_path                          ""
% 2.46/1.03  --include_path                          ""
% 2.46/1.03  --clausifier                            res/vclausify_rel
% 2.46/1.03  --clausifier_options                    --mode clausify
% 2.46/1.03  --stdin                                 false
% 2.46/1.03  --stats_out                             all
% 2.46/1.03  
% 2.46/1.03  ------ General Options
% 2.46/1.03  
% 2.46/1.03  --fof                                   false
% 2.46/1.03  --time_out_real                         305.
% 2.46/1.03  --time_out_virtual                      -1.
% 2.46/1.03  --symbol_type_check                     false
% 2.46/1.03  --clausify_out                          false
% 2.46/1.03  --sig_cnt_out                           false
% 2.46/1.03  --trig_cnt_out                          false
% 2.46/1.03  --trig_cnt_out_tolerance                1.
% 2.46/1.03  --trig_cnt_out_sk_spl                   false
% 2.46/1.03  --abstr_cl_out                          false
% 2.46/1.03  
% 2.46/1.03  ------ Global Options
% 2.46/1.03  
% 2.46/1.03  --schedule                              default
% 2.46/1.03  --add_important_lit                     false
% 2.46/1.03  --prop_solver_per_cl                    1000
% 2.46/1.03  --min_unsat_core                        false
% 2.46/1.03  --soft_assumptions                      false
% 2.46/1.03  --soft_lemma_size                       3
% 2.46/1.03  --prop_impl_unit_size                   0
% 2.46/1.03  --prop_impl_unit                        []
% 2.46/1.03  --share_sel_clauses                     true
% 2.46/1.03  --reset_solvers                         false
% 2.46/1.03  --bc_imp_inh                            [conj_cone]
% 2.46/1.03  --conj_cone_tolerance                   3.
% 2.46/1.03  --extra_neg_conj                        none
% 2.46/1.03  --large_theory_mode                     true
% 2.46/1.03  --prolific_symb_bound                   200
% 2.46/1.03  --lt_threshold                          2000
% 2.46/1.03  --clause_weak_htbl                      true
% 2.46/1.03  --gc_record_bc_elim                     false
% 2.46/1.03  
% 2.46/1.03  ------ Preprocessing Options
% 2.46/1.03  
% 2.46/1.03  --preprocessing_flag                    true
% 2.46/1.03  --time_out_prep_mult                    0.1
% 2.46/1.03  --splitting_mode                        input
% 2.46/1.03  --splitting_grd                         true
% 2.46/1.03  --splitting_cvd                         false
% 2.46/1.03  --splitting_cvd_svl                     false
% 2.46/1.03  --splitting_nvd                         32
% 2.46/1.03  --sub_typing                            true
% 2.46/1.03  --prep_gs_sim                           true
% 2.46/1.03  --prep_unflatten                        true
% 2.46/1.03  --prep_res_sim                          true
% 2.46/1.03  --prep_upred                            true
% 2.46/1.03  --prep_sem_filter                       exhaustive
% 2.46/1.03  --prep_sem_filter_out                   false
% 2.46/1.03  --pred_elim                             true
% 2.46/1.03  --res_sim_input                         true
% 2.46/1.03  --eq_ax_congr_red                       true
% 2.46/1.03  --pure_diseq_elim                       true
% 2.46/1.03  --brand_transform                       false
% 2.46/1.03  --non_eq_to_eq                          false
% 2.46/1.03  --prep_def_merge                        true
% 2.46/1.03  --prep_def_merge_prop_impl              false
% 2.46/1.03  --prep_def_merge_mbd                    true
% 2.46/1.03  --prep_def_merge_tr_red                 false
% 2.46/1.03  --prep_def_merge_tr_cl                  false
% 2.46/1.03  --smt_preprocessing                     true
% 2.46/1.03  --smt_ac_axioms                         fast
% 2.46/1.03  --preprocessed_out                      false
% 2.46/1.03  --preprocessed_stats                    false
% 2.46/1.03  
% 2.46/1.03  ------ Abstraction refinement Options
% 2.46/1.03  
% 2.46/1.03  --abstr_ref                             []
% 2.46/1.03  --abstr_ref_prep                        false
% 2.46/1.03  --abstr_ref_until_sat                   false
% 2.46/1.03  --abstr_ref_sig_restrict                funpre
% 2.46/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 2.46/1.03  --abstr_ref_under                       []
% 2.46/1.03  
% 2.46/1.03  ------ SAT Options
% 2.46/1.03  
% 2.46/1.03  --sat_mode                              false
% 2.46/1.03  --sat_fm_restart_options                ""
% 2.46/1.03  --sat_gr_def                            false
% 2.46/1.03  --sat_epr_types                         true
% 2.46/1.03  --sat_non_cyclic_types                  false
% 2.46/1.03  --sat_finite_models                     false
% 2.46/1.03  --sat_fm_lemmas                         false
% 2.46/1.03  --sat_fm_prep                           false
% 2.46/1.03  --sat_fm_uc_incr                        true
% 2.46/1.03  --sat_out_model                         small
% 2.46/1.03  --sat_out_clauses                       false
% 2.46/1.03  
% 2.46/1.03  ------ QBF Options
% 2.46/1.03  
% 2.46/1.03  --qbf_mode                              false
% 2.46/1.03  --qbf_elim_univ                         false
% 2.46/1.03  --qbf_dom_inst                          none
% 2.46/1.03  --qbf_dom_pre_inst                      false
% 2.46/1.03  --qbf_sk_in                             false
% 2.46/1.03  --qbf_pred_elim                         true
% 2.46/1.03  --qbf_split                             512
% 2.46/1.03  
% 2.46/1.03  ------ BMC1 Options
% 2.46/1.03  
% 2.46/1.03  --bmc1_incremental                      false
% 2.46/1.03  --bmc1_axioms                           reachable_all
% 2.46/1.03  --bmc1_min_bound                        0
% 2.46/1.03  --bmc1_max_bound                        -1
% 2.46/1.03  --bmc1_max_bound_default                -1
% 2.46/1.03  --bmc1_symbol_reachability              true
% 2.46/1.03  --bmc1_property_lemmas                  false
% 2.46/1.03  --bmc1_k_induction                      false
% 2.46/1.03  --bmc1_non_equiv_states                 false
% 2.46/1.03  --bmc1_deadlock                         false
% 2.46/1.03  --bmc1_ucm                              false
% 2.46/1.03  --bmc1_add_unsat_core                   none
% 2.46/1.03  --bmc1_unsat_core_children              false
% 2.46/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 2.46/1.03  --bmc1_out_stat                         full
% 2.46/1.03  --bmc1_ground_init                      false
% 2.46/1.03  --bmc1_pre_inst_next_state              false
% 2.46/1.03  --bmc1_pre_inst_state                   false
% 2.46/1.03  --bmc1_pre_inst_reach_state             false
% 2.46/1.03  --bmc1_out_unsat_core                   false
% 2.46/1.03  --bmc1_aig_witness_out                  false
% 2.46/1.03  --bmc1_verbose                          false
% 2.46/1.03  --bmc1_dump_clauses_tptp                false
% 2.46/1.03  --bmc1_dump_unsat_core_tptp             false
% 2.46/1.03  --bmc1_dump_file                        -
% 2.46/1.03  --bmc1_ucm_expand_uc_limit              128
% 2.46/1.03  --bmc1_ucm_n_expand_iterations          6
% 2.46/1.03  --bmc1_ucm_extend_mode                  1
% 2.46/1.03  --bmc1_ucm_init_mode                    2
% 2.46/1.03  --bmc1_ucm_cone_mode                    none
% 2.46/1.03  --bmc1_ucm_reduced_relation_type        0
% 2.46/1.03  --bmc1_ucm_relax_model                  4
% 2.46/1.03  --bmc1_ucm_full_tr_after_sat            true
% 2.46/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 2.46/1.03  --bmc1_ucm_layered_model                none
% 2.46/1.03  --bmc1_ucm_max_lemma_size               10
% 2.46/1.03  
% 2.46/1.03  ------ AIG Options
% 2.46/1.03  
% 2.46/1.03  --aig_mode                              false
% 2.46/1.03  
% 2.46/1.03  ------ Instantiation Options
% 2.46/1.03  
% 2.46/1.03  --instantiation_flag                    true
% 2.46/1.03  --inst_sos_flag                         false
% 2.46/1.03  --inst_sos_phase                        true
% 2.46/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.46/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.46/1.03  --inst_lit_sel_side                     none
% 2.46/1.03  --inst_solver_per_active                1400
% 2.46/1.03  --inst_solver_calls_frac                1.
% 2.46/1.03  --inst_passive_queue_type               priority_queues
% 2.46/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.46/1.03  --inst_passive_queues_freq              [25;2]
% 2.46/1.03  --inst_dismatching                      true
% 2.46/1.03  --inst_eager_unprocessed_to_passive     true
% 2.46/1.03  --inst_prop_sim_given                   true
% 2.46/1.03  --inst_prop_sim_new                     false
% 2.46/1.03  --inst_subs_new                         false
% 2.46/1.03  --inst_eq_res_simp                      false
% 2.46/1.03  --inst_subs_given                       false
% 2.46/1.03  --inst_orphan_elimination               true
% 2.46/1.03  --inst_learning_loop_flag               true
% 2.46/1.03  --inst_learning_start                   3000
% 2.46/1.03  --inst_learning_factor                  2
% 2.46/1.03  --inst_start_prop_sim_after_learn       3
% 2.46/1.03  --inst_sel_renew                        solver
% 2.46/1.03  --inst_lit_activity_flag                true
% 2.46/1.03  --inst_restr_to_given                   false
% 2.46/1.03  --inst_activity_threshold               500
% 2.46/1.03  --inst_out_proof                        true
% 2.46/1.03  
% 2.46/1.03  ------ Resolution Options
% 2.46/1.03  
% 2.46/1.03  --resolution_flag                       false
% 2.46/1.03  --res_lit_sel                           adaptive
% 2.46/1.03  --res_lit_sel_side                      none
% 2.46/1.03  --res_ordering                          kbo
% 2.46/1.03  --res_to_prop_solver                    active
% 2.46/1.03  --res_prop_simpl_new                    false
% 2.46/1.03  --res_prop_simpl_given                  true
% 2.46/1.03  --res_passive_queue_type                priority_queues
% 2.46/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.46/1.03  --res_passive_queues_freq               [15;5]
% 2.46/1.03  --res_forward_subs                      full
% 2.46/1.03  --res_backward_subs                     full
% 2.46/1.03  --res_forward_subs_resolution           true
% 2.46/1.03  --res_backward_subs_resolution          true
% 2.46/1.03  --res_orphan_elimination                true
% 2.46/1.03  --res_time_limit                        2.
% 2.46/1.03  --res_out_proof                         true
% 2.46/1.03  
% 2.46/1.03  ------ Superposition Options
% 2.46/1.03  
% 2.46/1.03  --superposition_flag                    true
% 2.46/1.03  --sup_passive_queue_type                priority_queues
% 2.46/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.46/1.03  --sup_passive_queues_freq               [8;1;4]
% 2.46/1.03  --demod_completeness_check              fast
% 2.46/1.03  --demod_use_ground                      true
% 2.46/1.03  --sup_to_prop_solver                    passive
% 2.46/1.03  --sup_prop_simpl_new                    true
% 2.46/1.03  --sup_prop_simpl_given                  true
% 2.46/1.03  --sup_fun_splitting                     false
% 2.46/1.03  --sup_smt_interval                      50000
% 2.46/1.03  
% 2.46/1.03  ------ Superposition Simplification Setup
% 2.46/1.03  
% 2.46/1.03  --sup_indices_passive                   []
% 2.46/1.03  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.03  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.46/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 2.46/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.03  --sup_full_bw                           [BwDemod]
% 2.46/1.03  --sup_immed_triv                        [TrivRules]
% 2.46/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.46/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.03  --sup_immed_bw_main                     []
% 2.46/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 2.46/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.46/1.03  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.46/1.03  
% 2.46/1.03  ------ Combination Options
% 2.46/1.03  
% 2.46/1.03  --comb_res_mult                         3
% 2.46/1.03  --comb_sup_mult                         2
% 2.46/1.03  --comb_inst_mult                        10
% 2.46/1.03  
% 2.46/1.03  ------ Debug Options
% 2.46/1.03  
% 2.46/1.03  --dbg_backtrace                         false
% 2.46/1.03  --dbg_dump_prop_clauses                 false
% 2.46/1.03  --dbg_dump_prop_clauses_file            -
% 2.46/1.03  --dbg_out_stat                          false
% 2.46/1.03  
% 2.46/1.03  
% 2.46/1.03  
% 2.46/1.03  
% 2.46/1.03  ------ Proving...
% 2.46/1.03  
% 2.46/1.03  
% 2.46/1.03  % SZS status Theorem for theBenchmark.p
% 2.46/1.03  
% 2.46/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 2.46/1.03  
% 2.46/1.03  fof(f9,conjecture,(
% 2.46/1.03    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.46/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.03  
% 2.46/1.03  fof(f10,negated_conjecture,(
% 2.46/1.03    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.46/1.03    inference(negated_conjecture,[],[f9])).
% 2.46/1.03  
% 2.46/1.03  fof(f25,plain,(
% 2.46/1.03    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.46/1.03    inference(ennf_transformation,[],[f10])).
% 2.46/1.03  
% 2.46/1.03  fof(f26,plain,(
% 2.46/1.03    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.46/1.03    inference(flattening,[],[f25])).
% 2.46/1.03  
% 2.46/1.03  fof(f30,plain,(
% 2.46/1.03    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.46/1.03    introduced(choice_axiom,[])).
% 2.46/1.03  
% 2.46/1.03  fof(f29,plain,(
% 2.46/1.03    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.46/1.03    introduced(choice_axiom,[])).
% 2.46/1.03  
% 2.46/1.03  fof(f28,plain,(
% 2.46/1.03    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.46/1.03    introduced(choice_axiom,[])).
% 2.46/1.03  
% 2.46/1.03  fof(f31,plain,(
% 2.46/1.03    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.46/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f26,f30,f29,f28])).
% 2.46/1.03  
% 2.46/1.03  fof(f52,plain,(
% 2.46/1.03    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.46/1.03    inference(cnf_transformation,[],[f31])).
% 2.46/1.03  
% 2.46/1.03  fof(f6,axiom,(
% 2.46/1.03    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.46/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.03  
% 2.46/1.03  fof(f20,plain,(
% 2.46/1.03    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.46/1.03    inference(ennf_transformation,[],[f6])).
% 2.46/1.03  
% 2.46/1.03  fof(f42,plain,(
% 2.46/1.03    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.46/1.03    inference(cnf_transformation,[],[f20])).
% 2.46/1.03  
% 2.46/1.03  fof(f46,plain,(
% 2.46/1.03    l1_struct_0(sK0)),
% 2.46/1.03    inference(cnf_transformation,[],[f31])).
% 2.46/1.03  
% 2.46/1.03  fof(f48,plain,(
% 2.46/1.03    l1_struct_0(sK1)),
% 2.46/1.03    inference(cnf_transformation,[],[f31])).
% 2.46/1.03  
% 2.46/1.03  fof(f7,axiom,(
% 2.46/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.46/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.03  
% 2.46/1.03  fof(f21,plain,(
% 2.46/1.03    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.46/1.03    inference(ennf_transformation,[],[f7])).
% 2.46/1.03  
% 2.46/1.03  fof(f22,plain,(
% 2.46/1.03    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.46/1.03    inference(flattening,[],[f21])).
% 2.46/1.03  
% 2.46/1.03  fof(f43,plain,(
% 2.46/1.03    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.46/1.03    inference(cnf_transformation,[],[f22])).
% 2.46/1.03  
% 2.46/1.03  fof(f49,plain,(
% 2.46/1.03    v1_funct_1(sK2)),
% 2.46/1.03    inference(cnf_transformation,[],[f31])).
% 2.46/1.03  
% 2.46/1.03  fof(f53,plain,(
% 2.46/1.03    v2_funct_1(sK2)),
% 2.46/1.03    inference(cnf_transformation,[],[f31])).
% 2.46/1.03  
% 2.46/1.03  fof(f50,plain,(
% 2.46/1.03    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.46/1.03    inference(cnf_transformation,[],[f31])).
% 2.46/1.03  
% 2.46/1.03  fof(f51,plain,(
% 2.46/1.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.46/1.03    inference(cnf_transformation,[],[f31])).
% 2.46/1.03  
% 2.46/1.03  fof(f8,axiom,(
% 2.46/1.03    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 2.46/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.03  
% 2.46/1.03  fof(f23,plain,(
% 2.46/1.03    ! [X0] : (! [X1] : (! [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 2.46/1.03    inference(ennf_transformation,[],[f8])).
% 2.46/1.03  
% 2.46/1.03  fof(f24,plain,(
% 2.46/1.03    ! [X0] : (! [X1] : (! [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.46/1.03    inference(flattening,[],[f23])).
% 2.46/1.03  
% 2.46/1.03  fof(f45,plain,(
% 2.46/1.03    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.46/1.03    inference(cnf_transformation,[],[f24])).
% 2.46/1.03  
% 2.46/1.03  fof(f47,plain,(
% 2.46/1.03    ~v2_struct_0(sK1)),
% 2.46/1.03    inference(cnf_transformation,[],[f31])).
% 2.46/1.03  
% 2.46/1.03  fof(f3,axiom,(
% 2.46/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.46/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.03  
% 2.46/1.03  fof(f15,plain,(
% 2.46/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.46/1.03    inference(ennf_transformation,[],[f3])).
% 2.46/1.03  
% 2.46/1.03  fof(f36,plain,(
% 2.46/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.46/1.03    inference(cnf_transformation,[],[f15])).
% 2.46/1.03  
% 2.46/1.03  fof(f2,axiom,(
% 2.46/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.46/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.03  
% 2.46/1.03  fof(f13,plain,(
% 2.46/1.03    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.46/1.03    inference(ennf_transformation,[],[f2])).
% 2.46/1.03  
% 2.46/1.03  fof(f14,plain,(
% 2.46/1.03    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.46/1.03    inference(flattening,[],[f13])).
% 2.46/1.03  
% 2.46/1.03  fof(f35,plain,(
% 2.46/1.03    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.46/1.03    inference(cnf_transformation,[],[f14])).
% 2.46/1.03  
% 2.46/1.03  fof(f1,axiom,(
% 2.46/1.03    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.46/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.03  
% 2.46/1.03  fof(f11,plain,(
% 2.46/1.03    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.46/1.03    inference(ennf_transformation,[],[f1])).
% 2.46/1.03  
% 2.46/1.03  fof(f12,plain,(
% 2.46/1.03    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.46/1.03    inference(flattening,[],[f11])).
% 2.46/1.03  
% 2.46/1.03  fof(f34,plain,(
% 2.46/1.03    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.46/1.03    inference(cnf_transformation,[],[f12])).
% 2.46/1.03  
% 2.46/1.03  fof(f33,plain,(
% 2.46/1.03    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.46/1.03    inference(cnf_transformation,[],[f12])).
% 2.46/1.03  
% 2.46/1.03  fof(f5,axiom,(
% 2.46/1.03    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.46/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.03  
% 2.46/1.03  fof(f18,plain,(
% 2.46/1.03    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.46/1.03    inference(ennf_transformation,[],[f5])).
% 2.46/1.03  
% 2.46/1.03  fof(f19,plain,(
% 2.46/1.03    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.46/1.03    inference(flattening,[],[f18])).
% 2.46/1.03  
% 2.46/1.03  fof(f41,plain,(
% 2.46/1.03    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.46/1.03    inference(cnf_transformation,[],[f19])).
% 2.46/1.03  
% 2.46/1.03  fof(f40,plain,(
% 2.46/1.03    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.46/1.03    inference(cnf_transformation,[],[f19])).
% 2.46/1.03  
% 2.46/1.03  fof(f4,axiom,(
% 2.46/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.46/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.46/1.03  
% 2.46/1.03  fof(f16,plain,(
% 2.46/1.03    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.46/1.03    inference(ennf_transformation,[],[f4])).
% 2.46/1.03  
% 2.46/1.03  fof(f17,plain,(
% 2.46/1.03    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.46/1.03    inference(flattening,[],[f16])).
% 2.46/1.03  
% 2.46/1.03  fof(f27,plain,(
% 2.46/1.03    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.46/1.03    inference(nnf_transformation,[],[f17])).
% 2.46/1.03  
% 2.46/1.03  fof(f38,plain,(
% 2.46/1.03    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.46/1.03    inference(cnf_transformation,[],[f27])).
% 2.46/1.03  
% 2.46/1.03  fof(f55,plain,(
% 2.46/1.03    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.46/1.03    inference(equality_resolution,[],[f38])).
% 2.46/1.03  
% 2.46/1.03  fof(f54,plain,(
% 2.46/1.03    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.46/1.03    inference(cnf_transformation,[],[f31])).
% 2.46/1.03  
% 2.46/1.03  cnf(c_16,negated_conjecture,
% 2.46/1.03      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.46/1.03      inference(cnf_transformation,[],[f52]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_627,negated_conjecture,
% 2.46/1.03      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_16]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_10,plain,
% 2.46/1.03      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.46/1.03      inference(cnf_transformation,[],[f42]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_22,negated_conjecture,
% 2.46/1.03      ( l1_struct_0(sK0) ),
% 2.46/1.03      inference(cnf_transformation,[],[f46]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_360,plain,
% 2.46/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.46/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_22]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_361,plain,
% 2.46/1.03      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.46/1.03      inference(unflattening,[status(thm)],[c_360]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_620,plain,
% 2.46/1.03      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_361]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_20,negated_conjecture,
% 2.46/1.03      ( l1_struct_0(sK1) ),
% 2.46/1.03      inference(cnf_transformation,[],[f48]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_355,plain,
% 2.46/1.03      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.46/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_356,plain,
% 2.46/1.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.46/1.03      inference(unflattening,[status(thm)],[c_355]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_621,plain,
% 2.46/1.03      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_356]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1045,plain,
% 2.46/1.03      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.46/1.03      inference(light_normalisation,[status(thm)],[c_627,c_620,c_621]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_11,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | ~ v2_funct_1(X0)
% 2.46/1.03      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.46/1.03      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.46/1.03      inference(cnf_transformation,[],[f43]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_629,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0_47,X0_48,X1_48)
% 2.46/1.03      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.46/1.03      | ~ v1_funct_1(X0_47)
% 2.46/1.03      | ~ v2_funct_1(X0_47)
% 2.46/1.03      | k2_relset_1(X0_48,X1_48,X0_47) != X1_48
% 2.46/1.03      | k2_tops_2(X0_48,X1_48,X0_47) = k2_funct_1(X0_47) ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_11]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1023,plain,
% 2.46/1.03      ( k2_relset_1(X0_48,X1_48,X0_47) != X1_48
% 2.46/1.03      | k2_tops_2(X0_48,X1_48,X0_47) = k2_funct_1(X0_47)
% 2.46/1.03      | v1_funct_2(X0_47,X0_48,X1_48) != iProver_top
% 2.46/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.46/1.03      | v1_funct_1(X0_47) != iProver_top
% 2.46/1.03      | v2_funct_1(X0_47) != iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_629]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1918,plain,
% 2.46/1.03      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.46/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.46/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_funct_1(sK2) != iProver_top
% 2.46/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.46/1.03      inference(superposition,[status(thm)],[c_1045,c_1023]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_19,negated_conjecture,
% 2.46/1.03      ( v1_funct_1(sK2) ),
% 2.46/1.03      inference(cnf_transformation,[],[f49]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_26,plain,
% 2.46/1.03      ( v1_funct_1(sK2) = iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_15,negated_conjecture,
% 2.46/1.03      ( v2_funct_1(sK2) ),
% 2.46/1.03      inference(cnf_transformation,[],[f53]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_29,plain,
% 2.46/1.03      ( v2_funct_1(sK2) = iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_18,negated_conjecture,
% 2.46/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.46/1.03      inference(cnf_transformation,[],[f50]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_625,negated_conjecture,
% 2.46/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_18]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1026,plain,
% 2.46/1.03      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_625]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1042,plain,
% 2.46/1.03      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.46/1.03      inference(light_normalisation,[status(thm)],[c_1026,c_620,c_621]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_17,negated_conjecture,
% 2.46/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.46/1.03      inference(cnf_transformation,[],[f51]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_626,negated_conjecture,
% 2.46/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_17]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1025,plain,
% 2.46/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_626]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1048,plain,
% 2.46/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.46/1.03      inference(light_normalisation,[status(thm)],[c_1025,c_620,c_621]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_2132,plain,
% 2.46/1.03      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.46/1.03      inference(global_propositional_subsumption,
% 2.46/1.03                [status(thm)],
% 2.46/1.03                [c_1918,c_26,c_29,c_1042,c_1048]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_12,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.46/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.46/1.03      | v2_struct_0(X2)
% 2.46/1.03      | ~ l1_struct_0(X1)
% 2.46/1.03      | ~ l1_struct_0(X2)
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | ~ v2_funct_1(X0)
% 2.46/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.46/1.03      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 2.46/1.03      inference(cnf_transformation,[],[f45]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_21,negated_conjecture,
% 2.46/1.03      ( ~ v2_struct_0(sK1) ),
% 2.46/1.03      inference(cnf_transformation,[],[f47]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_308,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.46/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.46/1.03      | ~ l1_struct_0(X2)
% 2.46/1.03      | ~ l1_struct_0(X1)
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | ~ v2_funct_1(X0)
% 2.46/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.46/1.03      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 2.46/1.03      | sK1 != X2 ),
% 2.46/1.03      inference(resolution_lifted,[status(thm)],[c_12,c_21]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_309,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.46/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.46/1.03      | ~ l1_struct_0(X1)
% 2.46/1.03      | ~ l1_struct_0(sK1)
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | ~ v2_funct_1(X0)
% 2.46/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.46/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.46/1.03      inference(unflattening,[status(thm)],[c_308]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_313,plain,
% 2.46/1.03      ( ~ l1_struct_0(X1)
% 2.46/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.46/1.03      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | ~ v2_funct_1(X0)
% 2.46/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.46/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.46/1.03      inference(global_propositional_subsumption,
% 2.46/1.03                [status(thm)],
% 2.46/1.03                [c_309,c_20]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_314,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.46/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.46/1.03      | ~ l1_struct_0(X1)
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | ~ v2_funct_1(X0)
% 2.46/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.46/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.46/1.03      inference(renaming,[status(thm)],[c_313]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_413,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.46/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | ~ v2_funct_1(X0)
% 2.46/1.03      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.46/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1)
% 2.46/1.03      | sK0 != X1 ),
% 2.46/1.03      inference(resolution_lifted,[status(thm)],[c_314,c_22]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_414,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.46/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | ~ v2_funct_1(X0)
% 2.46/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK0)
% 2.46/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 2.46/1.03      inference(unflattening,[status(thm)],[c_413]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_617,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0_47,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.46/1.03      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.46/1.03      | ~ v1_funct_1(X0_47)
% 2.46/1.03      | ~ v2_funct_1(X0_47)
% 2.46/1.03      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
% 2.46/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_47) != k2_struct_0(sK1) ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_414]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1032,plain,
% 2.46/1.03      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
% 2.46/1.03      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.46/1.03      | v1_funct_2(X0_47,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.46/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_funct_1(X0_47) != iProver_top
% 2.46/1.03      | v2_funct_1(X0_47) != iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_617]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1157,plain,
% 2.46/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
% 2.46/1.03      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.46/1.03      | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.46/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_funct_1(X0_47) != iProver_top
% 2.46/1.03      | v2_funct_1(X0_47) != iProver_top ),
% 2.46/1.03      inference(light_normalisation,[status(thm)],[c_1032,c_620,c_621]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1510,plain,
% 2.46/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.46/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.46/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_funct_1(sK2) != iProver_top
% 2.46/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.46/1.03      inference(superposition,[status(thm)],[c_1045,c_1157]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1210,plain,
% 2.46/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.46/1.03      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.46/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.46/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_funct_1(sK2) != iProver_top
% 2.46/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.46/1.03      inference(instantiation,[status(thm)],[c_1157]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1513,plain,
% 2.46/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0) ),
% 2.46/1.03      inference(global_propositional_subsumption,
% 2.46/1.03                [status(thm)],
% 2.46/1.03                [c_1510,c_26,c_29,c_1042,c_1045,c_1048,c_1210]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_2137,plain,
% 2.46/1.03      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 2.46/1.03      inference(demodulation,[status(thm)],[c_2132,c_1513]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_2357,plain,
% 2.46/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.46/1.03      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.46/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.46/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.46/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.46/1.03      inference(superposition,[status(thm)],[c_2137,c_1023]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_4,plain,
% 2.46/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.03      | v1_relat_1(X0) ),
% 2.46/1.03      inference(cnf_transformation,[],[f36]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_632,plain,
% 2.46/1.03      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.46/1.03      | v1_relat_1(X0_47) ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_4]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1020,plain,
% 2.46/1.03      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.46/1.03      | v1_relat_1(X0_47) = iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_632]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1329,plain,
% 2.46/1.03      ( v1_relat_1(sK2) = iProver_top ),
% 2.46/1.03      inference(superposition,[status(thm)],[c_1048,c_1020]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_3,plain,
% 2.46/1.03      ( ~ v1_relat_1(X0)
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | ~ v2_funct_1(X0)
% 2.46/1.03      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.46/1.03      inference(cnf_transformation,[],[f35]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_633,plain,
% 2.46/1.03      ( ~ v1_relat_1(X0_47)
% 2.46/1.03      | ~ v1_funct_1(X0_47)
% 2.46/1.03      | ~ v2_funct_1(X0_47)
% 2.46/1.03      | k2_funct_1(k2_funct_1(X0_47)) = X0_47 ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_3]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1019,plain,
% 2.46/1.03      ( k2_funct_1(k2_funct_1(X0_47)) = X0_47
% 2.46/1.03      | v1_relat_1(X0_47) != iProver_top
% 2.46/1.03      | v1_funct_1(X0_47) != iProver_top
% 2.46/1.03      | v2_funct_1(X0_47) != iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_633]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1664,plain,
% 2.46/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.46/1.03      | v1_funct_1(sK2) != iProver_top
% 2.46/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.46/1.03      inference(superposition,[status(thm)],[c_1329,c_1019]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_681,plain,
% 2.46/1.03      ( ~ v1_relat_1(sK2)
% 2.46/1.03      | ~ v1_funct_1(sK2)
% 2.46/1.03      | ~ v2_funct_1(sK2)
% 2.46/1.03      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.46/1.03      inference(instantiation,[status(thm)],[c_633]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1245,plain,
% 2.46/1.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.46/1.03      | v1_relat_1(sK2) ),
% 2.46/1.03      inference(instantiation,[status(thm)],[c_632]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1738,plain,
% 2.46/1.03      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.46/1.03      inference(global_propositional_subsumption,
% 2.46/1.03                [status(thm)],
% 2.46/1.03                [c_1664,c_19,c_17,c_15,c_681,c_1245]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_2377,plain,
% 2.46/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.46/1.03      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.46/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.46/1.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.46/1.03      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.46/1.03      inference(light_normalisation,[status(thm)],[c_2357,c_1738]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_28,plain,
% 2.46/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_0,plain,
% 2.46/1.03      ( ~ v1_relat_1(X0)
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | ~ v2_funct_1(X0)
% 2.46/1.03      | v2_funct_1(k2_funct_1(X0)) ),
% 2.46/1.03      inference(cnf_transformation,[],[f34]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_636,plain,
% 2.46/1.03      ( ~ v1_relat_1(X0_47)
% 2.46/1.03      | ~ v1_funct_1(X0_47)
% 2.46/1.03      | ~ v2_funct_1(X0_47)
% 2.46/1.03      | v2_funct_1(k2_funct_1(X0_47)) ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_0]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_671,plain,
% 2.46/1.03      ( v1_relat_1(X0_47) != iProver_top
% 2.46/1.03      | v1_funct_1(X0_47) != iProver_top
% 2.46/1.03      | v2_funct_1(X0_47) != iProver_top
% 2.46/1.03      | v2_funct_1(k2_funct_1(X0_47)) = iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_636]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_673,plain,
% 2.46/1.03      ( v1_relat_1(sK2) != iProver_top
% 2.46/1.03      | v1_funct_1(sK2) != iProver_top
% 2.46/1.03      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.46/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.46/1.03      inference(instantiation,[status(thm)],[c_671]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1,plain,
% 2.46/1.03      ( ~ v1_relat_1(X0)
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | v1_funct_1(k2_funct_1(X0))
% 2.46/1.03      | ~ v2_funct_1(X0) ),
% 2.46/1.03      inference(cnf_transformation,[],[f33]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_635,plain,
% 2.46/1.03      ( ~ v1_relat_1(X0_47)
% 2.46/1.03      | ~ v1_funct_1(X0_47)
% 2.46/1.03      | v1_funct_1(k2_funct_1(X0_47))
% 2.46/1.03      | ~ v2_funct_1(X0_47) ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_1]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_674,plain,
% 2.46/1.03      ( v1_relat_1(X0_47) != iProver_top
% 2.46/1.03      | v1_funct_1(X0_47) != iProver_top
% 2.46/1.03      | v1_funct_1(k2_funct_1(X0_47)) = iProver_top
% 2.46/1.03      | v2_funct_1(X0_47) != iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_635]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_676,plain,
% 2.46/1.03      ( v1_relat_1(sK2) != iProver_top
% 2.46/1.03      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.46/1.03      | v1_funct_1(sK2) != iProver_top
% 2.46/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.46/1.03      inference(instantiation,[status(thm)],[c_674]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1246,plain,
% 2.46/1.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_relat_1(sK2) = iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_1245]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_7,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.03      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | ~ v2_funct_1(X0)
% 2.46/1.03      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.46/1.03      inference(cnf_transformation,[],[f41]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_631,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0_47,X0_48,X1_48)
% 2.46/1.03      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.46/1.03      | m1_subset_1(k2_funct_1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48)))
% 2.46/1.03      | ~ v1_funct_1(X0_47)
% 2.46/1.03      | ~ v2_funct_1(X0_47)
% 2.46/1.03      | k2_relset_1(X0_48,X1_48,X0_47) != X1_48 ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_7]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1021,plain,
% 2.46/1.03      ( k2_relset_1(X0_48,X1_48,X0_47) != X1_48
% 2.46/1.03      | v1_funct_2(X0_47,X0_48,X1_48) != iProver_top
% 2.46/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.46/1.03      | m1_subset_1(k2_funct_1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48))) = iProver_top
% 2.46/1.03      | v1_funct_1(X0_47) != iProver_top
% 2.46/1.03      | v2_funct_1(X0_47) != iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_631]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1751,plain,
% 2.46/1.03      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.46/1.03      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.46/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_funct_1(sK2) != iProver_top
% 2.46/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.46/1.03      inference(superposition,[status(thm)],[c_1045,c_1021]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_8,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/1.03      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.46/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | ~ v2_funct_1(X0)
% 2.46/1.03      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.46/1.03      inference(cnf_transformation,[],[f40]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_630,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0_47,X0_48,X1_48)
% 2.46/1.03      | v1_funct_2(k2_funct_1(X0_47),X1_48,X0_48)
% 2.46/1.03      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.46/1.03      | ~ v1_funct_1(X0_47)
% 2.46/1.03      | ~ v2_funct_1(X0_47)
% 2.46/1.03      | k2_relset_1(X0_48,X1_48,X0_47) != X1_48 ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_8]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1022,plain,
% 2.46/1.03      ( k2_relset_1(X0_48,X1_48,X0_47) != X1_48
% 2.46/1.03      | v1_funct_2(X0_47,X0_48,X1_48) != iProver_top
% 2.46/1.03      | v1_funct_2(k2_funct_1(X0_47),X1_48,X0_48) = iProver_top
% 2.46/1.03      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.46/1.03      | v1_funct_1(X0_47) != iProver_top
% 2.46/1.03      | v2_funct_1(X0_47) != iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_630]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1887,plain,
% 2.46/1.03      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.46/1.03      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.46/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_funct_1(sK2) != iProver_top
% 2.46/1.03      | v2_funct_1(sK2) != iProver_top ),
% 2.46/1.03      inference(superposition,[status(thm)],[c_1045,c_1022]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_2888,plain,
% 2.46/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.46/1.03      inference(global_propositional_subsumption,
% 2.46/1.03                [status(thm)],
% 2.46/1.03                [c_2377,c_26,c_28,c_29,c_673,c_676,c_1042,c_1048,c_1246,
% 2.46/1.03                 c_1751,c_1887]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_5,plain,
% 2.46/1.03      ( r2_funct_2(X0,X1,X2,X2)
% 2.46/1.03      | ~ v1_funct_2(X2,X0,X1)
% 2.46/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.46/1.03      | ~ v1_funct_1(X2) ),
% 2.46/1.03      inference(cnf_transformation,[],[f55]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_14,negated_conjecture,
% 2.46/1.03      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.46/1.03      inference(cnf_transformation,[],[f54]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_256,plain,
% 2.46/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 2.46/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.46/1.03      | ~ v1_funct_1(X0)
% 2.46/1.03      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.46/1.03      | u1_struct_0(sK1) != X2
% 2.46/1.03      | u1_struct_0(sK0) != X1
% 2.46/1.03      | sK2 != X0 ),
% 2.46/1.03      inference(resolution_lifted,[status(thm)],[c_5,c_14]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_257,plain,
% 2.46/1.03      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.46/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.46/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.46/1.03      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.46/1.03      inference(unflattening,[status(thm)],[c_256]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_622,plain,
% 2.46/1.03      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.46/1.03      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.46/1.03      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.46/1.03      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.46/1.03      inference(subtyping,[status(esa)],[c_257]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1029,plain,
% 2.46/1.03      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.46/1.03      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.46/1.03      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.46/1.03      inference(predicate_to_equality,[status(thm)],[c_622]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_1183,plain,
% 2.46/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.46/1.03      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.46/1.03      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 2.46/1.03      inference(light_normalisation,[status(thm)],[c_1029,c_620,c_621]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_2135,plain,
% 2.46/1.03      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.46/1.03      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.46/1.03      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.46/1.03      inference(demodulation,[status(thm)],[c_2132,c_1183]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_2468,plain,
% 2.46/1.03      ( v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.46/1.03      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 2.46/1.03      inference(global_propositional_subsumption,
% 2.46/1.03                [status(thm)],
% 2.46/1.03                [c_2135,c_26,c_28,c_29,c_673,c_676,c_1042,c_1048,c_1246,
% 2.46/1.03                 c_1751,c_1887,c_2377]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(c_2891,plain,
% 2.46/1.03      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.46/1.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.46/1.03      | v1_funct_1(sK2) != iProver_top ),
% 2.46/1.03      inference(demodulation,[status(thm)],[c_2888,c_2468]) ).
% 2.46/1.03  
% 2.46/1.03  cnf(contradiction,plain,
% 2.46/1.03      ( $false ),
% 2.46/1.03      inference(minisat,[status(thm)],[c_2891,c_1048,c_1042,c_26]) ).
% 2.46/1.03  
% 2.46/1.03  
% 2.46/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 2.46/1.03  
% 2.46/1.03  ------                               Statistics
% 2.46/1.03  
% 2.46/1.03  ------ General
% 2.46/1.03  
% 2.46/1.03  abstr_ref_over_cycles:                  0
% 2.46/1.03  abstr_ref_under_cycles:                 0
% 2.46/1.03  gc_basic_clause_elim:                   0
% 2.46/1.03  forced_gc_time:                         0
% 2.46/1.03  parsing_time:                           0.01
% 2.46/1.03  unif_index_cands_time:                  0.
% 2.46/1.03  unif_index_add_time:                    0.
% 2.46/1.03  orderings_time:                         0.
% 2.46/1.03  out_proof_time:                         0.023
% 2.46/1.03  total_time:                             0.164
% 2.46/1.03  num_of_symbols:                         52
% 2.46/1.03  num_of_terms:                           2737
% 2.46/1.03  
% 2.46/1.03  ------ Preprocessing
% 2.46/1.03  
% 2.46/1.03  num_of_splits:                          0
% 2.46/1.03  num_of_split_atoms:                     0
% 2.46/1.03  num_of_reused_defs:                     0
% 2.46/1.03  num_eq_ax_congr_red:                    2
% 2.46/1.03  num_of_sem_filtered_clauses:            1
% 2.46/1.03  num_of_subtypes:                        5
% 2.46/1.03  monotx_restored_types:                  0
% 2.46/1.03  sat_num_of_epr_types:                   0
% 2.46/1.03  sat_num_of_non_cyclic_types:            0
% 2.46/1.03  sat_guarded_non_collapsed_types:        1
% 2.46/1.03  num_pure_diseq_elim:                    0
% 2.46/1.03  simp_replaced_by:                       0
% 2.46/1.03  res_preprocessed:                       121
% 2.46/1.03  prep_upred:                             0
% 2.46/1.03  prep_unflattend:                        15
% 2.46/1.03  smt_new_axioms:                         0
% 2.46/1.03  pred_elim_cands:                        5
% 2.46/1.03  pred_elim:                              3
% 2.46/1.03  pred_elim_cl:                           2
% 2.46/1.03  pred_elim_cycles:                       5
% 2.46/1.03  merged_defs:                            0
% 2.46/1.03  merged_defs_ncl:                        0
% 2.46/1.03  bin_hyper_res:                          0
% 2.46/1.03  prep_cycles:                            4
% 2.46/1.03  pred_elim_time:                         0.008
% 2.46/1.03  splitting_time:                         0.
% 2.46/1.03  sem_filter_time:                        0.
% 2.46/1.03  monotx_time:                            0.
% 2.46/1.03  subtype_inf_time:                       0.001
% 2.46/1.03  
% 2.46/1.03  ------ Problem properties
% 2.46/1.03  
% 2.46/1.03  clauses:                                21
% 2.46/1.03  conjectures:                            5
% 2.46/1.03  epr:                                    2
% 2.46/1.03  horn:                                   21
% 2.46/1.03  ground:                                 8
% 2.46/1.03  unary:                                  7
% 2.46/1.03  binary:                                 1
% 2.46/1.03  lits:                                   75
% 2.46/1.03  lits_eq:                                17
% 2.46/1.03  fd_pure:                                0
% 2.46/1.03  fd_pseudo:                              0
% 2.46/1.03  fd_cond:                                0
% 2.46/1.03  fd_pseudo_cond:                         0
% 2.46/1.03  ac_symbols:                             0
% 2.46/1.03  
% 2.46/1.03  ------ Propositional Solver
% 2.46/1.03  
% 2.46/1.03  prop_solver_calls:                      30
% 2.46/1.03  prop_fast_solver_calls:                 1073
% 2.46/1.03  smt_solver_calls:                       0
% 2.46/1.03  smt_fast_solver_calls:                  0
% 2.46/1.03  prop_num_of_clauses:                    958
% 2.46/1.03  prop_preprocess_simplified:             3821
% 2.46/1.03  prop_fo_subsumed:                       45
% 2.46/1.03  prop_solver_time:                       0.
% 2.46/1.03  smt_solver_time:                        0.
% 2.46/1.03  smt_fast_solver_time:                   0.
% 2.46/1.03  prop_fast_solver_time:                  0.
% 2.46/1.03  prop_unsat_core_time:                   0.
% 2.46/1.03  
% 2.46/1.03  ------ QBF
% 2.46/1.03  
% 2.46/1.03  qbf_q_res:                              0
% 2.46/1.03  qbf_num_tautologies:                    0
% 2.46/1.03  qbf_prep_cycles:                        0
% 2.46/1.03  
% 2.46/1.03  ------ BMC1
% 2.46/1.03  
% 2.46/1.03  bmc1_current_bound:                     -1
% 2.46/1.03  bmc1_last_solved_bound:                 -1
% 2.46/1.03  bmc1_unsat_core_size:                   -1
% 2.46/1.03  bmc1_unsat_core_parents_size:           -1
% 2.46/1.03  bmc1_merge_next_fun:                    0
% 2.46/1.03  bmc1_unsat_core_clauses_time:           0.
% 2.46/1.03  
% 2.46/1.03  ------ Instantiation
% 2.46/1.03  
% 2.46/1.03  inst_num_of_clauses:                    329
% 2.46/1.03  inst_num_in_passive:                    133
% 2.46/1.03  inst_num_in_active:                     186
% 2.46/1.03  inst_num_in_unprocessed:                10
% 2.46/1.03  inst_num_of_loops:                      200
% 2.46/1.03  inst_num_of_learning_restarts:          0
% 2.46/1.03  inst_num_moves_active_passive:          9
% 2.46/1.03  inst_lit_activity:                      0
% 2.46/1.03  inst_lit_activity_moves:                0
% 2.46/1.03  inst_num_tautologies:                   0
% 2.46/1.03  inst_num_prop_implied:                  0
% 2.46/1.03  inst_num_existing_simplified:           0
% 2.46/1.03  inst_num_eq_res_simplified:             0
% 2.46/1.03  inst_num_child_elim:                    0
% 2.46/1.03  inst_num_of_dismatching_blockings:      42
% 2.46/1.03  inst_num_of_non_proper_insts:           302
% 2.46/1.03  inst_num_of_duplicates:                 0
% 2.46/1.03  inst_inst_num_from_inst_to_res:         0
% 2.46/1.03  inst_dismatching_checking_time:         0.
% 2.46/1.03  
% 2.46/1.03  ------ Resolution
% 2.46/1.03  
% 2.46/1.03  res_num_of_clauses:                     0
% 2.46/1.03  res_num_in_passive:                     0
% 2.46/1.03  res_num_in_active:                      0
% 2.46/1.03  res_num_of_loops:                       125
% 2.46/1.03  res_forward_subset_subsumed:            38
% 2.46/1.03  res_backward_subset_subsumed:           0
% 2.46/1.03  res_forward_subsumed:                   0
% 2.46/1.03  res_backward_subsumed:                  0
% 2.46/1.03  res_forward_subsumption_resolution:     0
% 2.46/1.03  res_backward_subsumption_resolution:    0
% 2.46/1.03  res_clause_to_clause_subsumption:       128
% 2.46/1.03  res_orphan_elimination:                 0
% 2.46/1.03  res_tautology_del:                      31
% 2.46/1.03  res_num_eq_res_simplified:              0
% 2.46/1.03  res_num_sel_changes:                    0
% 2.46/1.03  res_moves_from_active_to_pass:          0
% 2.46/1.03  
% 2.46/1.03  ------ Superposition
% 2.46/1.03  
% 2.46/1.03  sup_time_total:                         0.
% 2.46/1.03  sup_time_generating:                    0.
% 2.46/1.03  sup_time_sim_full:                      0.
% 2.46/1.03  sup_time_sim_immed:                     0.
% 2.46/1.03  
% 2.46/1.03  sup_num_of_clauses:                     41
% 2.46/1.03  sup_num_in_active:                      35
% 2.46/1.03  sup_num_in_passive:                     6
% 2.46/1.03  sup_num_of_loops:                       39
% 2.46/1.03  sup_fw_superposition:                   28
% 2.46/1.03  sup_bw_superposition:                   11
% 2.46/1.03  sup_immediate_simplified:               20
% 2.46/1.03  sup_given_eliminated:                   0
% 2.46/1.03  comparisons_done:                       0
% 2.46/1.03  comparisons_avoided:                    0
% 2.46/1.03  
% 2.46/1.03  ------ Simplifications
% 2.46/1.03  
% 2.46/1.03  
% 2.46/1.03  sim_fw_subset_subsumed:                 3
% 2.46/1.03  sim_bw_subset_subsumed:                 0
% 2.46/1.03  sim_fw_subsumed:                        5
% 2.46/1.03  sim_bw_subsumed:                        0
% 2.46/1.03  sim_fw_subsumption_res:                 0
% 2.46/1.03  sim_bw_subsumption_res:                 0
% 2.46/1.03  sim_tautology_del:                      0
% 2.46/1.03  sim_eq_tautology_del:                   13
% 2.46/1.03  sim_eq_res_simp:                        0
% 2.46/1.03  sim_fw_demodulated:                     0
% 2.46/1.03  sim_bw_demodulated:                     4
% 2.46/1.03  sim_light_normalised:                   28
% 2.46/1.03  sim_joinable_taut:                      0
% 2.46/1.03  sim_joinable_simp:                      0
% 2.46/1.03  sim_ac_normalised:                      0
% 2.46/1.03  sim_smt_subsumption:                    0
% 2.46/1.03  
%------------------------------------------------------------------------------
