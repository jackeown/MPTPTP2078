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
% DateTime   : Thu Dec  3 12:17:44 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :  179 (1608 expanded)
%              Number of clauses        :  126 ( 575 expanded)
%              Number of leaves         :   17 ( 436 expanded)
%              Depth                    :   25
%              Number of atoms          :  769 (10263 expanded)
%              Number of equality atoms :  359 (1942 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   4 average)
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
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

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
    inference(ennf_transformation,[],[f11])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f31,plain,(
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

fof(f30,plain,(
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

fof(f29,plain,
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

fof(f32,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31,f30,f29])).

fof(f46,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f52,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

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

fof(f22,plain,(
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
    inference(flattening,[],[f22])).

fof(f44,plain,(
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
    inference(cnf_transformation,[],[f23])).

fof(f47,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f49,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f53,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f32])).

fof(f50,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f32])).

fof(f51,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
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
    inference(ennf_transformation,[],[f3])).

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
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

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

fof(f17,plain,(
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
    inference(flattening,[],[f17])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f9,axiom,(
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

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | ~ v2_funct_1(X2)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

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

fof(f15,plain,(
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
    inference(flattening,[],[f15])).

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
    inference(nnf_transformation,[],[f16])).

fof(f37,plain,(
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

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f37])).

fof(f54,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_21,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_464,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_21])).

cnf(c_865,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_464])).

cnf(c_8,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_473,plain,
    ( ~ l1_struct_0(X0_49)
    | u1_struct_0(X0_49) = k2_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_8])).

cnf(c_857,plain,
    ( u1_struct_0(X0_49) = k2_struct_0(X0_49)
    | l1_struct_0(X0_49) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_473])).

cnf(c_1216,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_865,c_857])).

cnf(c_19,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_465,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_19])).

cnf(c_864,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_465])).

cnf(c_1215,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_864,c_857])).

cnf(c_15,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_469,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1350,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1215,c_469])).

cnf(c_1416,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_1216,c_1350])).

cnf(c_10,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | v2_struct_0(X2)
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_20,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_288,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
    | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
    | sK1 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_20])).

cnf(c_289,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(unflattening,[status(thm)],[c_288])).

cnf(c_293,plain,
    ( ~ l1_struct_0(X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_289,c_19])).

cnf(c_294,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_293])).

cnf(c_461,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
    | ~ l1_struct_0(X0_49)
    | ~ v1_funct_1(X0_47)
    | ~ v2_funct_1(X0_47)
    | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_47)) = k2_struct_0(X0_49) ),
    inference(subtyping,[status(esa)],[c_294])).

cnf(c_868,plain,
    ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_47)) = k2_struct_0(X0_49)
    | v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_461])).

cnf(c_1955,plain,
    ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47)) = k2_struct_0(X0_49)
    | v1_funct_2(X0_47,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_868,c_1215])).

cnf(c_1966,plain,
    ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_2(X0_47,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1955])).

cnf(c_1990,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1966,c_1216])).

cnf(c_22,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2349,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1990,c_22])).

cnf(c_2350,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(renaming,[status(thm)],[c_2349])).

cnf(c_2361,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1416,c_2350])).

cnf(c_9,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f42])).

cnf(c_472,plain,
    ( ~ v1_funct_2(X0_47,X0_48,X1_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ v1_funct_1(X0_47)
    | ~ v2_funct_1(X0_47)
    | k2_relset_1(X0_48,X1_48,X0_47) != X1_48
    | k2_tops_2(X0_48,X1_48,X0_47) = k2_funct_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_858,plain,
    ( k2_relset_1(X0_48,X1_48,X0_47) != X1_48
    | k2_tops_2(X0_48,X1_48,X0_47) = k2_funct_1(X0_47)
    | v1_funct_2(X0_47,X0_48,X1_48) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_472])).

cnf(c_1681,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1416,c_858])).

cnf(c_18,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_25,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_14,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_28,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_17,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_467,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_862,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_467])).

cnf(c_1349,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1215,c_862])).

cnf(c_1535,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1349,c_1216])).

cnf(c_16,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_468,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_16])).

cnf(c_861,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_468])).

cnf(c_1348,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1215,c_861])).

cnf(c_1625,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1348,c_1216])).

cnf(c_2084,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1681,c_25,c_28,c_1535,c_1625])).

cnf(c_2362,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2361,c_2084])).

cnf(c_3290,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2362,c_25,c_28,c_1535,c_1625])).

cnf(c_3293,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3290,c_858])).

cnf(c_466,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_18])).

cnf(c_863,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_466])).

cnf(c_2,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f35])).

cnf(c_477,plain,
    ( ~ v1_funct_1(X0_47)
    | ~ v2_funct_1(X0_47)
    | ~ v1_relat_1(X0_47)
    | k2_funct_1(k2_funct_1(X0_47)) = X0_47 ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_853,plain,
    ( k2_funct_1(k2_funct_1(X0_47)) = X0_47
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top
    | v1_relat_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_477])).

cnf(c_1226,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_863,c_853])).

cnf(c_517,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_477])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_479,plain,
    ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
    | ~ v1_relat_1(X1_47)
    | v1_relat_1(X0_47) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_851,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
    | v1_relat_1(X1_47) != iProver_top
    | v1_relat_1(X0_47) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_479])).

cnf(c_1169,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_861,c_851])).

cnf(c_1170,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1169])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_478,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1173,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_478])).

cnf(c_1889,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1226,c_18,c_14,c_517,c_1170,c_1173])).

cnf(c_3331,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3293,c_1889])).

cnf(c_26,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_27,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_529,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_473])).

cnf(c_7,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_474,plain,
    ( ~ v1_funct_2(X0_47,X0_48,X1_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ v1_funct_1(X0_47)
    | v1_funct_1(k2_funct_1(X0_47))
    | ~ v2_funct_1(X0_47)
    | k2_relset_1(X0_48,X1_48,X0_47) != X1_48 ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1091,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_474])).

cnf(c_1092,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1091])).

cnf(c_485,plain,
    ( X0_48 != X1_48
    | X2_48 != X1_48
    | X2_48 = X0_48 ),
    theory(equality)).

cnf(c_1106,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_48
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_48 ),
    inference(instantiation,[status(thm)],[c_485])).

cnf(c_1178,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1106])).

cnf(c_5,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f40])).

cnf(c_476,plain,
    ( ~ v1_funct_2(X0_47,X0_48,X1_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | m1_subset_1(k2_funct_1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48)))
    | ~ v1_funct_1(X0_47)
    | ~ v2_funct_1(X0_47)
    | k2_relset_1(X0_48,X1_48,X0_47) != X1_48 ),
    inference(subtyping,[status(esa)],[c_5])).

cnf(c_854,plain,
    ( k2_relset_1(X0_48,X1_48,X0_47) != X1_48
    | v1_funct_2(X0_47,X0_48,X1_48) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48))) = iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_1637,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1416,c_854])).

cnf(c_6,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f39])).

cnf(c_475,plain,
    ( ~ v1_funct_2(X0_47,X0_48,X1_48)
    | v1_funct_2(k2_funct_1(X0_47),X1_48,X0_48)
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
    | ~ v1_funct_1(X0_47)
    | ~ v2_funct_1(X0_47)
    | k2_relset_1(X0_48,X1_48,X0_47) != X1_48 ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_855,plain,
    ( k2_relset_1(X0_48,X1_48,X0_47) != X1_48
    | v1_funct_2(X0_47,X0_48,X1_48) != iProver_top
    | v1_funct_2(k2_funct_1(X0_47),X1_48,X0_48) = iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_475])).

cnf(c_1672,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1416,c_855])).

cnf(c_12,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
    | ~ l1_struct_0(X1)
    | ~ l1_struct_0(X2)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_471,plain,
    ( ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49))
    | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
    | ~ l1_struct_0(X1_49)
    | ~ l1_struct_0(X0_49)
    | ~ v1_funct_1(X0_47)
    | ~ v2_funct_1(X0_47)
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_47))
    | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_47) != k2_struct_0(X1_49) ),
    inference(subtyping,[status(esa)],[c_12])).

cnf(c_859,plain,
    ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_47) != k2_struct_0(X1_49)
    | v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | l1_struct_0(X1_49) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_47)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_471])).

cnf(c_1738,plain,
    ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_47)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1215,c_859])).

cnf(c_1747,plain,
    ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_2(X0_47,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1738,c_1215])).

cnf(c_24,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2482,plain,
    ( l1_struct_0(X0_49) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_2(X0_47,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
    | k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1747,c_24])).

cnf(c_2483,plain,
    ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_2(X0_47,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(X0_49) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2482])).

cnf(c_2493,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_2(X0_47,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),X0_47)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_2483])).

cnf(c_2517,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | l1_struct_0(sK0) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2493,c_1216])).

cnf(c_2676,plain,
    ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2517,c_22])).

cnf(c_2677,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
    | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_47) != iProver_top
    | v2_funct_1(X0_47) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2676])).

cnf(c_2688,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1416,c_2677])).

cnf(c_2689,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2688,c_2084])).

cnf(c_3340,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3331,c_19,c_25,c_26,c_27,c_28,c_529,c_469,c_1092,c_1178,c_1535,c_1625,c_1637,c_1672,c_2689])).

cnf(c_3,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_13,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_236,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_13])).

cnf(c_237,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_236])).

cnf(c_463,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_237])).

cnf(c_866,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_543,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_463])).

cnf(c_492,plain,
    ( ~ v1_funct_1(X0_47)
    | v1_funct_1(X1_47)
    | X1_47 != X0_47 ),
    theory(equality)).

cnf(c_1067,plain,
    ( ~ v1_funct_1(X0_47)
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0_47 ),
    inference(instantiation,[status(thm)],[c_492])).

cnf(c_1068,plain,
    ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0_47
    | v1_funct_1(X0_47) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1067])).

cnf(c_1070,plain,
    ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != sK2
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1068])).

cnf(c_484,plain,
    ( X0_47 != X1_47
    | X2_47 != X1_47
    | X2_47 = X0_47 ),
    theory(equality)).

cnf(c_1143,plain,
    ( X0_47 != X1_47
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X1_47
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = X0_47 ),
    inference(instantiation,[status(thm)],[c_484])).

cnf(c_1273,plain,
    ( X0_47 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = X0_47
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1143])).

cnf(c_1275,plain,
    ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = sK2
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_1273])).

cnf(c_481,plain,
    ( X0_47 = X0_47 ),
    theory(equality)).

cnf(c_1274,plain,
    ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(c_2005,plain,
    ( m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_866,c_25,c_543,c_1070,c_1275,c_1274])).

cnf(c_2006,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
    inference(renaming,[status(thm)],[c_2005])).

cnf(c_2009,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2006,c_1215,c_1216])).

cnf(c_2087,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2084,c_2009])).

cnf(c_3343,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3340,c_2087])).

cnf(c_509,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_481])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_3343,c_1625,c_1535,c_509])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 09:15:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.19/0.96  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/0.96  
% 2.19/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.19/0.96  
% 2.19/0.96  ------  iProver source info
% 2.19/0.96  
% 2.19/0.96  git: date: 2020-06-30 10:37:57 +0100
% 2.19/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.19/0.96  git: non_committed_changes: false
% 2.19/0.96  git: last_make_outside_of_git: false
% 2.19/0.96  
% 2.19/0.96  ------ 
% 2.19/0.96  
% 2.19/0.96  ------ Input Options
% 2.19/0.96  
% 2.19/0.96  --out_options                           all
% 2.19/0.96  --tptp_safe_out                         true
% 2.19/0.96  --problem_path                          ""
% 2.19/0.96  --include_path                          ""
% 2.19/0.96  --clausifier                            res/vclausify_rel
% 2.19/0.96  --clausifier_options                    --mode clausify
% 2.19/0.96  --stdin                                 false
% 2.19/0.96  --stats_out                             all
% 2.19/0.96  
% 2.19/0.96  ------ General Options
% 2.19/0.96  
% 2.19/0.96  --fof                                   false
% 2.19/0.96  --time_out_real                         305.
% 2.19/0.96  --time_out_virtual                      -1.
% 2.19/0.96  --symbol_type_check                     false
% 2.19/0.96  --clausify_out                          false
% 2.19/0.96  --sig_cnt_out                           false
% 2.19/0.96  --trig_cnt_out                          false
% 2.19/0.96  --trig_cnt_out_tolerance                1.
% 2.19/0.96  --trig_cnt_out_sk_spl                   false
% 2.19/0.96  --abstr_cl_out                          false
% 2.19/0.96  
% 2.19/0.96  ------ Global Options
% 2.19/0.96  
% 2.19/0.96  --schedule                              default
% 2.19/0.96  --add_important_lit                     false
% 2.19/0.96  --prop_solver_per_cl                    1000
% 2.19/0.96  --min_unsat_core                        false
% 2.19/0.96  --soft_assumptions                      false
% 2.19/0.96  --soft_lemma_size                       3
% 2.19/0.96  --prop_impl_unit_size                   0
% 2.19/0.96  --prop_impl_unit                        []
% 2.19/0.96  --share_sel_clauses                     true
% 2.19/0.96  --reset_solvers                         false
% 2.19/0.96  --bc_imp_inh                            [conj_cone]
% 2.19/0.96  --conj_cone_tolerance                   3.
% 2.19/0.96  --extra_neg_conj                        none
% 2.19/0.96  --large_theory_mode                     true
% 2.19/0.96  --prolific_symb_bound                   200
% 2.19/0.96  --lt_threshold                          2000
% 2.19/0.96  --clause_weak_htbl                      true
% 2.19/0.96  --gc_record_bc_elim                     false
% 2.19/0.96  
% 2.19/0.96  ------ Preprocessing Options
% 2.19/0.96  
% 2.19/0.96  --preprocessing_flag                    true
% 2.19/0.96  --time_out_prep_mult                    0.1
% 2.19/0.96  --splitting_mode                        input
% 2.19/0.96  --splitting_grd                         true
% 2.19/0.96  --splitting_cvd                         false
% 2.19/0.96  --splitting_cvd_svl                     false
% 2.19/0.96  --splitting_nvd                         32
% 2.19/0.96  --sub_typing                            true
% 2.19/0.96  --prep_gs_sim                           true
% 2.19/0.96  --prep_unflatten                        true
% 2.19/0.96  --prep_res_sim                          true
% 2.19/0.96  --prep_upred                            true
% 2.19/0.96  --prep_sem_filter                       exhaustive
% 2.19/0.96  --prep_sem_filter_out                   false
% 2.19/0.96  --pred_elim                             true
% 2.19/0.96  --res_sim_input                         true
% 2.19/0.96  --eq_ax_congr_red                       true
% 2.19/0.96  --pure_diseq_elim                       true
% 2.19/0.96  --brand_transform                       false
% 2.19/0.96  --non_eq_to_eq                          false
% 2.19/0.96  --prep_def_merge                        true
% 2.19/0.96  --prep_def_merge_prop_impl              false
% 2.19/0.96  --prep_def_merge_mbd                    true
% 2.19/0.96  --prep_def_merge_tr_red                 false
% 2.19/0.96  --prep_def_merge_tr_cl                  false
% 2.19/0.96  --smt_preprocessing                     true
% 2.19/0.96  --smt_ac_axioms                         fast
% 2.19/0.96  --preprocessed_out                      false
% 2.19/0.96  --preprocessed_stats                    false
% 2.19/0.96  
% 2.19/0.96  ------ Abstraction refinement Options
% 2.19/0.96  
% 2.19/0.96  --abstr_ref                             []
% 2.19/0.96  --abstr_ref_prep                        false
% 2.19/0.96  --abstr_ref_until_sat                   false
% 2.19/0.96  --abstr_ref_sig_restrict                funpre
% 2.19/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.96  --abstr_ref_under                       []
% 2.19/0.96  
% 2.19/0.96  ------ SAT Options
% 2.19/0.96  
% 2.19/0.96  --sat_mode                              false
% 2.19/0.96  --sat_fm_restart_options                ""
% 2.19/0.96  --sat_gr_def                            false
% 2.19/0.96  --sat_epr_types                         true
% 2.19/0.96  --sat_non_cyclic_types                  false
% 2.19/0.96  --sat_finite_models                     false
% 2.19/0.96  --sat_fm_lemmas                         false
% 2.19/0.96  --sat_fm_prep                           false
% 2.19/0.96  --sat_fm_uc_incr                        true
% 2.19/0.96  --sat_out_model                         small
% 2.19/0.96  --sat_out_clauses                       false
% 2.19/0.96  
% 2.19/0.96  ------ QBF Options
% 2.19/0.96  
% 2.19/0.96  --qbf_mode                              false
% 2.19/0.96  --qbf_elim_univ                         false
% 2.19/0.96  --qbf_dom_inst                          none
% 2.19/0.96  --qbf_dom_pre_inst                      false
% 2.19/0.96  --qbf_sk_in                             false
% 2.19/0.96  --qbf_pred_elim                         true
% 2.19/0.96  --qbf_split                             512
% 2.19/0.96  
% 2.19/0.96  ------ BMC1 Options
% 2.19/0.96  
% 2.19/0.96  --bmc1_incremental                      false
% 2.19/0.96  --bmc1_axioms                           reachable_all
% 2.19/0.96  --bmc1_min_bound                        0
% 2.19/0.96  --bmc1_max_bound                        -1
% 2.19/0.96  --bmc1_max_bound_default                -1
% 2.19/0.96  --bmc1_symbol_reachability              true
% 2.19/0.96  --bmc1_property_lemmas                  false
% 2.19/0.96  --bmc1_k_induction                      false
% 2.19/0.96  --bmc1_non_equiv_states                 false
% 2.19/0.96  --bmc1_deadlock                         false
% 2.19/0.96  --bmc1_ucm                              false
% 2.19/0.96  --bmc1_add_unsat_core                   none
% 2.19/0.96  --bmc1_unsat_core_children              false
% 2.19/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.96  --bmc1_out_stat                         full
% 2.19/0.96  --bmc1_ground_init                      false
% 2.19/0.96  --bmc1_pre_inst_next_state              false
% 2.19/0.96  --bmc1_pre_inst_state                   false
% 2.19/0.96  --bmc1_pre_inst_reach_state             false
% 2.19/0.96  --bmc1_out_unsat_core                   false
% 2.19/0.96  --bmc1_aig_witness_out                  false
% 2.19/0.96  --bmc1_verbose                          false
% 2.19/0.96  --bmc1_dump_clauses_tptp                false
% 2.19/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.96  --bmc1_dump_file                        -
% 2.19/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.96  --bmc1_ucm_extend_mode                  1
% 2.19/0.96  --bmc1_ucm_init_mode                    2
% 2.19/0.96  --bmc1_ucm_cone_mode                    none
% 2.19/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.96  --bmc1_ucm_relax_model                  4
% 2.19/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.96  --bmc1_ucm_layered_model                none
% 2.19/0.96  --bmc1_ucm_max_lemma_size               10
% 2.19/0.96  
% 2.19/0.96  ------ AIG Options
% 2.19/0.96  
% 2.19/0.96  --aig_mode                              false
% 2.19/0.96  
% 2.19/0.96  ------ Instantiation Options
% 2.19/0.96  
% 2.19/0.96  --instantiation_flag                    true
% 2.19/0.96  --inst_sos_flag                         false
% 2.19/0.96  --inst_sos_phase                        true
% 2.19/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.96  --inst_lit_sel_side                     num_symb
% 2.19/0.96  --inst_solver_per_active                1400
% 2.19/0.96  --inst_solver_calls_frac                1.
% 2.19/0.96  --inst_passive_queue_type               priority_queues
% 2.19/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.96  --inst_passive_queues_freq              [25;2]
% 2.19/0.96  --inst_dismatching                      true
% 2.19/0.96  --inst_eager_unprocessed_to_passive     true
% 2.19/0.96  --inst_prop_sim_given                   true
% 2.19/0.96  --inst_prop_sim_new                     false
% 2.19/0.96  --inst_subs_new                         false
% 2.19/0.96  --inst_eq_res_simp                      false
% 2.19/0.96  --inst_subs_given                       false
% 2.19/0.96  --inst_orphan_elimination               true
% 2.19/0.96  --inst_learning_loop_flag               true
% 2.19/0.96  --inst_learning_start                   3000
% 2.19/0.96  --inst_learning_factor                  2
% 2.19/0.96  --inst_start_prop_sim_after_learn       3
% 2.19/0.96  --inst_sel_renew                        solver
% 2.19/0.96  --inst_lit_activity_flag                true
% 2.19/0.96  --inst_restr_to_given                   false
% 2.19/0.96  --inst_activity_threshold               500
% 2.19/0.96  --inst_out_proof                        true
% 2.19/0.96  
% 2.19/0.96  ------ Resolution Options
% 2.19/0.96  
% 2.19/0.96  --resolution_flag                       true
% 2.19/0.96  --res_lit_sel                           adaptive
% 2.19/0.96  --res_lit_sel_side                      none
% 2.19/0.96  --res_ordering                          kbo
% 2.19/0.96  --res_to_prop_solver                    active
% 2.19/0.96  --res_prop_simpl_new                    false
% 2.19/0.96  --res_prop_simpl_given                  true
% 2.19/0.96  --res_passive_queue_type                priority_queues
% 2.19/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.96  --res_passive_queues_freq               [15;5]
% 2.19/0.96  --res_forward_subs                      full
% 2.19/0.96  --res_backward_subs                     full
% 2.19/0.96  --res_forward_subs_resolution           true
% 2.19/0.96  --res_backward_subs_resolution          true
% 2.19/0.96  --res_orphan_elimination                true
% 2.19/0.96  --res_time_limit                        2.
% 2.19/0.96  --res_out_proof                         true
% 2.19/0.96  
% 2.19/0.96  ------ Superposition Options
% 2.19/0.96  
% 2.19/0.96  --superposition_flag                    true
% 2.19/0.96  --sup_passive_queue_type                priority_queues
% 2.19/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.96  --demod_completeness_check              fast
% 2.19/0.96  --demod_use_ground                      true
% 2.19/0.96  --sup_to_prop_solver                    passive
% 2.19/0.96  --sup_prop_simpl_new                    true
% 2.19/0.96  --sup_prop_simpl_given                  true
% 2.19/0.96  --sup_fun_splitting                     false
% 2.19/0.96  --sup_smt_interval                      50000
% 2.19/0.96  
% 2.19/0.96  ------ Superposition Simplification Setup
% 2.19/0.96  
% 2.19/0.96  --sup_indices_passive                   []
% 2.19/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.96  --sup_full_bw                           [BwDemod]
% 2.19/0.96  --sup_immed_triv                        [TrivRules]
% 2.19/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.96  --sup_immed_bw_main                     []
% 2.19/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.96  
% 2.19/0.96  ------ Combination Options
% 2.19/0.96  
% 2.19/0.96  --comb_res_mult                         3
% 2.19/0.96  --comb_sup_mult                         2
% 2.19/0.96  --comb_inst_mult                        10
% 2.19/0.96  
% 2.19/0.96  ------ Debug Options
% 2.19/0.96  
% 2.19/0.96  --dbg_backtrace                         false
% 2.19/0.96  --dbg_dump_prop_clauses                 false
% 2.19/0.96  --dbg_dump_prop_clauses_file            -
% 2.19/0.96  --dbg_out_stat                          false
% 2.19/0.96  ------ Parsing...
% 2.19/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.19/0.96  
% 2.19/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 2.19/0.96  
% 2.19/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.19/0.96  
% 2.19/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.19/0.96  ------ Proving...
% 2.19/0.96  ------ Problem Properties 
% 2.19/0.96  
% 2.19/0.96  
% 2.19/0.96  clauses                                 19
% 2.19/0.96  conjectures                             7
% 2.19/0.96  EPR                                     4
% 2.19/0.96  Horn                                    19
% 2.19/0.96  unary                                   8
% 2.19/0.96  binary                                  1
% 2.19/0.96  lits                                    67
% 2.19/0.96  lits eq                                 14
% 2.19/0.96  fd_pure                                 0
% 2.19/0.96  fd_pseudo                               0
% 2.19/0.96  fd_cond                                 0
% 2.19/0.96  fd_pseudo_cond                          0
% 2.19/0.96  AC symbols                              0
% 2.19/0.96  
% 2.19/0.96  ------ Schedule dynamic 5 is on 
% 2.19/0.96  
% 2.19/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.19/0.96  
% 2.19/0.96  
% 2.19/0.96  ------ 
% 2.19/0.96  Current options:
% 2.19/0.96  ------ 
% 2.19/0.96  
% 2.19/0.96  ------ Input Options
% 2.19/0.96  
% 2.19/0.96  --out_options                           all
% 2.19/0.96  --tptp_safe_out                         true
% 2.19/0.96  --problem_path                          ""
% 2.19/0.96  --include_path                          ""
% 2.19/0.96  --clausifier                            res/vclausify_rel
% 2.19/0.96  --clausifier_options                    --mode clausify
% 2.19/0.96  --stdin                                 false
% 2.19/0.96  --stats_out                             all
% 2.19/0.96  
% 2.19/0.96  ------ General Options
% 2.19/0.96  
% 2.19/0.96  --fof                                   false
% 2.19/0.96  --time_out_real                         305.
% 2.19/0.96  --time_out_virtual                      -1.
% 2.19/0.96  --symbol_type_check                     false
% 2.19/0.96  --clausify_out                          false
% 2.19/0.96  --sig_cnt_out                           false
% 2.19/0.96  --trig_cnt_out                          false
% 2.19/0.96  --trig_cnt_out_tolerance                1.
% 2.19/0.96  --trig_cnt_out_sk_spl                   false
% 2.19/0.96  --abstr_cl_out                          false
% 2.19/0.96  
% 2.19/0.96  ------ Global Options
% 2.19/0.96  
% 2.19/0.96  --schedule                              default
% 2.19/0.96  --add_important_lit                     false
% 2.19/0.96  --prop_solver_per_cl                    1000
% 2.19/0.96  --min_unsat_core                        false
% 2.19/0.96  --soft_assumptions                      false
% 2.19/0.96  --soft_lemma_size                       3
% 2.19/0.96  --prop_impl_unit_size                   0
% 2.19/0.96  --prop_impl_unit                        []
% 2.19/0.96  --share_sel_clauses                     true
% 2.19/0.96  --reset_solvers                         false
% 2.19/0.96  --bc_imp_inh                            [conj_cone]
% 2.19/0.96  --conj_cone_tolerance                   3.
% 2.19/0.96  --extra_neg_conj                        none
% 2.19/0.96  --large_theory_mode                     true
% 2.19/0.96  --prolific_symb_bound                   200
% 2.19/0.96  --lt_threshold                          2000
% 2.19/0.96  --clause_weak_htbl                      true
% 2.19/0.96  --gc_record_bc_elim                     false
% 2.19/0.96  
% 2.19/0.96  ------ Preprocessing Options
% 2.19/0.96  
% 2.19/0.96  --preprocessing_flag                    true
% 2.19/0.96  --time_out_prep_mult                    0.1
% 2.19/0.96  --splitting_mode                        input
% 2.19/0.96  --splitting_grd                         true
% 2.19/0.96  --splitting_cvd                         false
% 2.19/0.96  --splitting_cvd_svl                     false
% 2.19/0.96  --splitting_nvd                         32
% 2.19/0.96  --sub_typing                            true
% 2.19/0.96  --prep_gs_sim                           true
% 2.19/0.96  --prep_unflatten                        true
% 2.19/0.96  --prep_res_sim                          true
% 2.19/0.96  --prep_upred                            true
% 2.19/0.96  --prep_sem_filter                       exhaustive
% 2.19/0.96  --prep_sem_filter_out                   false
% 2.19/0.96  --pred_elim                             true
% 2.19/0.96  --res_sim_input                         true
% 2.19/0.96  --eq_ax_congr_red                       true
% 2.19/0.96  --pure_diseq_elim                       true
% 2.19/0.96  --brand_transform                       false
% 2.19/0.96  --non_eq_to_eq                          false
% 2.19/0.96  --prep_def_merge                        true
% 2.19/0.96  --prep_def_merge_prop_impl              false
% 2.19/0.96  --prep_def_merge_mbd                    true
% 2.19/0.96  --prep_def_merge_tr_red                 false
% 2.19/0.96  --prep_def_merge_tr_cl                  false
% 2.19/0.96  --smt_preprocessing                     true
% 2.19/0.96  --smt_ac_axioms                         fast
% 2.19/0.96  --preprocessed_out                      false
% 2.19/0.96  --preprocessed_stats                    false
% 2.19/0.96  
% 2.19/0.96  ------ Abstraction refinement Options
% 2.19/0.96  
% 2.19/0.96  --abstr_ref                             []
% 2.19/0.96  --abstr_ref_prep                        false
% 2.19/0.96  --abstr_ref_until_sat                   false
% 2.19/0.96  --abstr_ref_sig_restrict                funpre
% 2.19/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 2.19/0.96  --abstr_ref_under                       []
% 2.19/0.96  
% 2.19/0.96  ------ SAT Options
% 2.19/0.96  
% 2.19/0.96  --sat_mode                              false
% 2.19/0.96  --sat_fm_restart_options                ""
% 2.19/0.96  --sat_gr_def                            false
% 2.19/0.96  --sat_epr_types                         true
% 2.19/0.96  --sat_non_cyclic_types                  false
% 2.19/0.96  --sat_finite_models                     false
% 2.19/0.96  --sat_fm_lemmas                         false
% 2.19/0.96  --sat_fm_prep                           false
% 2.19/0.96  --sat_fm_uc_incr                        true
% 2.19/0.96  --sat_out_model                         small
% 2.19/0.96  --sat_out_clauses                       false
% 2.19/0.96  
% 2.19/0.96  ------ QBF Options
% 2.19/0.96  
% 2.19/0.96  --qbf_mode                              false
% 2.19/0.96  --qbf_elim_univ                         false
% 2.19/0.96  --qbf_dom_inst                          none
% 2.19/0.96  --qbf_dom_pre_inst                      false
% 2.19/0.96  --qbf_sk_in                             false
% 2.19/0.96  --qbf_pred_elim                         true
% 2.19/0.96  --qbf_split                             512
% 2.19/0.96  
% 2.19/0.96  ------ BMC1 Options
% 2.19/0.96  
% 2.19/0.96  --bmc1_incremental                      false
% 2.19/0.96  --bmc1_axioms                           reachable_all
% 2.19/0.96  --bmc1_min_bound                        0
% 2.19/0.96  --bmc1_max_bound                        -1
% 2.19/0.96  --bmc1_max_bound_default                -1
% 2.19/0.96  --bmc1_symbol_reachability              true
% 2.19/0.96  --bmc1_property_lemmas                  false
% 2.19/0.96  --bmc1_k_induction                      false
% 2.19/0.96  --bmc1_non_equiv_states                 false
% 2.19/0.96  --bmc1_deadlock                         false
% 2.19/0.96  --bmc1_ucm                              false
% 2.19/0.96  --bmc1_add_unsat_core                   none
% 2.19/0.96  --bmc1_unsat_core_children              false
% 2.19/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 2.19/0.96  --bmc1_out_stat                         full
% 2.19/0.96  --bmc1_ground_init                      false
% 2.19/0.96  --bmc1_pre_inst_next_state              false
% 2.19/0.96  --bmc1_pre_inst_state                   false
% 2.19/0.96  --bmc1_pre_inst_reach_state             false
% 2.19/0.96  --bmc1_out_unsat_core                   false
% 2.19/0.96  --bmc1_aig_witness_out                  false
% 2.19/0.96  --bmc1_verbose                          false
% 2.19/0.96  --bmc1_dump_clauses_tptp                false
% 2.19/0.96  --bmc1_dump_unsat_core_tptp             false
% 2.19/0.96  --bmc1_dump_file                        -
% 2.19/0.96  --bmc1_ucm_expand_uc_limit              128
% 2.19/0.96  --bmc1_ucm_n_expand_iterations          6
% 2.19/0.96  --bmc1_ucm_extend_mode                  1
% 2.19/0.96  --bmc1_ucm_init_mode                    2
% 2.19/0.96  --bmc1_ucm_cone_mode                    none
% 2.19/0.96  --bmc1_ucm_reduced_relation_type        0
% 2.19/0.96  --bmc1_ucm_relax_model                  4
% 2.19/0.96  --bmc1_ucm_full_tr_after_sat            true
% 2.19/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 2.19/0.96  --bmc1_ucm_layered_model                none
% 2.19/0.96  --bmc1_ucm_max_lemma_size               10
% 2.19/0.96  
% 2.19/0.96  ------ AIG Options
% 2.19/0.96  
% 2.19/0.96  --aig_mode                              false
% 2.19/0.96  
% 2.19/0.96  ------ Instantiation Options
% 2.19/0.96  
% 2.19/0.96  --instantiation_flag                    true
% 2.19/0.96  --inst_sos_flag                         false
% 2.19/0.96  --inst_sos_phase                        true
% 2.19/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.19/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.19/0.96  --inst_lit_sel_side                     none
% 2.19/0.96  --inst_solver_per_active                1400
% 2.19/0.96  --inst_solver_calls_frac                1.
% 2.19/0.96  --inst_passive_queue_type               priority_queues
% 2.19/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.19/0.96  --inst_passive_queues_freq              [25;2]
% 2.19/0.96  --inst_dismatching                      true
% 2.19/0.96  --inst_eager_unprocessed_to_passive     true
% 2.19/0.96  --inst_prop_sim_given                   true
% 2.19/0.96  --inst_prop_sim_new                     false
% 2.19/0.96  --inst_subs_new                         false
% 2.19/0.96  --inst_eq_res_simp                      false
% 2.19/0.96  --inst_subs_given                       false
% 2.19/0.96  --inst_orphan_elimination               true
% 2.19/0.96  --inst_learning_loop_flag               true
% 2.19/0.96  --inst_learning_start                   3000
% 2.19/0.96  --inst_learning_factor                  2
% 2.19/0.96  --inst_start_prop_sim_after_learn       3
% 2.19/0.96  --inst_sel_renew                        solver
% 2.19/0.96  --inst_lit_activity_flag                true
% 2.19/0.96  --inst_restr_to_given                   false
% 2.19/0.96  --inst_activity_threshold               500
% 2.19/0.96  --inst_out_proof                        true
% 2.19/0.96  
% 2.19/0.96  ------ Resolution Options
% 2.19/0.96  
% 2.19/0.96  --resolution_flag                       false
% 2.19/0.96  --res_lit_sel                           adaptive
% 2.19/0.96  --res_lit_sel_side                      none
% 2.19/0.96  --res_ordering                          kbo
% 2.19/0.96  --res_to_prop_solver                    active
% 2.19/0.96  --res_prop_simpl_new                    false
% 2.19/0.96  --res_prop_simpl_given                  true
% 2.19/0.96  --res_passive_queue_type                priority_queues
% 2.19/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.19/0.96  --res_passive_queues_freq               [15;5]
% 2.19/0.96  --res_forward_subs                      full
% 2.19/0.96  --res_backward_subs                     full
% 2.19/0.96  --res_forward_subs_resolution           true
% 2.19/0.96  --res_backward_subs_resolution          true
% 2.19/0.96  --res_orphan_elimination                true
% 2.19/0.96  --res_time_limit                        2.
% 2.19/0.96  --res_out_proof                         true
% 2.19/0.96  
% 2.19/0.96  ------ Superposition Options
% 2.19/0.96  
% 2.19/0.96  --superposition_flag                    true
% 2.19/0.96  --sup_passive_queue_type                priority_queues
% 2.19/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.19/0.96  --sup_passive_queues_freq               [8;1;4]
% 2.19/0.96  --demod_completeness_check              fast
% 2.19/0.96  --demod_use_ground                      true
% 2.19/0.96  --sup_to_prop_solver                    passive
% 2.19/0.96  --sup_prop_simpl_new                    true
% 2.19/0.96  --sup_prop_simpl_given                  true
% 2.19/0.96  --sup_fun_splitting                     false
% 2.19/0.96  --sup_smt_interval                      50000
% 2.19/0.96  
% 2.19/0.96  ------ Superposition Simplification Setup
% 2.19/0.96  
% 2.19/0.96  --sup_indices_passive                   []
% 2.19/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.19/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 2.19/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.96  --sup_full_bw                           [BwDemod]
% 2.19/0.96  --sup_immed_triv                        [TrivRules]
% 2.19/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.19/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.96  --sup_immed_bw_main                     []
% 2.19/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 2.19/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.19/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.19/0.96  
% 2.19/0.96  ------ Combination Options
% 2.19/0.96  
% 2.19/0.96  --comb_res_mult                         3
% 2.19/0.96  --comb_sup_mult                         2
% 2.19/0.96  --comb_inst_mult                        10
% 2.19/0.96  
% 2.19/0.96  ------ Debug Options
% 2.19/0.96  
% 2.19/0.96  --dbg_backtrace                         false
% 2.19/0.96  --dbg_dump_prop_clauses                 false
% 2.19/0.96  --dbg_dump_prop_clauses_file            -
% 2.19/0.96  --dbg_out_stat                          false
% 2.19/0.96  
% 2.19/0.96  
% 2.19/0.96  
% 2.19/0.96  
% 2.19/0.96  ------ Proving...
% 2.19/0.96  
% 2.19/0.96  
% 2.19/0.96  % SZS status Theorem for theBenchmark.p
% 2.19/0.96  
% 2.19/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 2.19/0.96  
% 2.19/0.96  fof(f10,conjecture,(
% 2.19/0.96    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.19/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.96  
% 2.19/0.96  fof(f11,negated_conjecture,(
% 2.19/0.96    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 2.19/0.96    inference(negated_conjecture,[],[f10])).
% 2.19/0.96  
% 2.19/0.96  fof(f26,plain,(
% 2.19/0.96    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.19/0.96    inference(ennf_transformation,[],[f11])).
% 2.19/0.96  
% 2.19/0.96  fof(f27,plain,(
% 2.19/0.96    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.19/0.96    inference(flattening,[],[f26])).
% 2.19/0.96  
% 2.19/0.96  fof(f31,plain,(
% 2.19/0.96    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.19/0.96    introduced(choice_axiom,[])).
% 2.19/0.96  
% 2.19/0.96  fof(f30,plain,(
% 2.19/0.96    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.19/0.96    introduced(choice_axiom,[])).
% 2.19/0.96  
% 2.19/0.96  fof(f29,plain,(
% 2.19/0.96    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.19/0.96    introduced(choice_axiom,[])).
% 2.19/0.96  
% 2.19/0.96  fof(f32,plain,(
% 2.19/0.96    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.19/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f27,f31,f30,f29])).
% 2.19/0.96  
% 2.19/0.96  fof(f46,plain,(
% 2.19/0.96    l1_struct_0(sK0)),
% 2.19/0.96    inference(cnf_transformation,[],[f32])).
% 2.19/0.96  
% 2.19/0.96  fof(f6,axiom,(
% 2.19/0.96    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.19/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.96  
% 2.19/0.96  fof(f19,plain,(
% 2.19/0.96    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.19/0.96    inference(ennf_transformation,[],[f6])).
% 2.19/0.96  
% 2.19/0.96  fof(f41,plain,(
% 2.19/0.96    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.19/0.96    inference(cnf_transformation,[],[f19])).
% 2.19/0.96  
% 2.19/0.96  fof(f48,plain,(
% 2.19/0.96    l1_struct_0(sK1)),
% 2.19/0.96    inference(cnf_transformation,[],[f32])).
% 2.19/0.96  
% 2.19/0.96  fof(f52,plain,(
% 2.19/0.96    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.19/0.96    inference(cnf_transformation,[],[f32])).
% 2.19/0.96  
% 2.19/0.96  fof(f8,axiom,(
% 2.19/0.96    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 2.19/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.96  
% 2.19/0.96  fof(f22,plain,(
% 2.19/0.96    ! [X0] : (! [X1] : (! [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 2.19/0.96    inference(ennf_transformation,[],[f8])).
% 2.19/0.96  
% 2.19/0.96  fof(f23,plain,(
% 2.19/0.96    ! [X0] : (! [X1] : (! [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.19/0.96    inference(flattening,[],[f22])).
% 2.19/0.96  
% 2.19/0.96  fof(f44,plain,(
% 2.19/0.96    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.19/0.96    inference(cnf_transformation,[],[f23])).
% 2.19/0.96  
% 2.19/0.96  fof(f47,plain,(
% 2.19/0.96    ~v2_struct_0(sK1)),
% 2.19/0.96    inference(cnf_transformation,[],[f32])).
% 2.19/0.96  
% 2.19/0.96  fof(f7,axiom,(
% 2.19/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.19/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.96  
% 2.19/0.96  fof(f20,plain,(
% 2.19/0.96    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.19/0.96    inference(ennf_transformation,[],[f7])).
% 2.19/0.96  
% 2.19/0.96  fof(f21,plain,(
% 2.19/0.96    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.19/0.96    inference(flattening,[],[f20])).
% 2.19/0.96  
% 2.19/0.96  fof(f42,plain,(
% 2.19/0.96    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/0.96    inference(cnf_transformation,[],[f21])).
% 2.19/0.96  
% 2.19/0.96  fof(f49,plain,(
% 2.19/0.96    v1_funct_1(sK2)),
% 2.19/0.96    inference(cnf_transformation,[],[f32])).
% 2.19/0.96  
% 2.19/0.96  fof(f53,plain,(
% 2.19/0.96    v2_funct_1(sK2)),
% 2.19/0.96    inference(cnf_transformation,[],[f32])).
% 2.19/0.96  
% 2.19/0.96  fof(f50,plain,(
% 2.19/0.96    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.19/0.96    inference(cnf_transformation,[],[f32])).
% 2.19/0.96  
% 2.19/0.96  fof(f51,plain,(
% 2.19/0.96    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.19/0.96    inference(cnf_transformation,[],[f32])).
% 2.19/0.96  
% 2.19/0.96  fof(f3,axiom,(
% 2.19/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.19/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.96  
% 2.19/0.96  fof(f13,plain,(
% 2.19/0.96    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.19/0.96    inference(ennf_transformation,[],[f3])).
% 2.19/0.96  
% 2.19/0.96  fof(f14,plain,(
% 2.19/0.96    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.19/0.96    inference(flattening,[],[f13])).
% 2.19/0.96  
% 2.19/0.96  fof(f35,plain,(
% 2.19/0.96    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.19/0.96    inference(cnf_transformation,[],[f14])).
% 2.19/0.96  
% 2.19/0.96  fof(f1,axiom,(
% 2.19/0.96    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.19/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.96  
% 2.19/0.96  fof(f12,plain,(
% 2.19/0.96    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.19/0.96    inference(ennf_transformation,[],[f1])).
% 2.19/0.96  
% 2.19/0.96  fof(f33,plain,(
% 2.19/0.96    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.19/0.96    inference(cnf_transformation,[],[f12])).
% 2.19/0.96  
% 2.19/0.96  fof(f2,axiom,(
% 2.19/0.96    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.19/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.96  
% 2.19/0.96  fof(f34,plain,(
% 2.19/0.96    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.19/0.96    inference(cnf_transformation,[],[f2])).
% 2.19/0.96  
% 2.19/0.96  fof(f5,axiom,(
% 2.19/0.96    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.19/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.96  
% 2.19/0.96  fof(f17,plain,(
% 2.19/0.96    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.19/0.96    inference(ennf_transformation,[],[f5])).
% 2.19/0.96  
% 2.19/0.96  fof(f18,plain,(
% 2.19/0.96    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.19/0.96    inference(flattening,[],[f17])).
% 2.19/0.96  
% 2.19/0.96  fof(f38,plain,(
% 2.19/0.96    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/0.96    inference(cnf_transformation,[],[f18])).
% 2.19/0.96  
% 2.19/0.96  fof(f40,plain,(
% 2.19/0.96    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/0.96    inference(cnf_transformation,[],[f18])).
% 2.19/0.96  
% 2.19/0.96  fof(f39,plain,(
% 2.19/0.96    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/0.96    inference(cnf_transformation,[],[f18])).
% 2.19/0.96  
% 2.19/0.96  fof(f9,axiom,(
% 2.19/0.96    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 2.19/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.96  
% 2.19/0.96  fof(f24,plain,(
% 2.19/0.96    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.19/0.96    inference(ennf_transformation,[],[f9])).
% 2.19/0.96  
% 2.19/0.96  fof(f25,plain,(
% 2.19/0.96    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 2.19/0.96    inference(flattening,[],[f24])).
% 2.19/0.96  
% 2.19/0.96  fof(f45,plain,(
% 2.19/0.96    ( ! [X2,X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 2.19/0.96    inference(cnf_transformation,[],[f25])).
% 2.19/0.96  
% 2.19/0.96  fof(f4,axiom,(
% 2.19/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 2.19/0.96    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.19/0.96  
% 2.19/0.96  fof(f15,plain,(
% 2.19/0.96    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.19/0.96    inference(ennf_transformation,[],[f4])).
% 2.19/0.96  
% 2.19/0.96  fof(f16,plain,(
% 2.19/0.96    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.19/0.96    inference(flattening,[],[f15])).
% 2.19/0.96  
% 2.19/0.96  fof(f28,plain,(
% 2.19/0.96    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.19/0.96    inference(nnf_transformation,[],[f16])).
% 2.19/0.96  
% 2.19/0.96  fof(f37,plain,(
% 2.19/0.96    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.19/0.96    inference(cnf_transformation,[],[f28])).
% 2.19/0.96  
% 2.19/0.96  fof(f55,plain,(
% 2.19/0.96    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 2.19/0.96    inference(equality_resolution,[],[f37])).
% 2.19/0.96  
% 2.19/0.96  fof(f54,plain,(
% 2.19/0.96    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 2.19/0.96    inference(cnf_transformation,[],[f32])).
% 2.19/0.96  
% 2.19/0.96  cnf(c_21,negated_conjecture,
% 2.19/0.96      ( l1_struct_0(sK0) ),
% 2.19/0.96      inference(cnf_transformation,[],[f46]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_464,negated_conjecture,
% 2.19/0.96      ( l1_struct_0(sK0) ),
% 2.19/0.96      inference(subtyping,[status(esa)],[c_21]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_865,plain,
% 2.19/0.96      ( l1_struct_0(sK0) = iProver_top ),
% 2.19/0.96      inference(predicate_to_equality,[status(thm)],[c_464]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_8,plain,
% 2.19/0.96      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.19/0.96      inference(cnf_transformation,[],[f41]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_473,plain,
% 2.19/0.96      ( ~ l1_struct_0(X0_49) | u1_struct_0(X0_49) = k2_struct_0(X0_49) ),
% 2.19/0.96      inference(subtyping,[status(esa)],[c_8]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_857,plain,
% 2.19/0.96      ( u1_struct_0(X0_49) = k2_struct_0(X0_49)
% 2.19/0.96      | l1_struct_0(X0_49) != iProver_top ),
% 2.19/0.96      inference(predicate_to_equality,[status(thm)],[c_473]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_1216,plain,
% 2.19/0.96      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.19/0.96      inference(superposition,[status(thm)],[c_865,c_857]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_19,negated_conjecture,
% 2.19/0.96      ( l1_struct_0(sK1) ),
% 2.19/0.96      inference(cnf_transformation,[],[f48]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_465,negated_conjecture,
% 2.19/0.96      ( l1_struct_0(sK1) ),
% 2.19/0.96      inference(subtyping,[status(esa)],[c_19]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_864,plain,
% 2.19/0.96      ( l1_struct_0(sK1) = iProver_top ),
% 2.19/0.96      inference(predicate_to_equality,[status(thm)],[c_465]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_1215,plain,
% 2.19/0.96      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.19/0.96      inference(superposition,[status(thm)],[c_864,c_857]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_15,negated_conjecture,
% 2.19/0.96      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.19/0.96      inference(cnf_transformation,[],[f52]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_469,negated_conjecture,
% 2.19/0.96      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.19/0.96      inference(subtyping,[status(esa)],[c_15]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_1350,plain,
% 2.19/0.96      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.19/0.96      inference(demodulation,[status(thm)],[c_1215,c_469]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_1416,plain,
% 2.19/0.96      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.19/0.96      inference(demodulation,[status(thm)],[c_1216,c_1350]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_10,plain,
% 2.19/0.96      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.19/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.19/0.96      | v2_struct_0(X2)
% 2.19/0.96      | ~ l1_struct_0(X1)
% 2.19/0.96      | ~ l1_struct_0(X2)
% 2.19/0.96      | ~ v1_funct_1(X0)
% 2.19/0.96      | ~ v2_funct_1(X0)
% 2.19/0.96      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.19/0.96      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 2.19/0.96      inference(cnf_transformation,[],[f44]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_20,negated_conjecture,
% 2.19/0.96      ( ~ v2_struct_0(sK1) ),
% 2.19/0.96      inference(cnf_transformation,[],[f47]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_288,plain,
% 2.19/0.96      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.19/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.19/0.96      | ~ l1_struct_0(X1)
% 2.19/0.96      | ~ l1_struct_0(X2)
% 2.19/0.96      | ~ v1_funct_1(X0)
% 2.19/0.96      | ~ v2_funct_1(X0)
% 2.19/0.96      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 2.19/0.96      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 2.19/0.96      | sK1 != X2 ),
% 2.19/0.96      inference(resolution_lifted,[status(thm)],[c_10,c_20]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_289,plain,
% 2.19/0.96      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.19/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.19/0.96      | ~ l1_struct_0(X1)
% 2.19/0.96      | ~ l1_struct_0(sK1)
% 2.19/0.96      | ~ v1_funct_1(X0)
% 2.19/0.96      | ~ v2_funct_1(X0)
% 2.19/0.96      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.19/0.96      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.19/0.96      inference(unflattening,[status(thm)],[c_288]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_293,plain,
% 2.19/0.96      ( ~ l1_struct_0(X1)
% 2.19/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.19/0.96      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.19/0.96      | ~ v1_funct_1(X0)
% 2.19/0.96      | ~ v2_funct_1(X0)
% 2.19/0.96      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.19/0.96      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.19/0.96      inference(global_propositional_subsumption,
% 2.19/0.96                [status(thm)],
% 2.19/0.96                [c_289,c_19]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_294,plain,
% 2.19/0.96      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 2.19/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 2.19/0.96      | ~ l1_struct_0(X1)
% 2.19/0.96      | ~ v1_funct_1(X0)
% 2.19/0.96      | ~ v2_funct_1(X0)
% 2.19/0.96      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 2.19/0.96      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 2.19/0.96      inference(renaming,[status(thm)],[c_293]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_461,plain,
% 2.19/0.96      ( ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(sK1))
% 2.19/0.96      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1))))
% 2.19/0.96      | ~ l1_struct_0(X0_49)
% 2.19/0.96      | ~ v1_funct_1(X0_47)
% 2.19/0.96      | ~ v2_funct_1(X0_47)
% 2.19/0.96      | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.96      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_47)) = k2_struct_0(X0_49) ),
% 2.19/0.96      inference(subtyping,[status(esa)],[c_294]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_868,plain,
% 2.19/0.96      ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.96      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_47)) = k2_struct_0(X0_49)
% 2.19/0.96      | v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(sK1)) != iProver_top
% 2.19/0.96      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1)))) != iProver_top
% 2.19/0.96      | l1_struct_0(X0_49) != iProver_top
% 2.19/0.96      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.96      | v2_funct_1(X0_47) != iProver_top ),
% 2.19/0.96      inference(predicate_to_equality,[status(thm)],[c_461]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_1955,plain,
% 2.19/0.96      ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.96      | k2_relset_1(k2_struct_0(sK1),u1_struct_0(X0_49),k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47)) = k2_struct_0(X0_49)
% 2.19/0.96      | v1_funct_2(X0_47,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
% 2.19/0.96      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.96      | l1_struct_0(X0_49) != iProver_top
% 2.19/0.96      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.96      | v2_funct_1(X0_47) != iProver_top ),
% 2.19/0.96      inference(light_normalisation,[status(thm)],[c_868,c_1215]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_1966,plain,
% 2.19/0.96      ( k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
% 2.19/0.96      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.96      | v1_funct_2(X0_47,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.96      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.96      | l1_struct_0(sK0) != iProver_top
% 2.19/0.96      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.96      | v2_funct_1(X0_47) != iProver_top ),
% 2.19/0.96      inference(superposition,[status(thm)],[c_1216,c_1955]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_1990,plain,
% 2.19/0.96      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
% 2.19/0.96      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.96      | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.96      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.96      | l1_struct_0(sK0) != iProver_top
% 2.19/0.96      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.96      | v2_funct_1(X0_47) != iProver_top ),
% 2.19/0.96      inference(light_normalisation,[status(thm)],[c_1966,c_1216]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_22,plain,
% 2.19/0.96      ( l1_struct_0(sK0) = iProver_top ),
% 2.19/0.96      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_2349,plain,
% 2.19/0.96      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.96      | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.96      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.96      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
% 2.19/0.96      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.96      | v2_funct_1(X0_47) != iProver_top ),
% 2.19/0.96      inference(global_propositional_subsumption,
% 2.19/0.96                [status(thm)],
% 2.19/0.96                [c_1990,c_22]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_2350,plain,
% 2.19/0.96      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = k2_struct_0(sK0)
% 2.19/0.96      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.96      | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.96      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.96      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.96      | v2_funct_1(X0_47) != iProver_top ),
% 2.19/0.96      inference(renaming,[status(thm)],[c_2349]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_2361,plain,
% 2.19/0.96      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 2.19/0.96      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.96      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.96      | v1_funct_1(sK2) != iProver_top
% 2.19/0.96      | v2_funct_1(sK2) != iProver_top ),
% 2.19/0.96      inference(superposition,[status(thm)],[c_1416,c_2350]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_9,plain,
% 2.19/0.96      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/0.96      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.96      | ~ v1_funct_1(X0)
% 2.19/0.96      | ~ v2_funct_1(X0)
% 2.19/0.96      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.19/0.96      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.19/0.96      inference(cnf_transformation,[],[f42]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_472,plain,
% 2.19/0.96      ( ~ v1_funct_2(X0_47,X0_48,X1_48)
% 2.19/0.96      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.19/0.96      | ~ v1_funct_1(X0_47)
% 2.19/0.96      | ~ v2_funct_1(X0_47)
% 2.19/0.96      | k2_relset_1(X0_48,X1_48,X0_47) != X1_48
% 2.19/0.96      | k2_tops_2(X0_48,X1_48,X0_47) = k2_funct_1(X0_47) ),
% 2.19/0.96      inference(subtyping,[status(esa)],[c_9]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_858,plain,
% 2.19/0.96      ( k2_relset_1(X0_48,X1_48,X0_47) != X1_48
% 2.19/0.96      | k2_tops_2(X0_48,X1_48,X0_47) = k2_funct_1(X0_47)
% 2.19/0.96      | v1_funct_2(X0_47,X0_48,X1_48) != iProver_top
% 2.19/0.96      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.19/0.96      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.96      | v2_funct_1(X0_47) != iProver_top ),
% 2.19/0.96      inference(predicate_to_equality,[status(thm)],[c_472]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_1681,plain,
% 2.19/0.96      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.19/0.96      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.96      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.96      | v1_funct_1(sK2) != iProver_top
% 2.19/0.96      | v2_funct_1(sK2) != iProver_top ),
% 2.19/0.96      inference(superposition,[status(thm)],[c_1416,c_858]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_18,negated_conjecture,
% 2.19/0.96      ( v1_funct_1(sK2) ),
% 2.19/0.96      inference(cnf_transformation,[],[f49]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_25,plain,
% 2.19/0.96      ( v1_funct_1(sK2) = iProver_top ),
% 2.19/0.96      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_14,negated_conjecture,
% 2.19/0.96      ( v2_funct_1(sK2) ),
% 2.19/0.96      inference(cnf_transformation,[],[f53]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_28,plain,
% 2.19/0.96      ( v2_funct_1(sK2) = iProver_top ),
% 2.19/0.96      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_17,negated_conjecture,
% 2.19/0.96      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.19/0.96      inference(cnf_transformation,[],[f50]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_467,negated_conjecture,
% 2.19/0.96      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.19/0.96      inference(subtyping,[status(esa)],[c_17]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_862,plain,
% 2.19/0.96      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.19/0.96      inference(predicate_to_equality,[status(thm)],[c_467]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_1349,plain,
% 2.19/0.96      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.19/0.96      inference(demodulation,[status(thm)],[c_1215,c_862]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_1535,plain,
% 2.19/0.96      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 2.19/0.96      inference(light_normalisation,[status(thm)],[c_1349,c_1216]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_16,negated_conjecture,
% 2.19/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.19/0.96      inference(cnf_transformation,[],[f51]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_468,negated_conjecture,
% 2.19/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.19/0.96      inference(subtyping,[status(esa)],[c_16]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_861,plain,
% 2.19/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.19/0.96      inference(predicate_to_equality,[status(thm)],[c_468]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_1348,plain,
% 2.19/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.19/0.96      inference(demodulation,[status(thm)],[c_1215,c_861]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_1625,plain,
% 2.19/0.96      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.19/0.96      inference(light_normalisation,[status(thm)],[c_1348,c_1216]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_2084,plain,
% 2.19/0.96      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.19/0.96      inference(global_propositional_subsumption,
% 2.19/0.96                [status(thm)],
% 2.19/0.96                [c_1681,c_25,c_28,c_1535,c_1625]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_2362,plain,
% 2.19/0.96      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0)
% 2.19/0.96      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.96      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.96      | v1_funct_1(sK2) != iProver_top
% 2.19/0.96      | v2_funct_1(sK2) != iProver_top ),
% 2.19/0.96      inference(light_normalisation,[status(thm)],[c_2361,c_2084]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_3290,plain,
% 2.19/0.96      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 2.19/0.96      inference(global_propositional_subsumption,
% 2.19/0.96                [status(thm)],
% 2.19/0.96                [c_2362,c_25,c_28,c_1535,c_1625]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_3293,plain,
% 2.19/0.96      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 2.19/0.96      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.19/0.96      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.19/0.96      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.19/0.96      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.19/0.96      inference(superposition,[status(thm)],[c_3290,c_858]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_466,negated_conjecture,
% 2.19/0.96      ( v1_funct_1(sK2) ),
% 2.19/0.96      inference(subtyping,[status(esa)],[c_18]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_863,plain,
% 2.19/0.96      ( v1_funct_1(sK2) = iProver_top ),
% 2.19/0.96      inference(predicate_to_equality,[status(thm)],[c_466]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_2,plain,
% 2.19/0.96      ( ~ v1_funct_1(X0)
% 2.19/0.96      | ~ v2_funct_1(X0)
% 2.19/0.96      | ~ v1_relat_1(X0)
% 2.19/0.96      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 2.19/0.96      inference(cnf_transformation,[],[f35]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_477,plain,
% 2.19/0.96      ( ~ v1_funct_1(X0_47)
% 2.19/0.96      | ~ v2_funct_1(X0_47)
% 2.19/0.96      | ~ v1_relat_1(X0_47)
% 2.19/0.96      | k2_funct_1(k2_funct_1(X0_47)) = X0_47 ),
% 2.19/0.96      inference(subtyping,[status(esa)],[c_2]) ).
% 2.19/0.96  
% 2.19/0.96  cnf(c_853,plain,
% 2.19/0.96      ( k2_funct_1(k2_funct_1(X0_47)) = X0_47
% 2.19/0.96      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.96      | v2_funct_1(X0_47) != iProver_top
% 2.19/0.96      | v1_relat_1(X0_47) != iProver_top ),
% 2.19/0.96      inference(predicate_to_equality,[status(thm)],[c_477]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1226,plain,
% 2.19/0.97      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 2.19/0.97      | v2_funct_1(sK2) != iProver_top
% 2.19/0.97      | v1_relat_1(sK2) != iProver_top ),
% 2.19/0.97      inference(superposition,[status(thm)],[c_863,c_853]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_517,plain,
% 2.19/0.97      ( ~ v1_funct_1(sK2)
% 2.19/0.97      | ~ v2_funct_1(sK2)
% 2.19/0.97      | ~ v1_relat_1(sK2)
% 2.19/0.97      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_477]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_0,plain,
% 2.19/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.19/0.97      | ~ v1_relat_1(X1)
% 2.19/0.97      | v1_relat_1(X0) ),
% 2.19/0.97      inference(cnf_transformation,[],[f33]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_479,plain,
% 2.19/0.97      ( ~ m1_subset_1(X0_47,k1_zfmisc_1(X1_47))
% 2.19/0.97      | ~ v1_relat_1(X1_47)
% 2.19/0.97      | v1_relat_1(X0_47) ),
% 2.19/0.97      inference(subtyping,[status(esa)],[c_0]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_851,plain,
% 2.19/0.97      ( m1_subset_1(X0_47,k1_zfmisc_1(X1_47)) != iProver_top
% 2.19/0.97      | v1_relat_1(X1_47) != iProver_top
% 2.19/0.97      | v1_relat_1(X0_47) = iProver_top ),
% 2.19/0.97      inference(predicate_to_equality,[status(thm)],[c_479]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1169,plain,
% 2.19/0.97      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.19/0.97      | v1_relat_1(sK2) = iProver_top ),
% 2.19/0.97      inference(superposition,[status(thm)],[c_861,c_851]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1170,plain,
% 2.19/0.97      ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.19/0.97      | v1_relat_1(sK2) ),
% 2.19/0.97      inference(predicate_to_equality_rev,[status(thm)],[c_1169]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1,plain,
% 2.19/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.19/0.97      inference(cnf_transformation,[],[f34]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_478,plain,
% 2.19/0.97      ( v1_relat_1(k2_zfmisc_1(X0_48,X1_48)) ),
% 2.19/0.97      inference(subtyping,[status(esa)],[c_1]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1173,plain,
% 2.19/0.97      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_478]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1889,plain,
% 2.19/0.97      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 2.19/0.97      inference(global_propositional_subsumption,
% 2.19/0.97                [status(thm)],
% 2.19/0.97                [c_1226,c_18,c_14,c_517,c_1170,c_1173]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_3331,plain,
% 2.19/0.97      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 2.19/0.97      | v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) != iProver_top
% 2.19/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) != iProver_top
% 2.19/0.97      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 2.19/0.97      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 2.19/0.97      inference(light_normalisation,[status(thm)],[c_3293,c_1889]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_26,plain,
% 2.19/0.97      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 2.19/0.97      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_27,plain,
% 2.19/0.97      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.19/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_529,plain,
% 2.19/0.97      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_473]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_7,plain,
% 2.19/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.97      | ~ v1_funct_1(X0)
% 2.19/0.97      | v1_funct_1(k2_funct_1(X0))
% 2.19/0.97      | ~ v2_funct_1(X0)
% 2.19/0.97      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.19/0.97      inference(cnf_transformation,[],[f38]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_474,plain,
% 2.19/0.97      ( ~ v1_funct_2(X0_47,X0_48,X1_48)
% 2.19/0.97      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.19/0.97      | ~ v1_funct_1(X0_47)
% 2.19/0.97      | v1_funct_1(k2_funct_1(X0_47))
% 2.19/0.97      | ~ v2_funct_1(X0_47)
% 2.19/0.97      | k2_relset_1(X0_48,X1_48,X0_47) != X1_48 ),
% 2.19/0.97      inference(subtyping,[status(esa)],[c_7]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1091,plain,
% 2.19/0.97      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 2.19/0.97      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.19/0.97      | v1_funct_1(k2_funct_1(sK2))
% 2.19/0.97      | ~ v1_funct_1(sK2)
% 2.19/0.97      | ~ v2_funct_1(sK2)
% 2.19/0.97      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_474]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1092,plain,
% 2.19/0.97      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 2.19/0.97      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.19/0.97      | v1_funct_1(sK2) != iProver_top
% 2.19/0.97      | v2_funct_1(sK2) != iProver_top ),
% 2.19/0.97      inference(predicate_to_equality,[status(thm)],[c_1091]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_485,plain,
% 2.19/0.97      ( X0_48 != X1_48 | X2_48 != X1_48 | X2_48 = X0_48 ),
% 2.19/0.97      theory(equality) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1106,plain,
% 2.19/0.97      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_48
% 2.19/0.97      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.19/0.97      | u1_struct_0(sK1) != X0_48 ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_485]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1178,plain,
% 2.19/0.97      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 2.19/0.97      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 2.19/0.97      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_1106]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_5,plain,
% 2.19/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.97      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 2.19/0.97      | ~ v1_funct_1(X0)
% 2.19/0.97      | ~ v2_funct_1(X0)
% 2.19/0.97      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.19/0.97      inference(cnf_transformation,[],[f40]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_476,plain,
% 2.19/0.97      ( ~ v1_funct_2(X0_47,X0_48,X1_48)
% 2.19/0.97      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.19/0.97      | m1_subset_1(k2_funct_1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48)))
% 2.19/0.97      | ~ v1_funct_1(X0_47)
% 2.19/0.97      | ~ v2_funct_1(X0_47)
% 2.19/0.97      | k2_relset_1(X0_48,X1_48,X0_47) != X1_48 ),
% 2.19/0.97      inference(subtyping,[status(esa)],[c_5]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_854,plain,
% 2.19/0.97      ( k2_relset_1(X0_48,X1_48,X0_47) != X1_48
% 2.19/0.97      | v1_funct_2(X0_47,X0_48,X1_48) != iProver_top
% 2.19/0.97      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.19/0.97      | m1_subset_1(k2_funct_1(X0_47),k1_zfmisc_1(k2_zfmisc_1(X1_48,X0_48))) = iProver_top
% 2.19/0.97      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(X0_47) != iProver_top ),
% 2.19/0.97      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1637,plain,
% 2.19/0.97      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) = iProver_top
% 2.19/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | v1_funct_1(sK2) != iProver_top
% 2.19/0.97      | v2_funct_1(sK2) != iProver_top ),
% 2.19/0.97      inference(superposition,[status(thm)],[c_1416,c_854]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_6,plain,
% 2.19/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/0.97      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 2.19/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.97      | ~ v1_funct_1(X0)
% 2.19/0.97      | ~ v2_funct_1(X0)
% 2.19/0.97      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.19/0.97      inference(cnf_transformation,[],[f39]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_475,plain,
% 2.19/0.97      ( ~ v1_funct_2(X0_47,X0_48,X1_48)
% 2.19/0.97      | v1_funct_2(k2_funct_1(X0_47),X1_48,X0_48)
% 2.19/0.97      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48)))
% 2.19/0.97      | ~ v1_funct_1(X0_47)
% 2.19/0.97      | ~ v2_funct_1(X0_47)
% 2.19/0.97      | k2_relset_1(X0_48,X1_48,X0_47) != X1_48 ),
% 2.19/0.97      inference(subtyping,[status(esa)],[c_6]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_855,plain,
% 2.19/0.97      ( k2_relset_1(X0_48,X1_48,X0_47) != X1_48
% 2.19/0.97      | v1_funct_2(X0_47,X0_48,X1_48) != iProver_top
% 2.19/0.97      | v1_funct_2(k2_funct_1(X0_47),X1_48,X0_48) = iProver_top
% 2.19/0.97      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(X0_48,X1_48))) != iProver_top
% 2.19/0.97      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(X0_47) != iProver_top ),
% 2.19/0.97      inference(predicate_to_equality,[status(thm)],[c_475]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1672,plain,
% 2.19/0.97      ( v1_funct_2(k2_funct_1(sK2),k2_struct_0(sK1),k2_struct_0(sK0)) = iProver_top
% 2.19/0.97      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | v1_funct_1(sK2) != iProver_top
% 2.19/0.97      | v2_funct_1(sK2) != iProver_top ),
% 2.19/0.97      inference(superposition,[status(thm)],[c_1416,c_855]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_12,plain,
% 2.19/0.97      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 2.19/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 2.19/0.97      | ~ l1_struct_0(X1)
% 2.19/0.97      | ~ l1_struct_0(X2)
% 2.19/0.97      | ~ v1_funct_1(X0)
% 2.19/0.97      | ~ v2_funct_1(X0)
% 2.19/0.97      | v2_funct_1(k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0))
% 2.19/0.97      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2) ),
% 2.19/0.97      inference(cnf_transformation,[],[f45]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_471,plain,
% 2.19/0.97      ( ~ v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49))
% 2.19/0.97      | ~ m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49))))
% 2.19/0.97      | ~ l1_struct_0(X1_49)
% 2.19/0.97      | ~ l1_struct_0(X0_49)
% 2.19/0.97      | ~ v1_funct_1(X0_47)
% 2.19/0.97      | ~ v2_funct_1(X0_47)
% 2.19/0.97      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_47))
% 2.19/0.97      | k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_47) != k2_struct_0(X1_49) ),
% 2.19/0.97      inference(subtyping,[status(esa)],[c_12]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_859,plain,
% 2.19/0.97      ( k2_relset_1(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_47) != k2_struct_0(X1_49)
% 2.19/0.97      | v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(X1_49)) != iProver_top
% 2.19/0.97      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(X1_49)))) != iProver_top
% 2.19/0.97      | l1_struct_0(X0_49) != iProver_top
% 2.19/0.97      | l1_struct_0(X1_49) != iProver_top
% 2.19/0.97      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(X1_49),X0_47)) = iProver_top ),
% 2.19/0.97      inference(predicate_to_equality,[status(thm)],[c_471]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1738,plain,
% 2.19/0.97      ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.97      | v1_funct_2(X0_47,u1_struct_0(X0_49),u1_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),u1_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | l1_struct_0(X0_49) != iProver_top
% 2.19/0.97      | l1_struct_0(sK1) != iProver_top
% 2.19/0.97      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),u1_struct_0(sK1),X0_47)) = iProver_top ),
% 2.19/0.97      inference(superposition,[status(thm)],[c_1215,c_859]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1747,plain,
% 2.19/0.97      ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.97      | v1_funct_2(X0_47,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | l1_struct_0(X0_49) != iProver_top
% 2.19/0.97      | l1_struct_0(sK1) != iProver_top
% 2.19/0.97      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47)) = iProver_top ),
% 2.19/0.97      inference(light_normalisation,[status(thm)],[c_1738,c_1215]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_24,plain,
% 2.19/0.97      ( l1_struct_0(sK1) = iProver_top ),
% 2.19/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_2482,plain,
% 2.19/0.97      ( l1_struct_0(X0_49) != iProver_top
% 2.19/0.97      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | v1_funct_2(X0_47,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.97      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47)) = iProver_top ),
% 2.19/0.97      inference(global_propositional_subsumption,
% 2.19/0.97                [status(thm)],
% 2.19/0.97                [c_1747,c_24]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_2483,plain,
% 2.19/0.97      ( k2_relset_1(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.97      | v1_funct_2(X0_47,u1_struct_0(X0_49),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0_49),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | l1_struct_0(X0_49) != iProver_top
% 2.19/0.97      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(k2_tops_2(u1_struct_0(X0_49),k2_struct_0(sK1),X0_47)) = iProver_top ),
% 2.19/0.97      inference(renaming,[status(thm)],[c_2482]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_2493,plain,
% 2.19/0.97      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.97      | v1_funct_2(X0_47,u1_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | l1_struct_0(sK0) != iProver_top
% 2.19/0.97      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),X0_47)) = iProver_top ),
% 2.19/0.97      inference(superposition,[status(thm)],[c_1216,c_2483]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_2517,plain,
% 2.19/0.97      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.97      | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | l1_struct_0(sK0) != iProver_top
% 2.19/0.97      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = iProver_top ),
% 2.19/0.97      inference(light_normalisation,[status(thm)],[c_2493,c_1216]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_2676,plain,
% 2.19/0.97      ( m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.97      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = iProver_top ),
% 2.19/0.97      inference(global_propositional_subsumption,
% 2.19/0.97                [status(thm)],
% 2.19/0.97                [c_2517,c_22]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_2677,plain,
% 2.19/0.97      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_47) != k2_struct_0(sK1)
% 2.19/0.97      | v1_funct_2(X0_47,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(X0_47,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_47)) = iProver_top ),
% 2.19/0.97      inference(renaming,[status(thm)],[c_2676]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_2688,plain,
% 2.19/0.97      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | v1_funct_1(sK2) != iProver_top
% 2.19/0.97      | v2_funct_1(k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = iProver_top
% 2.19/0.97      | v2_funct_1(sK2) != iProver_top ),
% 2.19/0.97      inference(superposition,[status(thm)],[c_1416,c_2677]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_2689,plain,
% 2.19/0.97      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | v1_funct_1(sK2) != iProver_top
% 2.19/0.97      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 2.19/0.97      | v2_funct_1(sK2) != iProver_top ),
% 2.19/0.97      inference(light_normalisation,[status(thm)],[c_2688,c_2084]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_3340,plain,
% 2.19/0.97      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 2.19/0.97      inference(global_propositional_subsumption,
% 2.19/0.97                [status(thm)],
% 2.19/0.97                [c_3331,c_19,c_25,c_26,c_27,c_28,c_529,c_469,c_1092,
% 2.19/0.97                 c_1178,c_1535,c_1625,c_1637,c_1672,c_2689]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_3,plain,
% 2.19/0.97      ( r2_funct_2(X0,X1,X2,X2)
% 2.19/0.97      | ~ v1_funct_2(X2,X0,X1)
% 2.19/0.97      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.19/0.97      | ~ v1_funct_1(X2) ),
% 2.19/0.97      inference(cnf_transformation,[],[f55]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_13,negated_conjecture,
% 2.19/0.97      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 2.19/0.97      inference(cnf_transformation,[],[f54]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_236,plain,
% 2.19/0.97      ( ~ v1_funct_2(X0,X1,X2)
% 2.19/0.97      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.19/0.97      | ~ v1_funct_1(X0)
% 2.19/0.97      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 2.19/0.97      | u1_struct_0(sK1) != X2
% 2.19/0.97      | u1_struct_0(sK0) != X1
% 2.19/0.97      | sK2 != X0 ),
% 2.19/0.97      inference(resolution_lifted,[status(thm)],[c_3,c_13]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_237,plain,
% 2.19/0.97      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.19/0.97      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.19/0.97      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.19/0.97      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.19/0.97      inference(unflattening,[status(thm)],[c_236]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_463,plain,
% 2.19/0.97      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 2.19/0.97      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.19/0.97      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.19/0.97      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.19/0.97      inference(subtyping,[status(esa)],[c_237]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_866,plain,
% 2.19/0.97      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.19/0.97      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.19/0.97      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_543,plain,
% 2.19/0.97      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.19/0.97      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 2.19/0.97      inference(predicate_to_equality,[status(thm)],[c_463]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_492,plain,
% 2.19/0.97      ( ~ v1_funct_1(X0_47) | v1_funct_1(X1_47) | X1_47 != X0_47 ),
% 2.19/0.97      theory(equality) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1067,plain,
% 2.19/0.97      ( ~ v1_funct_1(X0_47)
% 2.19/0.97      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 2.19/0.97      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0_47 ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_492]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1068,plain,
% 2.19/0.97      ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0_47
% 2.19/0.97      | v1_funct_1(X0_47) != iProver_top
% 2.19/0.97      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = iProver_top ),
% 2.19/0.97      inference(predicate_to_equality,[status(thm)],[c_1067]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1070,plain,
% 2.19/0.97      ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != sK2
% 2.19/0.97      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = iProver_top
% 2.19/0.97      | v1_funct_1(sK2) != iProver_top ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_1068]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_484,plain,
% 2.19/0.97      ( X0_47 != X1_47 | X2_47 != X1_47 | X2_47 = X0_47 ),
% 2.19/0.97      theory(equality) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1143,plain,
% 2.19/0.97      ( X0_47 != X1_47
% 2.19/0.97      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X1_47
% 2.19/0.97      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = X0_47 ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_484]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1273,plain,
% 2.19/0.97      ( X0_47 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.19/0.97      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = X0_47
% 2.19/0.97      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_1143]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1275,plain,
% 2.19/0.97      ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.19/0.97      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = sK2
% 2.19/0.97      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_1273]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_481,plain,( X0_47 = X0_47 ),theory(equality) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_1274,plain,
% 2.19/0.97      ( k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_481]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_2005,plain,
% 2.19/0.97      ( m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.19/0.97      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.19/0.97      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 2.19/0.97      inference(global_propositional_subsumption,
% 2.19/0.97                [status(thm)],
% 2.19/0.97                [c_866,c_25,c_543,c_1070,c_1275,c_1274]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_2006,plain,
% 2.19/0.97      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 2.19/0.97      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top ),
% 2.19/0.97      inference(renaming,[status(thm)],[c_2005]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_2009,plain,
% 2.19/0.97      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 2.19/0.97      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.19/0.97      inference(light_normalisation,[status(thm)],[c_2006,c_1215,c_1216]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_2087,plain,
% 2.19/0.97      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 2.19/0.97      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.19/0.97      inference(demodulation,[status(thm)],[c_2084,c_2009]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_3343,plain,
% 2.19/0.97      ( sK2 != sK2
% 2.19/0.97      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 2.19/0.97      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top ),
% 2.19/0.97      inference(demodulation,[status(thm)],[c_3340,c_2087]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(c_509,plain,
% 2.19/0.97      ( sK2 = sK2 ),
% 2.19/0.97      inference(instantiation,[status(thm)],[c_481]) ).
% 2.19/0.97  
% 2.19/0.97  cnf(contradiction,plain,
% 2.19/0.97      ( $false ),
% 2.19/0.97      inference(minisat,[status(thm)],[c_3343,c_1625,c_1535,c_509]) ).
% 2.19/0.97  
% 2.19/0.97  
% 2.19/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 2.19/0.97  
% 2.19/0.97  ------                               Statistics
% 2.19/0.97  
% 2.19/0.97  ------ General
% 2.19/0.97  
% 2.19/0.97  abstr_ref_over_cycles:                  0
% 2.19/0.97  abstr_ref_under_cycles:                 0
% 2.19/0.97  gc_basic_clause_elim:                   0
% 2.19/0.97  forced_gc_time:                         0
% 2.19/0.97  parsing_time:                           0.01
% 2.19/0.97  unif_index_cands_time:                  0.
% 2.19/0.97  unif_index_add_time:                    0.
% 2.19/0.97  orderings_time:                         0.
% 2.19/0.97  out_proof_time:                         0.013
% 2.19/0.97  total_time:                             0.16
% 2.19/0.97  num_of_symbols:                         51
% 2.19/0.97  num_of_terms:                           3472
% 2.19/0.97  
% 2.19/0.97  ------ Preprocessing
% 2.19/0.97  
% 2.19/0.97  num_of_splits:                          0
% 2.19/0.97  num_of_split_atoms:                     0
% 2.19/0.97  num_of_reused_defs:                     0
% 2.19/0.97  num_eq_ax_congr_red:                    3
% 2.19/0.97  num_of_sem_filtered_clauses:            1
% 2.19/0.97  num_of_subtypes:                        4
% 2.19/0.97  monotx_restored_types:                  0
% 2.19/0.97  sat_num_of_epr_types:                   0
% 2.19/0.97  sat_num_of_non_cyclic_types:            0
% 2.19/0.97  sat_guarded_non_collapsed_types:        1
% 2.19/0.97  num_pure_diseq_elim:                    0
% 2.19/0.97  simp_replaced_by:                       0
% 2.19/0.97  res_preprocessed:                       112
% 2.19/0.97  prep_upred:                             0
% 2.19/0.97  prep_unflattend:                        9
% 2.19/0.97  smt_new_axioms:                         0
% 2.19/0.97  pred_elim_cands:                        6
% 2.19/0.97  pred_elim:                              2
% 2.19/0.97  pred_elim_cl:                           3
% 2.19/0.97  pred_elim_cycles:                       4
% 2.19/0.97  merged_defs:                            0
% 2.19/0.97  merged_defs_ncl:                        0
% 2.19/0.97  bin_hyper_res:                          0
% 2.19/0.97  prep_cycles:                            4
% 2.19/0.97  pred_elim_time:                         0.004
% 2.19/0.97  splitting_time:                         0.
% 2.19/0.97  sem_filter_time:                        0.
% 2.19/0.97  monotx_time:                            0.
% 2.19/0.97  subtype_inf_time:                       0.
% 2.19/0.97  
% 2.19/0.97  ------ Problem properties
% 2.19/0.97  
% 2.19/0.97  clauses:                                19
% 2.19/0.97  conjectures:                            7
% 2.19/0.97  epr:                                    4
% 2.19/0.97  horn:                                   19
% 2.19/0.97  ground:                                 8
% 2.19/0.97  unary:                                  8
% 2.19/0.97  binary:                                 1
% 2.19/0.97  lits:                                   67
% 2.19/0.97  lits_eq:                                14
% 2.19/0.97  fd_pure:                                0
% 2.19/0.97  fd_pseudo:                              0
% 2.19/0.97  fd_cond:                                0
% 2.19/0.97  fd_pseudo_cond:                         0
% 2.19/0.97  ac_symbols:                             0
% 2.19/0.97  
% 2.19/0.97  ------ Propositional Solver
% 2.19/0.97  
% 2.19/0.97  prop_solver_calls:                      29
% 2.19/0.97  prop_fast_solver_calls:                 1116
% 2.19/0.97  smt_solver_calls:                       0
% 2.19/0.97  smt_fast_solver_calls:                  0
% 2.19/0.97  prop_num_of_clauses:                    1119
% 2.19/0.97  prop_preprocess_simplified:             4211
% 2.19/0.97  prop_fo_subsumed:                       55
% 2.19/0.97  prop_solver_time:                       0.
% 2.19/0.97  smt_solver_time:                        0.
% 2.19/0.97  smt_fast_solver_time:                   0.
% 2.19/0.97  prop_fast_solver_time:                  0.
% 2.19/0.97  prop_unsat_core_time:                   0.
% 2.19/0.97  
% 2.19/0.97  ------ QBF
% 2.19/0.97  
% 2.19/0.97  qbf_q_res:                              0
% 2.19/0.97  qbf_num_tautologies:                    0
% 2.19/0.97  qbf_prep_cycles:                        0
% 2.19/0.97  
% 2.19/0.97  ------ BMC1
% 2.19/0.97  
% 2.19/0.97  bmc1_current_bound:                     -1
% 2.19/0.97  bmc1_last_solved_bound:                 -1
% 2.19/0.97  bmc1_unsat_core_size:                   -1
% 2.19/0.97  bmc1_unsat_core_parents_size:           -1
% 2.19/0.97  bmc1_merge_next_fun:                    0
% 2.19/0.97  bmc1_unsat_core_clauses_time:           0.
% 2.19/0.97  
% 2.19/0.97  ------ Instantiation
% 2.19/0.97  
% 2.19/0.97  inst_num_of_clauses:                    401
% 2.19/0.97  inst_num_in_passive:                    75
% 2.19/0.97  inst_num_in_active:                     224
% 2.19/0.97  inst_num_in_unprocessed:                102
% 2.19/0.97  inst_num_of_loops:                      260
% 2.19/0.97  inst_num_of_learning_restarts:          0
% 2.19/0.97  inst_num_moves_active_passive:          32
% 2.19/0.97  inst_lit_activity:                      0
% 2.19/0.97  inst_lit_activity_moves:                0
% 2.19/0.97  inst_num_tautologies:                   0
% 2.19/0.97  inst_num_prop_implied:                  0
% 2.19/0.97  inst_num_existing_simplified:           0
% 2.19/0.97  inst_num_eq_res_simplified:             0
% 2.19/0.97  inst_num_child_elim:                    0
% 2.19/0.97  inst_num_of_dismatching_blockings:      71
% 2.19/0.97  inst_num_of_non_proper_insts:           391
% 2.19/0.97  inst_num_of_duplicates:                 0
% 2.19/0.97  inst_inst_num_from_inst_to_res:         0
% 2.19/0.97  inst_dismatching_checking_time:         0.
% 2.19/0.97  
% 2.19/0.97  ------ Resolution
% 2.19/0.97  
% 2.19/0.97  res_num_of_clauses:                     0
% 2.19/0.97  res_num_in_passive:                     0
% 2.19/0.97  res_num_in_active:                      0
% 2.19/0.97  res_num_of_loops:                       116
% 2.19/0.97  res_forward_subset_subsumed:            39
% 2.19/0.97  res_backward_subset_subsumed:           0
% 2.19/0.97  res_forward_subsumed:                   0
% 2.19/0.97  res_backward_subsumed:                  0
% 2.19/0.97  res_forward_subsumption_resolution:     0
% 2.19/0.97  res_backward_subsumption_resolution:    0
% 2.19/0.97  res_clause_to_clause_subsumption:       56
% 2.19/0.97  res_orphan_elimination:                 0
% 2.19/0.97  res_tautology_del:                      42
% 2.19/0.97  res_num_eq_res_simplified:              0
% 2.19/0.97  res_num_sel_changes:                    0
% 2.19/0.97  res_moves_from_active_to_pass:          0
% 2.19/0.97  
% 2.19/0.97  ------ Superposition
% 2.19/0.97  
% 2.19/0.97  sup_time_total:                         0.
% 2.19/0.97  sup_time_generating:                    0.
% 2.19/0.97  sup_time_sim_full:                      0.
% 2.19/0.97  sup_time_sim_immed:                     0.
% 2.19/0.97  
% 2.19/0.97  sup_num_of_clauses:                     45
% 2.19/0.97  sup_num_in_active:                      42
% 2.19/0.97  sup_num_in_passive:                     3
% 2.19/0.97  sup_num_of_loops:                       51
% 2.19/0.97  sup_fw_superposition:                   28
% 2.19/0.97  sup_bw_superposition:                   10
% 2.19/0.97  sup_immediate_simplified:               26
% 2.19/0.97  sup_given_eliminated:                   0
% 2.19/0.97  comparisons_done:                       0
% 2.19/0.97  comparisons_avoided:                    0
% 2.19/0.97  
% 2.19/0.97  ------ Simplifications
% 2.19/0.97  
% 2.19/0.97  
% 2.19/0.97  sim_fw_subset_subsumed:                 3
% 2.19/0.97  sim_bw_subset_subsumed:                 0
% 2.19/0.97  sim_fw_subsumed:                        5
% 2.19/0.97  sim_bw_subsumed:                        0
% 2.19/0.97  sim_fw_subsumption_res:                 1
% 2.19/0.97  sim_bw_subsumption_res:                 0
% 2.19/0.97  sim_tautology_del:                      0
% 2.19/0.97  sim_eq_tautology_del:                   1
% 2.19/0.97  sim_eq_res_simp:                        0
% 2.19/0.97  sim_fw_demodulated:                     0
% 2.19/0.97  sim_bw_demodulated:                     9
% 2.19/0.97  sim_light_normalised:                   29
% 2.19/0.97  sim_joinable_taut:                      0
% 2.19/0.97  sim_joinable_simp:                      0
% 2.19/0.97  sim_ac_normalised:                      0
% 2.19/0.97  sim_smt_subsumption:                    0
% 2.19/0.97  
%------------------------------------------------------------------------------
