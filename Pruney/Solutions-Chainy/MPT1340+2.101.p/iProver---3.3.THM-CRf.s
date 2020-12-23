%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:43 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  219 (12703 expanded)
%              Number of clauses        :  154 (4015 expanded)
%              Number of leaves         :   18 (3646 expanded)
%              Depth                    :   27
%              Number of atoms          :  855 (82086 expanded)
%              Number of equality atoms :  357 (14685 expanded)
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

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f39,plain,(
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

fof(f38,plain,(
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

fof(f37,plain,
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

fof(f40,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f57,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f61,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f40])).

fof(f63,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
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

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f68,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f65,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f20,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f48,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f41,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f13,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f13])).

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

fof(f60,plain,(
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

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f69,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f51,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f47,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f20])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
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

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f22,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f49,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_743,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(subtyping,[status(esa)],[c_23])).

cnf(c_1288,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_16,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_28,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_528,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_28])).

cnf(c_529,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_528])).

cnf(c_734,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(subtyping,[status(esa)],[c_529])).

cnf(c_26,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_523,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_26])).

cnf(c_524,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_523])).

cnf(c_735,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_524])).

cnf(c_1317,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1288,c_734,c_735])).

cnf(c_11,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_750,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | k2_relset_1(X0_51,X1_51,X0_53) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_11])).

cnf(c_1282,plain,
    ( k2_relset_1(X0_51,X1_51,X0_53) = k2_relat_1(X0_53)
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_750])).

cnf(c_1779,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1317,c_1282])).

cnf(c_22,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_744,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_22])).

cnf(c_1314,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_744,c_734,c_735])).

cnf(c_1947,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1779,c_1314])).

cnf(c_1988,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1947,c_1779])).

cnf(c_13,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_749,plain,
    ( ~ v1_funct_2(X0_53,X0_51,X1_51)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
    | ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | k2_relset_1(X0_51,X1_51,X0_53) != X1_51 ),
    inference(subtyping,[status(esa)],[c_13])).

cnf(c_1283,plain,
    ( k2_relset_1(X0_51,X1_51,X0_53) != X1_51
    | v1_funct_2(X0_53,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) = iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_749])).

cnf(c_3236,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1988,c_1283])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_32,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_21,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_35,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1995,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1947,c_1317])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_742,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subtyping,[status(esa)],[c_24])).

cnf(c_1289,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_742])).

cnf(c_1311,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1289,c_734,c_735])).

cnf(c_1996,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1947,c_1311])).

cnf(c_4119,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3236,c_32,c_35,c_1995,c_1996])).

cnf(c_4124,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4119,c_1282])).

cnf(c_741,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(subtyping,[status(esa)],[c_25])).

cnf(c_1290,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_741])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_755,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_6])).

cnf(c_1277,plain,
    ( k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53)
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_755])).

cnf(c_2102,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_1277])).

cnf(c_817,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_755])).

cnf(c_0,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_761,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
    | ~ v1_relat_1(X1_53)
    | v1_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_0])).

cnf(c_1586,plain,
    ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | v1_relat_1(X0_53)
    | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(instantiation,[status(thm)],[c_761])).

cnf(c_1757,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_1,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_760,plain,
    ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
    inference(subtyping,[status(esa)],[c_1])).

cnf(c_1788,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_2408,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2102,c_25,c_23,c_21,c_817,c_1757,c_1788])).

cnf(c_17,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_746,plain,
    ( ~ v1_funct_2(X0_53,X0_51,X1_51)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | k2_tops_2(X0_51,X1_51,X0_53) = k2_funct_1(X0_53)
    | k2_relset_1(X0_51,X1_51,X0_53) != X1_51 ),
    inference(subtyping,[status(esa)],[c_17])).

cnf(c_1286,plain,
    ( k2_tops_2(X0_51,X1_51,X0_53) = k2_funct_1(X0_53)
    | k2_relset_1(X0_51,X1_51,X0_53) != X1_51
    | v1_funct_2(X0_53,X0_51,X1_51) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_746])).

cnf(c_2836,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1988,c_1286])).

cnf(c_3486,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2836,c_32,c_35,c_1995,c_1996])).

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
    inference(cnf_transformation,[],[f60])).

cnf(c_27,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f62])).

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
    inference(resolution_lifted,[status(thm)],[c_18,c_27])).

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
    inference(global_propositional_subsumption,[status(thm)],[c_381,c_26])).

cnf(c_386,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ l1_struct_0(X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
    inference(renaming,[status(thm)],[c_385])).

cnf(c_475,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1)
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_386,c_28])).

cnf(c_476,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_737,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_53)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_53) != k2_struct_0(sK1) ),
    inference(subtyping,[status(esa)],[c_476])).

cnf(c_1295,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_53)) = k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_53) != k2_struct_0(sK1)
    | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_737])).

cnf(c_1481,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_53)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_53) != k2_struct_0(sK1)
    | v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1295,c_734,c_735])).

cnf(c_1835,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1314,c_1481])).

cnf(c_1529,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1317])).

cnf(c_1536,plain,
    ( ~ v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_53)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_53) != k2_struct_0(sK1) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1481])).

cnf(c_1538,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1536])).

cnf(c_1546,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1311])).

cnf(c_1881,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1835,c_25,c_21,c_1529,c_1538,c_1546,c_1314])).

cnf(c_1991,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_1947,c_1881])).

cnf(c_3489,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3486,c_1991])).

cnf(c_4131,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_4124,c_2408,c_3489])).

cnf(c_12,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X3,X0,X1)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X3)
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_20,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_314,plain,
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
    inference(resolution_lifted,[status(thm)],[c_12,c_20])).

cnf(c_315,plain,
    ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_314])).

cnf(c_740,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(subtyping,[status(esa)],[c_315])).

cnf(c_763,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sP0_iProver_split
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_740])).

cnf(c_1291,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_763])).

cnf(c_1507,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
    | sP0_iProver_split = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1291,c_734,c_735])).

cnf(c_762,plain,
    ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(X0_53)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_740])).

cnf(c_1292,plain,
    ( v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_762])).

cnf(c_1370,plain,
    ( v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | sP0_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1292,c_734,c_735])).

cnf(c_1513,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1507,c_1370])).

cnf(c_3949,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1513,c_1947,c_3486])).

cnf(c_4148,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4131,c_3949])).

cnf(c_3957,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3489,c_1286])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f51])).

cnf(c_751,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k2_funct_1(k2_funct_1(X0_53)) = X0_53 ),
    inference(subtyping,[status(esa)],[c_10])).

cnf(c_1281,plain,
    ( k2_funct_1(k2_funct_1(X0_53)) = X0_53
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_751])).

cnf(c_2095,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_1281])).

cnf(c_829,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(instantiation,[status(thm)],[c_751])).

cnf(c_2302,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2095,c_25,c_23,c_21,c_829,c_1757,c_1788])).

cnf(c_3977,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3957,c_2302])).

cnf(c_33,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_34,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_15,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_747,plain,
    ( ~ v1_funct_2(X0_53,X0_51,X1_51)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_53)
    | v1_funct_1(k2_funct_1(X0_53))
    | ~ v2_funct_1(X0_53)
    | k2_relset_1(X0_51,X1_51,X0_53) != X1_51 ),
    inference(subtyping,[status(esa)],[c_15])).

cnf(c_1652,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_747])).

cnf(c_1653,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1652])).

cnf(c_768,plain,
    ( X0_51 != X1_51
    | X2_51 != X1_51
    | X2_51 = X0_51 ),
    theory(equality)).

cnf(c_1707,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_51
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0_51 ),
    inference(instantiation,[status(thm)],[c_768])).

cnf(c_1793,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1707])).

cnf(c_14,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_748,plain,
    ( ~ v1_funct_2(X0_53,X0_51,X1_51)
    | v1_funct_2(k2_funct_1(X0_53),X1_51,X0_51)
    | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
    | ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | k2_relset_1(X0_51,X1_51,X0_53) != X1_51 ),
    inference(subtyping,[status(esa)],[c_14])).

cnf(c_1284,plain,
    ( k2_relset_1(X0_51,X1_51,X0_53) != X1_51
    | v1_funct_2(X0_53,X0_51,X1_51) != iProver_top
    | v1_funct_2(k2_funct_1(X0_53),X1_51,X0_51) = iProver_top
    | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_748])).

cnf(c_2786,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1988,c_1284])).

cnf(c_7,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_754,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k1_relat_1(k2_funct_1(X0_53)) = k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_7])).

cnf(c_1278,plain,
    ( k1_relat_1(k2_funct_1(X0_53)) = k2_relat_1(X0_53)
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_754])).

cnf(c_2194,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_1278])).

cnf(c_820,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_754])).

cnf(c_2414,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2194,c_25,c_23,c_21,c_820,c_1757,c_1788])).

cnf(c_4,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | v2_funct_1(X1)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_757,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v1_funct_1(X1_53)
    | v2_funct_1(X1_53)
    | ~ v2_funct_1(k5_relat_1(X0_53,X1_53))
    | ~ v1_relat_1(X0_53)
    | ~ v1_relat_1(X1_53)
    | k1_relat_1(X1_53) != k2_relat_1(X0_53) ),
    inference(subtyping,[status(esa)],[c_4])).

cnf(c_1275,plain,
    ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
    | v1_funct_1(X1_53) != iProver_top
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) = iProver_top
    | v2_funct_1(k5_relat_1(X1_53,X0_53)) != iProver_top
    | v1_relat_1(X1_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_757])).

cnf(c_2417,plain,
    ( k2_relat_1(X0_53) != k2_relat_1(sK2)
    | v1_funct_1(X0_53) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2414,c_1275])).

cnf(c_1658,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_749])).

cnf(c_1659,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1658])).

cnf(c_1864,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1586])).

cnf(c_1868,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1864])).

cnf(c_2663,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_760])).

cnf(c_2664,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2663])).

cnf(c_3206,plain,
    ( v1_relat_1(X0_53) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
    | k2_relat_1(X0_53) != k2_relat_1(sK2)
    | v1_funct_1(X0_53) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2417,c_32,c_33,c_34,c_35,c_744,c_735,c_1653,c_1659,c_1793,c_1868,c_2664])).

cnf(c_3207,plain,
    ( k2_relat_1(X0_53) != k2_relat_1(sK2)
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(renaming,[status(thm)],[c_3206])).

cnf(c_3218,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3207])).

cnf(c_9,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_752,plain,
    ( ~ v1_funct_1(X0_53)
    | ~ v2_funct_1(X0_53)
    | ~ v1_relat_1(X0_53)
    | k5_relat_1(X0_53,k2_funct_1(X0_53)) = k6_relat_1(k1_relat_1(X0_53)) ),
    inference(subtyping,[status(esa)],[c_9])).

cnf(c_1280,plain,
    ( k5_relat_1(X0_53,k2_funct_1(X0_53)) = k6_relat_1(k1_relat_1(X0_53))
    | v1_funct_1(X0_53) != iProver_top
    | v2_funct_1(X0_53) != iProver_top
    | v1_relat_1(X0_53) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_752])).

cnf(c_2717,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1290,c_1280])).

cnf(c_826,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_752])).

cnf(c_2839,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2717,c_25,c_23,c_21,c_826,c_1757,c_1788])).

cnf(c_3223,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3218,c_2839])).

cnf(c_1758,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1757])).

cnf(c_1789,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1788])).

cnf(c_3496,plain,
    ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3223,c_32,c_34,c_1758,c_1789])).

cnf(c_3497,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3496])).

cnf(c_2,plain,
    ( v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_759,plain,
    ( v2_funct_1(k6_relat_1(X0_51)) ),
    inference(subtyping,[status(esa)],[c_2])).

cnf(c_1273,plain,
    ( v2_funct_1(k6_relat_1(X0_51)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_759])).

cnf(c_3502,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3497,c_1273])).

cnf(c_4349,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3977,c_32,c_33,c_34,c_35,c_744,c_735,c_1653,c_1793,c_1995,c_1996,c_2786,c_3236,c_3502])).

cnf(c_4351,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_4349,c_4131])).

cnf(c_4960,plain,
    ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4148,c_4351])).

cnf(c_4964,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4960,c_4351])).

cnf(c_4153,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4131,c_1995])).

cnf(c_4155,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4131,c_1996])).

cnf(c_4968,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4964,c_1290,c_4153,c_4155])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:16:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.02/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.00  
% 3.02/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.02/1.00  
% 3.02/1.00  ------  iProver source info
% 3.02/1.00  
% 3.02/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.02/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.02/1.00  git: non_committed_changes: false
% 3.02/1.00  git: last_make_outside_of_git: false
% 3.02/1.00  
% 3.02/1.00  ------ 
% 3.02/1.00  
% 3.02/1.00  ------ Input Options
% 3.02/1.00  
% 3.02/1.00  --out_options                           all
% 3.02/1.00  --tptp_safe_out                         true
% 3.02/1.00  --problem_path                          ""
% 3.02/1.00  --include_path                          ""
% 3.02/1.00  --clausifier                            res/vclausify_rel
% 3.02/1.00  --clausifier_options                    --mode clausify
% 3.02/1.00  --stdin                                 false
% 3.02/1.00  --stats_out                             all
% 3.02/1.00  
% 3.02/1.00  ------ General Options
% 3.02/1.00  
% 3.02/1.00  --fof                                   false
% 3.02/1.00  --time_out_real                         305.
% 3.02/1.00  --time_out_virtual                      -1.
% 3.02/1.00  --symbol_type_check                     false
% 3.02/1.00  --clausify_out                          false
% 3.02/1.00  --sig_cnt_out                           false
% 3.02/1.00  --trig_cnt_out                          false
% 3.02/1.00  --trig_cnt_out_tolerance                1.
% 3.02/1.00  --trig_cnt_out_sk_spl                   false
% 3.02/1.00  --abstr_cl_out                          false
% 3.02/1.00  
% 3.02/1.00  ------ Global Options
% 3.02/1.00  
% 3.02/1.00  --schedule                              default
% 3.02/1.00  --add_important_lit                     false
% 3.02/1.00  --prop_solver_per_cl                    1000
% 3.02/1.00  --min_unsat_core                        false
% 3.02/1.00  --soft_assumptions                      false
% 3.02/1.00  --soft_lemma_size                       3
% 3.02/1.00  --prop_impl_unit_size                   0
% 3.02/1.00  --prop_impl_unit                        []
% 3.02/1.00  --share_sel_clauses                     true
% 3.02/1.00  --reset_solvers                         false
% 3.02/1.00  --bc_imp_inh                            [conj_cone]
% 3.02/1.00  --conj_cone_tolerance                   3.
% 3.02/1.00  --extra_neg_conj                        none
% 3.02/1.00  --large_theory_mode                     true
% 3.02/1.00  --prolific_symb_bound                   200
% 3.02/1.00  --lt_threshold                          2000
% 3.02/1.00  --clause_weak_htbl                      true
% 3.02/1.00  --gc_record_bc_elim                     false
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing Options
% 3.02/1.00  
% 3.02/1.00  --preprocessing_flag                    true
% 3.02/1.00  --time_out_prep_mult                    0.1
% 3.02/1.00  --splitting_mode                        input
% 3.02/1.00  --splitting_grd                         true
% 3.02/1.00  --splitting_cvd                         false
% 3.02/1.00  --splitting_cvd_svl                     false
% 3.02/1.00  --splitting_nvd                         32
% 3.02/1.00  --sub_typing                            true
% 3.02/1.00  --prep_gs_sim                           true
% 3.02/1.00  --prep_unflatten                        true
% 3.02/1.00  --prep_res_sim                          true
% 3.02/1.00  --prep_upred                            true
% 3.02/1.00  --prep_sem_filter                       exhaustive
% 3.02/1.00  --prep_sem_filter_out                   false
% 3.02/1.00  --pred_elim                             true
% 3.02/1.00  --res_sim_input                         true
% 3.02/1.00  --eq_ax_congr_red                       true
% 3.02/1.00  --pure_diseq_elim                       true
% 3.02/1.00  --brand_transform                       false
% 3.02/1.00  --non_eq_to_eq                          false
% 3.02/1.00  --prep_def_merge                        true
% 3.02/1.00  --prep_def_merge_prop_impl              false
% 3.02/1.00  --prep_def_merge_mbd                    true
% 3.02/1.00  --prep_def_merge_tr_red                 false
% 3.02/1.00  --prep_def_merge_tr_cl                  false
% 3.02/1.00  --smt_preprocessing                     true
% 3.02/1.00  --smt_ac_axioms                         fast
% 3.02/1.00  --preprocessed_out                      false
% 3.02/1.00  --preprocessed_stats                    false
% 3.02/1.00  
% 3.02/1.00  ------ Abstraction refinement Options
% 3.02/1.00  
% 3.02/1.00  --abstr_ref                             []
% 3.02/1.00  --abstr_ref_prep                        false
% 3.02/1.00  --abstr_ref_until_sat                   false
% 3.02/1.00  --abstr_ref_sig_restrict                funpre
% 3.02/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/1.00  --abstr_ref_under                       []
% 3.02/1.00  
% 3.02/1.00  ------ SAT Options
% 3.02/1.00  
% 3.02/1.00  --sat_mode                              false
% 3.02/1.00  --sat_fm_restart_options                ""
% 3.02/1.00  --sat_gr_def                            false
% 3.02/1.00  --sat_epr_types                         true
% 3.02/1.00  --sat_non_cyclic_types                  false
% 3.02/1.00  --sat_finite_models                     false
% 3.02/1.00  --sat_fm_lemmas                         false
% 3.02/1.00  --sat_fm_prep                           false
% 3.02/1.00  --sat_fm_uc_incr                        true
% 3.02/1.00  --sat_out_model                         small
% 3.02/1.00  --sat_out_clauses                       false
% 3.02/1.00  
% 3.02/1.00  ------ QBF Options
% 3.02/1.00  
% 3.02/1.00  --qbf_mode                              false
% 3.02/1.00  --qbf_elim_univ                         false
% 3.02/1.00  --qbf_dom_inst                          none
% 3.02/1.00  --qbf_dom_pre_inst                      false
% 3.02/1.00  --qbf_sk_in                             false
% 3.02/1.00  --qbf_pred_elim                         true
% 3.02/1.00  --qbf_split                             512
% 3.02/1.00  
% 3.02/1.00  ------ BMC1 Options
% 3.02/1.00  
% 3.02/1.00  --bmc1_incremental                      false
% 3.02/1.00  --bmc1_axioms                           reachable_all
% 3.02/1.00  --bmc1_min_bound                        0
% 3.02/1.00  --bmc1_max_bound                        -1
% 3.02/1.00  --bmc1_max_bound_default                -1
% 3.02/1.00  --bmc1_symbol_reachability              true
% 3.02/1.00  --bmc1_property_lemmas                  false
% 3.02/1.00  --bmc1_k_induction                      false
% 3.02/1.00  --bmc1_non_equiv_states                 false
% 3.02/1.00  --bmc1_deadlock                         false
% 3.02/1.00  --bmc1_ucm                              false
% 3.02/1.00  --bmc1_add_unsat_core                   none
% 3.02/1.00  --bmc1_unsat_core_children              false
% 3.02/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/1.00  --bmc1_out_stat                         full
% 3.02/1.00  --bmc1_ground_init                      false
% 3.02/1.00  --bmc1_pre_inst_next_state              false
% 3.02/1.00  --bmc1_pre_inst_state                   false
% 3.02/1.00  --bmc1_pre_inst_reach_state             false
% 3.02/1.00  --bmc1_out_unsat_core                   false
% 3.02/1.00  --bmc1_aig_witness_out                  false
% 3.02/1.00  --bmc1_verbose                          false
% 3.02/1.00  --bmc1_dump_clauses_tptp                false
% 3.02/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.02/1.00  --bmc1_dump_file                        -
% 3.02/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.02/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.02/1.00  --bmc1_ucm_extend_mode                  1
% 3.02/1.00  --bmc1_ucm_init_mode                    2
% 3.02/1.00  --bmc1_ucm_cone_mode                    none
% 3.02/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.02/1.00  --bmc1_ucm_relax_model                  4
% 3.02/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.02/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/1.00  --bmc1_ucm_layered_model                none
% 3.02/1.00  --bmc1_ucm_max_lemma_size               10
% 3.02/1.00  
% 3.02/1.00  ------ AIG Options
% 3.02/1.00  
% 3.02/1.00  --aig_mode                              false
% 3.02/1.00  
% 3.02/1.00  ------ Instantiation Options
% 3.02/1.00  
% 3.02/1.00  --instantiation_flag                    true
% 3.02/1.00  --inst_sos_flag                         false
% 3.02/1.00  --inst_sos_phase                        true
% 3.02/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/1.00  --inst_lit_sel_side                     num_symb
% 3.02/1.00  --inst_solver_per_active                1400
% 3.02/1.00  --inst_solver_calls_frac                1.
% 3.02/1.00  --inst_passive_queue_type               priority_queues
% 3.02/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/1.00  --inst_passive_queues_freq              [25;2]
% 3.02/1.00  --inst_dismatching                      true
% 3.02/1.00  --inst_eager_unprocessed_to_passive     true
% 3.02/1.00  --inst_prop_sim_given                   true
% 3.02/1.00  --inst_prop_sim_new                     false
% 3.02/1.00  --inst_subs_new                         false
% 3.02/1.00  --inst_eq_res_simp                      false
% 3.02/1.00  --inst_subs_given                       false
% 3.02/1.00  --inst_orphan_elimination               true
% 3.02/1.00  --inst_learning_loop_flag               true
% 3.02/1.00  --inst_learning_start                   3000
% 3.02/1.00  --inst_learning_factor                  2
% 3.02/1.00  --inst_start_prop_sim_after_learn       3
% 3.02/1.00  --inst_sel_renew                        solver
% 3.02/1.00  --inst_lit_activity_flag                true
% 3.02/1.00  --inst_restr_to_given                   false
% 3.02/1.00  --inst_activity_threshold               500
% 3.02/1.00  --inst_out_proof                        true
% 3.02/1.00  
% 3.02/1.00  ------ Resolution Options
% 3.02/1.00  
% 3.02/1.00  --resolution_flag                       true
% 3.02/1.00  --res_lit_sel                           adaptive
% 3.02/1.00  --res_lit_sel_side                      none
% 3.02/1.00  --res_ordering                          kbo
% 3.02/1.00  --res_to_prop_solver                    active
% 3.02/1.00  --res_prop_simpl_new                    false
% 3.02/1.00  --res_prop_simpl_given                  true
% 3.02/1.00  --res_passive_queue_type                priority_queues
% 3.02/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/1.00  --res_passive_queues_freq               [15;5]
% 3.02/1.00  --res_forward_subs                      full
% 3.02/1.00  --res_backward_subs                     full
% 3.02/1.00  --res_forward_subs_resolution           true
% 3.02/1.00  --res_backward_subs_resolution          true
% 3.02/1.00  --res_orphan_elimination                true
% 3.02/1.00  --res_time_limit                        2.
% 3.02/1.00  --res_out_proof                         true
% 3.02/1.00  
% 3.02/1.00  ------ Superposition Options
% 3.02/1.00  
% 3.02/1.00  --superposition_flag                    true
% 3.02/1.00  --sup_passive_queue_type                priority_queues
% 3.02/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.02/1.00  --demod_completeness_check              fast
% 3.02/1.00  --demod_use_ground                      true
% 3.02/1.00  --sup_to_prop_solver                    passive
% 3.02/1.00  --sup_prop_simpl_new                    true
% 3.02/1.00  --sup_prop_simpl_given                  true
% 3.02/1.00  --sup_fun_splitting                     false
% 3.02/1.00  --sup_smt_interval                      50000
% 3.02/1.00  
% 3.02/1.00  ------ Superposition Simplification Setup
% 3.02/1.00  
% 3.02/1.00  --sup_indices_passive                   []
% 3.02/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_full_bw                           [BwDemod]
% 3.02/1.00  --sup_immed_triv                        [TrivRules]
% 3.02/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_immed_bw_main                     []
% 3.02/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.00  
% 3.02/1.00  ------ Combination Options
% 3.02/1.00  
% 3.02/1.00  --comb_res_mult                         3
% 3.02/1.00  --comb_sup_mult                         2
% 3.02/1.00  --comb_inst_mult                        10
% 3.02/1.00  
% 3.02/1.00  ------ Debug Options
% 3.02/1.00  
% 3.02/1.00  --dbg_backtrace                         false
% 3.02/1.00  --dbg_dump_prop_clauses                 false
% 3.02/1.00  --dbg_dump_prop_clauses_file            -
% 3.02/1.00  --dbg_out_stat                          false
% 3.02/1.00  ------ Parsing...
% 3.02/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing... sf_s  rm: 2 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.02/1.00  ------ Proving...
% 3.02/1.00  ------ Problem Properties 
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  clauses                                 29
% 3.02/1.00  conjectures                             5
% 3.02/1.00  EPR                                     2
% 3.02/1.00  Horn                                    29
% 3.02/1.00  unary                                   10
% 3.02/1.00  binary                                  1
% 3.02/1.00  lits                                    106
% 3.02/1.00  lits eq                                 25
% 3.02/1.00  fd_pure                                 0
% 3.02/1.00  fd_pseudo                               0
% 3.02/1.00  fd_cond                                 0
% 3.02/1.00  fd_pseudo_cond                          0
% 3.02/1.00  AC symbols                              0
% 3.02/1.00  
% 3.02/1.00  ------ Schedule dynamic 5 is on 
% 3.02/1.00  
% 3.02/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  ------ 
% 3.02/1.00  Current options:
% 3.02/1.00  ------ 
% 3.02/1.00  
% 3.02/1.00  ------ Input Options
% 3.02/1.00  
% 3.02/1.00  --out_options                           all
% 3.02/1.00  --tptp_safe_out                         true
% 3.02/1.00  --problem_path                          ""
% 3.02/1.00  --include_path                          ""
% 3.02/1.00  --clausifier                            res/vclausify_rel
% 3.02/1.00  --clausifier_options                    --mode clausify
% 3.02/1.00  --stdin                                 false
% 3.02/1.00  --stats_out                             all
% 3.02/1.00  
% 3.02/1.00  ------ General Options
% 3.02/1.00  
% 3.02/1.00  --fof                                   false
% 3.02/1.00  --time_out_real                         305.
% 3.02/1.00  --time_out_virtual                      -1.
% 3.02/1.00  --symbol_type_check                     false
% 3.02/1.00  --clausify_out                          false
% 3.02/1.00  --sig_cnt_out                           false
% 3.02/1.00  --trig_cnt_out                          false
% 3.02/1.00  --trig_cnt_out_tolerance                1.
% 3.02/1.00  --trig_cnt_out_sk_spl                   false
% 3.02/1.00  --abstr_cl_out                          false
% 3.02/1.00  
% 3.02/1.00  ------ Global Options
% 3.02/1.00  
% 3.02/1.00  --schedule                              default
% 3.02/1.00  --add_important_lit                     false
% 3.02/1.00  --prop_solver_per_cl                    1000
% 3.02/1.00  --min_unsat_core                        false
% 3.02/1.00  --soft_assumptions                      false
% 3.02/1.00  --soft_lemma_size                       3
% 3.02/1.00  --prop_impl_unit_size                   0
% 3.02/1.00  --prop_impl_unit                        []
% 3.02/1.00  --share_sel_clauses                     true
% 3.02/1.00  --reset_solvers                         false
% 3.02/1.00  --bc_imp_inh                            [conj_cone]
% 3.02/1.00  --conj_cone_tolerance                   3.
% 3.02/1.00  --extra_neg_conj                        none
% 3.02/1.00  --large_theory_mode                     true
% 3.02/1.00  --prolific_symb_bound                   200
% 3.02/1.00  --lt_threshold                          2000
% 3.02/1.00  --clause_weak_htbl                      true
% 3.02/1.00  --gc_record_bc_elim                     false
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing Options
% 3.02/1.00  
% 3.02/1.00  --preprocessing_flag                    true
% 3.02/1.00  --time_out_prep_mult                    0.1
% 3.02/1.00  --splitting_mode                        input
% 3.02/1.00  --splitting_grd                         true
% 3.02/1.00  --splitting_cvd                         false
% 3.02/1.00  --splitting_cvd_svl                     false
% 3.02/1.00  --splitting_nvd                         32
% 3.02/1.00  --sub_typing                            true
% 3.02/1.00  --prep_gs_sim                           true
% 3.02/1.00  --prep_unflatten                        true
% 3.02/1.00  --prep_res_sim                          true
% 3.02/1.00  --prep_upred                            true
% 3.02/1.00  --prep_sem_filter                       exhaustive
% 3.02/1.00  --prep_sem_filter_out                   false
% 3.02/1.00  --pred_elim                             true
% 3.02/1.00  --res_sim_input                         true
% 3.02/1.00  --eq_ax_congr_red                       true
% 3.02/1.00  --pure_diseq_elim                       true
% 3.02/1.00  --brand_transform                       false
% 3.02/1.00  --non_eq_to_eq                          false
% 3.02/1.00  --prep_def_merge                        true
% 3.02/1.00  --prep_def_merge_prop_impl              false
% 3.02/1.00  --prep_def_merge_mbd                    true
% 3.02/1.00  --prep_def_merge_tr_red                 false
% 3.02/1.00  --prep_def_merge_tr_cl                  false
% 3.02/1.00  --smt_preprocessing                     true
% 3.02/1.00  --smt_ac_axioms                         fast
% 3.02/1.00  --preprocessed_out                      false
% 3.02/1.00  --preprocessed_stats                    false
% 3.02/1.00  
% 3.02/1.00  ------ Abstraction refinement Options
% 3.02/1.00  
% 3.02/1.00  --abstr_ref                             []
% 3.02/1.00  --abstr_ref_prep                        false
% 3.02/1.00  --abstr_ref_until_sat                   false
% 3.02/1.00  --abstr_ref_sig_restrict                funpre
% 3.02/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.02/1.00  --abstr_ref_under                       []
% 3.02/1.00  
% 3.02/1.00  ------ SAT Options
% 3.02/1.00  
% 3.02/1.00  --sat_mode                              false
% 3.02/1.00  --sat_fm_restart_options                ""
% 3.02/1.00  --sat_gr_def                            false
% 3.02/1.00  --sat_epr_types                         true
% 3.02/1.00  --sat_non_cyclic_types                  false
% 3.02/1.00  --sat_finite_models                     false
% 3.02/1.00  --sat_fm_lemmas                         false
% 3.02/1.00  --sat_fm_prep                           false
% 3.02/1.00  --sat_fm_uc_incr                        true
% 3.02/1.00  --sat_out_model                         small
% 3.02/1.00  --sat_out_clauses                       false
% 3.02/1.00  
% 3.02/1.00  ------ QBF Options
% 3.02/1.00  
% 3.02/1.00  --qbf_mode                              false
% 3.02/1.00  --qbf_elim_univ                         false
% 3.02/1.00  --qbf_dom_inst                          none
% 3.02/1.00  --qbf_dom_pre_inst                      false
% 3.02/1.00  --qbf_sk_in                             false
% 3.02/1.00  --qbf_pred_elim                         true
% 3.02/1.00  --qbf_split                             512
% 3.02/1.00  
% 3.02/1.00  ------ BMC1 Options
% 3.02/1.00  
% 3.02/1.00  --bmc1_incremental                      false
% 3.02/1.00  --bmc1_axioms                           reachable_all
% 3.02/1.00  --bmc1_min_bound                        0
% 3.02/1.00  --bmc1_max_bound                        -1
% 3.02/1.00  --bmc1_max_bound_default                -1
% 3.02/1.00  --bmc1_symbol_reachability              true
% 3.02/1.00  --bmc1_property_lemmas                  false
% 3.02/1.00  --bmc1_k_induction                      false
% 3.02/1.00  --bmc1_non_equiv_states                 false
% 3.02/1.00  --bmc1_deadlock                         false
% 3.02/1.00  --bmc1_ucm                              false
% 3.02/1.00  --bmc1_add_unsat_core                   none
% 3.02/1.00  --bmc1_unsat_core_children              false
% 3.02/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.02/1.00  --bmc1_out_stat                         full
% 3.02/1.00  --bmc1_ground_init                      false
% 3.02/1.00  --bmc1_pre_inst_next_state              false
% 3.02/1.00  --bmc1_pre_inst_state                   false
% 3.02/1.00  --bmc1_pre_inst_reach_state             false
% 3.02/1.00  --bmc1_out_unsat_core                   false
% 3.02/1.00  --bmc1_aig_witness_out                  false
% 3.02/1.00  --bmc1_verbose                          false
% 3.02/1.00  --bmc1_dump_clauses_tptp                false
% 3.02/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.02/1.00  --bmc1_dump_file                        -
% 3.02/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.02/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.02/1.00  --bmc1_ucm_extend_mode                  1
% 3.02/1.00  --bmc1_ucm_init_mode                    2
% 3.02/1.00  --bmc1_ucm_cone_mode                    none
% 3.02/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.02/1.00  --bmc1_ucm_relax_model                  4
% 3.02/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.02/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.02/1.00  --bmc1_ucm_layered_model                none
% 3.02/1.00  --bmc1_ucm_max_lemma_size               10
% 3.02/1.00  
% 3.02/1.00  ------ AIG Options
% 3.02/1.00  
% 3.02/1.00  --aig_mode                              false
% 3.02/1.00  
% 3.02/1.00  ------ Instantiation Options
% 3.02/1.00  
% 3.02/1.00  --instantiation_flag                    true
% 3.02/1.00  --inst_sos_flag                         false
% 3.02/1.00  --inst_sos_phase                        true
% 3.02/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.02/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.02/1.00  --inst_lit_sel_side                     none
% 3.02/1.00  --inst_solver_per_active                1400
% 3.02/1.00  --inst_solver_calls_frac                1.
% 3.02/1.00  --inst_passive_queue_type               priority_queues
% 3.02/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.02/1.00  --inst_passive_queues_freq              [25;2]
% 3.02/1.00  --inst_dismatching                      true
% 3.02/1.00  --inst_eager_unprocessed_to_passive     true
% 3.02/1.00  --inst_prop_sim_given                   true
% 3.02/1.00  --inst_prop_sim_new                     false
% 3.02/1.00  --inst_subs_new                         false
% 3.02/1.00  --inst_eq_res_simp                      false
% 3.02/1.00  --inst_subs_given                       false
% 3.02/1.00  --inst_orphan_elimination               true
% 3.02/1.00  --inst_learning_loop_flag               true
% 3.02/1.00  --inst_learning_start                   3000
% 3.02/1.00  --inst_learning_factor                  2
% 3.02/1.00  --inst_start_prop_sim_after_learn       3
% 3.02/1.00  --inst_sel_renew                        solver
% 3.02/1.00  --inst_lit_activity_flag                true
% 3.02/1.00  --inst_restr_to_given                   false
% 3.02/1.00  --inst_activity_threshold               500
% 3.02/1.00  --inst_out_proof                        true
% 3.02/1.00  
% 3.02/1.00  ------ Resolution Options
% 3.02/1.00  
% 3.02/1.00  --resolution_flag                       false
% 3.02/1.00  --res_lit_sel                           adaptive
% 3.02/1.00  --res_lit_sel_side                      none
% 3.02/1.00  --res_ordering                          kbo
% 3.02/1.00  --res_to_prop_solver                    active
% 3.02/1.00  --res_prop_simpl_new                    false
% 3.02/1.00  --res_prop_simpl_given                  true
% 3.02/1.00  --res_passive_queue_type                priority_queues
% 3.02/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.02/1.00  --res_passive_queues_freq               [15;5]
% 3.02/1.00  --res_forward_subs                      full
% 3.02/1.00  --res_backward_subs                     full
% 3.02/1.00  --res_forward_subs_resolution           true
% 3.02/1.00  --res_backward_subs_resolution          true
% 3.02/1.00  --res_orphan_elimination                true
% 3.02/1.00  --res_time_limit                        2.
% 3.02/1.00  --res_out_proof                         true
% 3.02/1.00  
% 3.02/1.00  ------ Superposition Options
% 3.02/1.00  
% 3.02/1.00  --superposition_flag                    true
% 3.02/1.00  --sup_passive_queue_type                priority_queues
% 3.02/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.02/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.02/1.00  --demod_completeness_check              fast
% 3.02/1.00  --demod_use_ground                      true
% 3.02/1.00  --sup_to_prop_solver                    passive
% 3.02/1.00  --sup_prop_simpl_new                    true
% 3.02/1.00  --sup_prop_simpl_given                  true
% 3.02/1.00  --sup_fun_splitting                     false
% 3.02/1.00  --sup_smt_interval                      50000
% 3.02/1.00  
% 3.02/1.00  ------ Superposition Simplification Setup
% 3.02/1.00  
% 3.02/1.00  --sup_indices_passive                   []
% 3.02/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.02/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.02/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_full_bw                           [BwDemod]
% 3.02/1.00  --sup_immed_triv                        [TrivRules]
% 3.02/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.02/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_immed_bw_main                     []
% 3.02/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.02/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.02/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.02/1.00  
% 3.02/1.00  ------ Combination Options
% 3.02/1.00  
% 3.02/1.00  --comb_res_mult                         3
% 3.02/1.00  --comb_sup_mult                         2
% 3.02/1.00  --comb_inst_mult                        10
% 3.02/1.00  
% 3.02/1.00  ------ Debug Options
% 3.02/1.00  
% 3.02/1.00  --dbg_backtrace                         false
% 3.02/1.00  --dbg_dump_prop_clauses                 false
% 3.02/1.00  --dbg_dump_prop_clauses_file            -
% 3.02/1.00  --dbg_out_stat                          false
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  ------ Proving...
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  % SZS status Theorem for theBenchmark.p
% 3.02/1.00  
% 3.02/1.00   Resolution empty clause
% 3.02/1.00  
% 3.02/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.02/1.00  
% 3.02/1.00  fof(f14,conjecture,(
% 3.02/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f15,negated_conjecture,(
% 3.02/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.02/1.00    inference(negated_conjecture,[],[f14])).
% 3.02/1.00  
% 3.02/1.00  fof(f35,plain,(
% 3.02/1.00    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f15])).
% 3.02/1.00  
% 3.02/1.00  fof(f36,plain,(
% 3.02/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.02/1.00    inference(flattening,[],[f35])).
% 3.02/1.00  
% 3.02/1.00  fof(f39,plain,(
% 3.02/1.00    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.02/1.00    introduced(choice_axiom,[])).
% 3.02/1.00  
% 3.02/1.00  fof(f38,plain,(
% 3.02/1.00    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.02/1.00    introduced(choice_axiom,[])).
% 3.02/1.00  
% 3.02/1.00  fof(f37,plain,(
% 3.02/1.00    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.02/1.00    introduced(choice_axiom,[])).
% 3.02/1.00  
% 3.02/1.00  fof(f40,plain,(
% 3.02/1.00    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.02/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f36,f39,f38,f37])).
% 3.02/1.00  
% 3.02/1.00  fof(f66,plain,(
% 3.02/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.02/1.00    inference(cnf_transformation,[],[f40])).
% 3.02/1.00  
% 3.02/1.00  fof(f11,axiom,(
% 3.02/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f30,plain,(
% 3.02/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f11])).
% 3.02/1.00  
% 3.02/1.00  fof(f57,plain,(
% 3.02/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f30])).
% 3.02/1.00  
% 3.02/1.00  fof(f61,plain,(
% 3.02/1.00    l1_struct_0(sK0)),
% 3.02/1.00    inference(cnf_transformation,[],[f40])).
% 3.02/1.00  
% 3.02/1.00  fof(f63,plain,(
% 3.02/1.00    l1_struct_0(sK1)),
% 3.02/1.00    inference(cnf_transformation,[],[f40])).
% 3.02/1.00  
% 3.02/1.00  fof(f8,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f25,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.02/1.00    inference(ennf_transformation,[],[f8])).
% 3.02/1.00  
% 3.02/1.00  fof(f52,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f25])).
% 3.02/1.00  
% 3.02/1.00  fof(f67,plain,(
% 3.02/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.02/1.00    inference(cnf_transformation,[],[f40])).
% 3.02/1.00  
% 3.02/1.00  fof(f10,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f28,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.02/1.00    inference(ennf_transformation,[],[f10])).
% 3.02/1.00  
% 3.02/1.00  fof(f29,plain,(
% 3.02/1.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.02/1.00    inference(flattening,[],[f28])).
% 3.02/1.00  
% 3.02/1.00  fof(f56,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f29])).
% 3.02/1.00  
% 3.02/1.00  fof(f64,plain,(
% 3.02/1.00    v1_funct_1(sK2)),
% 3.02/1.00    inference(cnf_transformation,[],[f40])).
% 3.02/1.00  
% 3.02/1.00  fof(f68,plain,(
% 3.02/1.00    v2_funct_1(sK2)),
% 3.02/1.00    inference(cnf_transformation,[],[f40])).
% 3.02/1.00  
% 3.02/1.00  fof(f65,plain,(
% 3.02/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.02/1.00    inference(cnf_transformation,[],[f40])).
% 3.02/1.00  
% 3.02/1.00  fof(f5,axiom,(
% 3.02/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f19,plain,(
% 3.02/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/1.00    inference(ennf_transformation,[],[f5])).
% 3.02/1.00  
% 3.02/1.00  fof(f20,plain,(
% 3.02/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(flattening,[],[f19])).
% 3.02/1.00  
% 3.02/1.00  fof(f48,plain,(
% 3.02/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f20])).
% 3.02/1.00  
% 3.02/1.00  fof(f1,axiom,(
% 3.02/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f16,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f1])).
% 3.02/1.00  
% 3.02/1.00  fof(f41,plain,(
% 3.02/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f16])).
% 3.02/1.00  
% 3.02/1.00  fof(f2,axiom,(
% 3.02/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f42,plain,(
% 3.02/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f2])).
% 3.02/1.00  
% 3.02/1.00  fof(f12,axiom,(
% 3.02/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f31,plain,(
% 3.02/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.02/1.00    inference(ennf_transformation,[],[f12])).
% 3.02/1.00  
% 3.02/1.00  fof(f32,plain,(
% 3.02/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.02/1.00    inference(flattening,[],[f31])).
% 3.02/1.00  
% 3.02/1.00  fof(f58,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f32])).
% 3.02/1.00  
% 3.02/1.00  fof(f13,axiom,(
% 3.02/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f33,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : (! [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 3.02/1.00    inference(ennf_transformation,[],[f13])).
% 3.02/1.00  
% 3.02/1.00  fof(f34,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : (! [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 3.02/1.00    inference(flattening,[],[f33])).
% 3.02/1.00  
% 3.02/1.00  fof(f60,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f34])).
% 3.02/1.00  
% 3.02/1.00  fof(f62,plain,(
% 3.02/1.00    ~v2_struct_0(sK1)),
% 3.02/1.00    inference(cnf_transformation,[],[f40])).
% 3.02/1.00  
% 3.02/1.00  fof(f9,axiom,(
% 3.02/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f26,plain,(
% 3.02/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.02/1.00    inference(ennf_transformation,[],[f9])).
% 3.02/1.00  
% 3.02/1.00  fof(f27,plain,(
% 3.02/1.00    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.02/1.00    inference(flattening,[],[f26])).
% 3.02/1.00  
% 3.02/1.00  fof(f53,plain,(
% 3.02/1.00    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f27])).
% 3.02/1.00  
% 3.02/1.00  fof(f69,plain,(
% 3.02/1.00    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.02/1.00    inference(cnf_transformation,[],[f40])).
% 3.02/1.00  
% 3.02/1.00  fof(f7,axiom,(
% 3.02/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f23,plain,(
% 3.02/1.00    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/1.00    inference(ennf_transformation,[],[f7])).
% 3.02/1.00  
% 3.02/1.00  fof(f24,plain,(
% 3.02/1.00    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(flattening,[],[f23])).
% 3.02/1.00  
% 3.02/1.00  fof(f51,plain,(
% 3.02/1.00    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f24])).
% 3.02/1.00  
% 3.02/1.00  fof(f54,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f29])).
% 3.02/1.00  
% 3.02/1.00  fof(f55,plain,(
% 3.02/1.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f29])).
% 3.02/1.00  
% 3.02/1.00  fof(f47,plain,(
% 3.02/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f20])).
% 3.02/1.00  
% 3.02/1.00  fof(f4,axiom,(
% 3.02/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f17,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/1.00    inference(ennf_transformation,[],[f4])).
% 3.02/1.00  
% 3.02/1.00  fof(f18,plain,(
% 3.02/1.00    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(flattening,[],[f17])).
% 3.02/1.00  
% 3.02/1.00  fof(f46,plain,(
% 3.02/1.00    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f18])).
% 3.02/1.00  
% 3.02/1.00  fof(f6,axiom,(
% 3.02/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f21,plain,(
% 3.02/1.00    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.02/1.00    inference(ennf_transformation,[],[f6])).
% 3.02/1.00  
% 3.02/1.00  fof(f22,plain,(
% 3.02/1.00    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.02/1.00    inference(flattening,[],[f21])).
% 3.02/1.00  
% 3.02/1.00  fof(f49,plain,(
% 3.02/1.00    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.02/1.00    inference(cnf_transformation,[],[f22])).
% 3.02/1.00  
% 3.02/1.00  fof(f3,axiom,(
% 3.02/1.00    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 3.02/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.02/1.00  
% 3.02/1.00  fof(f44,plain,(
% 3.02/1.00    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 3.02/1.00    inference(cnf_transformation,[],[f3])).
% 3.02/1.00  
% 3.02/1.00  cnf(c_23,negated_conjecture,
% 3.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.02/1.00      inference(cnf_transformation,[],[f66]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_743,negated_conjecture,
% 3.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_23]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1288,plain,
% 3.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_16,plain,
% 3.02/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f57]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_28,negated_conjecture,
% 3.02/1.00      ( l1_struct_0(sK0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_528,plain,
% 3.02/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_28]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_529,plain,
% 3.02/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_528]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_734,plain,
% 3.02/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_529]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_26,negated_conjecture,
% 3.02/1.00      ( l1_struct_0(sK1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_523,plain,
% 3.02/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_26]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_524,plain,
% 3.02/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_523]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_735,plain,
% 3.02/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_524]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1317,plain,
% 3.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_1288,c_734,c_735]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_11,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f52]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_750,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.02/1.00      | k2_relset_1(X0_51,X1_51,X0_53) = k2_relat_1(X0_53) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_11]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1282,plain,
% 3.02/1.00      ( k2_relset_1(X0_51,X1_51,X0_53) = k2_relat_1(X0_53)
% 3.02/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_750]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1779,plain,
% 3.02/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1317,c_1282]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_22,negated_conjecture,
% 3.02/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f67]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_744,negated_conjecture,
% 3.02/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_22]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1314,plain,
% 3.02/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_744,c_734,c_735]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1947,plain,
% 3.02/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_1779,c_1314]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1988,plain,
% 3.02/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_1947,c_1779]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_13,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.02/1.00      inference(cnf_transformation,[],[f56]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_749,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0_53,X0_51,X1_51)
% 3.02/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.02/1.00      | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51)))
% 3.02/1.00      | ~ v1_funct_1(X0_53)
% 3.02/1.00      | ~ v2_funct_1(X0_53)
% 3.02/1.00      | k2_relset_1(X0_51,X1_51,X0_53) != X1_51 ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_13]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1283,plain,
% 3.02/1.00      ( k2_relset_1(X0_51,X1_51,X0_53) != X1_51
% 3.02/1.00      | v1_funct_2(X0_53,X0_51,X1_51) != iProver_top
% 3.02/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.02/1.00      | m1_subset_1(k2_funct_1(X0_53),k1_zfmisc_1(k2_zfmisc_1(X1_51,X0_51))) = iProver_top
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v2_funct_1(X0_53) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_749]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3236,plain,
% 3.02/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 3.02/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.02/1.00      | v1_funct_1(sK2) != iProver_top
% 3.02/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1988,c_1283]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_25,negated_conjecture,
% 3.02/1.00      ( v1_funct_1(sK2) ),
% 3.02/1.00      inference(cnf_transformation,[],[f64]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_32,plain,
% 3.02/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_21,negated_conjecture,
% 3.02/1.00      ( v2_funct_1(sK2) ),
% 3.02/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_35,plain,
% 3.02/1.00      ( v2_funct_1(sK2) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1995,plain,
% 3.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_1947,c_1317]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_24,negated_conjecture,
% 3.02/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f65]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_742,negated_conjecture,
% 3.02/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_24]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1289,plain,
% 3.02/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_742]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1311,plain,
% 3.02/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_1289,c_734,c_735]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1996,plain,
% 3.02/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_1947,c_1311]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4119,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_3236,c_32,c_35,c_1995,c_1996]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4124,plain,
% 3.02/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_4119,c_1282]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_741,negated_conjecture,
% 3.02/1.00      ( v1_funct_1(sK2) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_25]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1290,plain,
% 3.02/1.00      ( v1_funct_1(sK2) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_741]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_6,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f48]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_755,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0_53)
% 3.02/1.00      | ~ v2_funct_1(X0_53)
% 3.02/1.00      | ~ v1_relat_1(X0_53)
% 3.02/1.00      | k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_6]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1277,plain,
% 3.02/1.00      ( k2_relat_1(k2_funct_1(X0_53)) = k1_relat_1(X0_53)
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v2_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_755]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2102,plain,
% 3.02/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.02/1.00      | v2_funct_1(sK2) != iProver_top
% 3.02/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1290,c_1277]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_817,plain,
% 3.02/1.00      ( ~ v1_funct_1(sK2)
% 3.02/1.00      | ~ v2_funct_1(sK2)
% 3.02/1.00      | ~ v1_relat_1(sK2)
% 3.02/1.00      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_755]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_0,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f41]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_761,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(X1_53))
% 3.02/1.00      | ~ v1_relat_1(X1_53)
% 3.02/1.00      | v1_relat_1(X0_53) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_0]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1586,plain,
% 3.02/1.00      ( ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.02/1.00      | v1_relat_1(X0_53)
% 3.02/1.00      | ~ v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_761]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1757,plain,
% 3.02/1.00      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/1.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 3.02/1.00      | v1_relat_1(sK2) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_1586]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f42]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_760,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(X0_51,X1_51)) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_1]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1788,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_760]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2408,plain,
% 3.02/1.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2102,c_25,c_23,c_21,c_817,c_1757,c_1788]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_17,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.02/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.02/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_746,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0_53,X0_51,X1_51)
% 3.02/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.02/1.00      | ~ v1_funct_1(X0_53)
% 3.02/1.00      | ~ v2_funct_1(X0_53)
% 3.02/1.00      | k2_tops_2(X0_51,X1_51,X0_53) = k2_funct_1(X0_53)
% 3.02/1.00      | k2_relset_1(X0_51,X1_51,X0_53) != X1_51 ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_17]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1286,plain,
% 3.02/1.00      ( k2_tops_2(X0_51,X1_51,X0_53) = k2_funct_1(X0_53)
% 3.02/1.00      | k2_relset_1(X0_51,X1_51,X0_53) != X1_51
% 3.02/1.00      | v1_funct_2(X0_53,X0_51,X1_51) != iProver_top
% 3.02/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v2_funct_1(X0_53) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_746]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2836,plain,
% 3.02/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 3.02/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.02/1.00      | v1_funct_1(sK2) != iProver_top
% 3.02/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1988,c_1286]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3486,plain,
% 3.02/1.00      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2836,c_32,c_35,c_1995,c_1996]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_18,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.02/1.00      | v2_struct_0(X2)
% 3.02/1.00      | ~ l1_struct_0(X1)
% 3.02/1.00      | ~ l1_struct_0(X2)
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.02/1.00      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_27,negated_conjecture,
% 3.02/1.00      ( ~ v2_struct_0(sK1) ),
% 3.02/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_380,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(X2))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X2))))
% 3.02/1.00      | ~ l1_struct_0(X1)
% 3.02/1.00      | ~ l1_struct_0(X2)
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(X2),X0) != k2_struct_0(X2)
% 3.02/1.00      | k2_relset_1(u1_struct_0(X2),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X2),X0)) = k2_struct_0(X1)
% 3.02/1.00      | sK1 != X2 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_18,c_27]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_381,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.02/1.00      | ~ l1_struct_0(X1)
% 3.02/1.00      | ~ l1_struct_0(sK1)
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_380]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_385,plain,
% 3.02/1.00      ( ~ l1_struct_0(X1)
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.02/1.00      | ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 3.02/1.00      inference(global_propositional_subsumption,[status(thm)],[c_381,c_26]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_386,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.02/1.00      | ~ l1_struct_0(X1)
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1) ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_385]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_475,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,u1_struct_0(X1),u1_struct_0(sK1))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(sK1))))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | k2_relset_1(u1_struct_0(X1),u1_struct_0(sK1),X0) != k2_struct_0(sK1)
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK1),X0)) = k2_struct_0(X1)
% 3.02/1.00      | sK0 != X1 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_386,c_28]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_476,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0)) = k2_struct_0(sK0)
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0) != k2_struct_0(sK1) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_475]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_737,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/1.00      | ~ v1_funct_1(X0_53)
% 3.02/1.00      | ~ v2_funct_1(X0_53)
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_53)) = k2_struct_0(sK0)
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_53) != k2_struct_0(sK1) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_476]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1295,plain,
% 3.02/1.00      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X0_53)) = k2_struct_0(sK0)
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X0_53) != k2_struct_0(sK1)
% 3.02/1.00      | v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.02/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v2_funct_1(X0_53) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_737]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1481,plain,
% 3.02/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_53)) = k2_struct_0(sK0)
% 3.02/1.00      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_53) != k2_struct_0(sK1)
% 3.02/1.00      | v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.02/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v2_funct_1(X0_53) != iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_1295,c_734,c_735]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1835,plain,
% 3.02/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 3.02/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.02/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.02/1.00      | v1_funct_1(sK2) != iProver_top
% 3.02/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1314,c_1481]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1529,plain,
% 3.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
% 3.02/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1317]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1536,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1))
% 3.02/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
% 3.02/1.00      | ~ v1_funct_1(X0_53)
% 3.02/1.00      | ~ v2_funct_1(X0_53)
% 3.02/1.00      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),X0_53)) = k2_struct_0(sK0)
% 3.02/1.00      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),X0_53) != k2_struct_0(sK1) ),
% 3.02/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1481]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1538,plain,
% 3.02/1.00      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
% 3.02/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
% 3.02/1.00      | ~ v1_funct_1(sK2)
% 3.02/1.00      | ~ v2_funct_1(sK2)
% 3.02/1.00      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0)
% 3.02/1.00      | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_struct_0(sK1) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_1536]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1546,plain,
% 3.02/1.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
% 3.02/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1311]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1881,plain,
% 3.02/1.00      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) = k2_struct_0(sK0) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_1835,c_25,c_21,c_1529,c_1538,c_1546,c_1314]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1991,plain,
% 3.02/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) = k2_struct_0(sK0) ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_1947,c_1881]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3489,plain,
% 3.02/1.00      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_struct_0(sK0) ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_3486,c_1991]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4131,plain,
% 3.02/1.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_4124,c_2408,c_3489]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_12,plain,
% 3.02/1.00      ( r2_funct_2(X0,X1,X2,X2)
% 3.02/1.00      | ~ v1_funct_2(X3,X0,X1)
% 3.02/1.00      | ~ v1_funct_2(X2,X0,X1)
% 3.02/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.02/1.00      | ~ v1_funct_1(X3)
% 3.02/1.00      | ~ v1_funct_1(X2) ),
% 3.02/1.00      inference(cnf_transformation,[],[f53]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_20,negated_conjecture,
% 3.02/1.00      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.02/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_314,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.00      | ~ v1_funct_2(X3,X1,X2)
% 3.02/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_funct_1(X3)
% 3.02/1.00      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X3
% 3.02/1.00      | u1_struct_0(sK1) != X2
% 3.02/1.00      | u1_struct_0(sK0) != X1
% 3.02/1.00      | sK2 != X3 ),
% 3.02/1.00      inference(resolution_lifted,[status(thm)],[c_12,c_20]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_315,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.02/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.02/1.00      inference(unflattening,[status(thm)],[c_314]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_740,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/1.00      | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/1.00      | ~ v1_funct_1(X0_53)
% 3.02/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.02/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_315]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_763,plain,
% 3.02/1.00      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/1.00      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/1.00      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.02/1.00      | sP0_iProver_split
% 3.02/1.00      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.02/1.00      inference(splitting,
% 3.02/1.00                [splitting(split),new_symbols(definition,[])],
% 3.02/1.00                [c_740]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1291,plain,
% 3.02/1.00      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.02/1.00      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.02/1.00      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top
% 3.02/1.00      | sP0_iProver_split = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_763]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1507,plain,
% 3.02/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.02/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.02/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top
% 3.02/1.00      | sP0_iProver_split = iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_1291,c_734,c_735]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_762,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/1.00      | ~ v1_funct_1(X0_53)
% 3.02/1.00      | ~ sP0_iProver_split ),
% 3.02/1.00      inference(splitting,
% 3.02/1.00                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.02/1.00                [c_740]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1292,plain,
% 3.02/1.00      ( v1_funct_2(X0_53,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.02/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | sP0_iProver_split != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_762]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1370,plain,
% 3.02/1.00      ( v1_funct_2(X0_53,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.02/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | sP0_iProver_split != iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_1292,c_734,c_735]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1513,plain,
% 3.02/1.00      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.02/1.00      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.02/1.00      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.02/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_1507,c_1370]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3949,plain,
% 3.02/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 3.02/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_1513,c_1947,c_3486]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4148,plain,
% 3.02/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 3.02/1.00      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.02/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_4131,c_3949]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3957,plain,
% 3.02/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
% 3.02/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.02/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_3489,c_1286]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_10,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 3.02/1.00      inference(cnf_transformation,[],[f51]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_751,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0_53)
% 3.02/1.00      | ~ v2_funct_1(X0_53)
% 3.02/1.00      | ~ v1_relat_1(X0_53)
% 3.02/1.00      | k2_funct_1(k2_funct_1(X0_53)) = X0_53 ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_10]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1281,plain,
% 3.02/1.00      ( k2_funct_1(k2_funct_1(X0_53)) = X0_53
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v2_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_751]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2095,plain,
% 3.02/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.02/1.00      | v2_funct_1(sK2) != iProver_top
% 3.02/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1290,c_1281]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_829,plain,
% 3.02/1.00      ( ~ v1_funct_1(sK2)
% 3.02/1.00      | ~ v2_funct_1(sK2)
% 3.02/1.00      | ~ v1_relat_1(sK2)
% 3.02/1.00      | k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_751]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2302,plain,
% 3.02/1.00      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2095,c_25,c_23,c_21,c_829,c_1757,c_1788]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3977,plain,
% 3.02/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2
% 3.02/1.00      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) != iProver_top
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.02/1.00      | v2_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_3957,c_2302]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_33,plain,
% 3.02/1.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_34,plain,
% 3.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_15,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.02/1.00      inference(cnf_transformation,[],[f54]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_747,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0_53,X0_51,X1_51)
% 3.02/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.02/1.00      | ~ v1_funct_1(X0_53)
% 3.02/1.00      | v1_funct_1(k2_funct_1(X0_53))
% 3.02/1.00      | ~ v2_funct_1(X0_53)
% 3.02/1.00      | k2_relset_1(X0_51,X1_51,X0_53) != X1_51 ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_15]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1652,plain,
% 3.02/1.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK2))
% 3.02/1.00      | ~ v1_funct_1(sK2)
% 3.02/1.00      | ~ v2_funct_1(sK2)
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_747]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1653,plain,
% 3.02/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 3.02/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.02/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.02/1.00      | v1_funct_1(sK2) != iProver_top
% 3.02/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1652]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_768,plain,
% 3.02/1.00      ( X0_51 != X1_51 | X2_51 != X1_51 | X2_51 = X0_51 ),
% 3.02/1.00      theory(equality) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1707,plain,
% 3.02/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0_51
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 3.02/1.00      | u1_struct_0(sK1) != X0_51 ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_768]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1793,plain,
% 3.02/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 3.02/1.00      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_1707]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_14,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.02/1.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.02/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.02/1.00      | ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.02/1.00      inference(cnf_transformation,[],[f55]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_748,plain,
% 3.02/1.00      ( ~ v1_funct_2(X0_53,X0_51,X1_51)
% 3.02/1.00      | v1_funct_2(k2_funct_1(X0_53),X1_51,X0_51)
% 3.02/1.00      | ~ m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51)))
% 3.02/1.00      | ~ v1_funct_1(X0_53)
% 3.02/1.00      | ~ v2_funct_1(X0_53)
% 3.02/1.00      | k2_relset_1(X0_51,X1_51,X0_53) != X1_51 ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_14]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1284,plain,
% 3.02/1.00      ( k2_relset_1(X0_51,X1_51,X0_53) != X1_51
% 3.02/1.00      | v1_funct_2(X0_53,X0_51,X1_51) != iProver_top
% 3.02/1.00      | v1_funct_2(k2_funct_1(X0_53),X1_51,X0_51) = iProver_top
% 3.02/1.00      | m1_subset_1(X0_53,k1_zfmisc_1(k2_zfmisc_1(X0_51,X1_51))) != iProver_top
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v2_funct_1(X0_53) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_748]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2786,plain,
% 3.02/1.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) = iProver_top
% 3.02/1.00      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.02/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.02/1.00      | v1_funct_1(sK2) != iProver_top
% 3.02/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1988,c_1284]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_7,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f47]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_754,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0_53)
% 3.02/1.00      | ~ v2_funct_1(X0_53)
% 3.02/1.00      | ~ v1_relat_1(X0_53)
% 3.02/1.00      | k1_relat_1(k2_funct_1(X0_53)) = k2_relat_1(X0_53) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_7]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1278,plain,
% 3.02/1.00      ( k1_relat_1(k2_funct_1(X0_53)) = k2_relat_1(X0_53)
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v2_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_754]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2194,plain,
% 3.02/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.02/1.00      | v2_funct_1(sK2) != iProver_top
% 3.02/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1290,c_1278]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_820,plain,
% 3.02/1.00      ( ~ v1_funct_1(sK2)
% 3.02/1.00      | ~ v2_funct_1(sK2)
% 3.02/1.00      | ~ v1_relat_1(sK2)
% 3.02/1.00      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_754]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2414,plain,
% 3.02/1.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2194,c_25,c_23,c_21,c_820,c_1757,c_1788]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v1_funct_1(X1)
% 3.02/1.00      | v2_funct_1(X1)
% 3.02/1.00      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 3.02/1.00      | ~ v1_relat_1(X1)
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 3.02/1.00      inference(cnf_transformation,[],[f46]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_757,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0_53)
% 3.02/1.00      | ~ v1_funct_1(X1_53)
% 3.02/1.00      | v2_funct_1(X1_53)
% 3.02/1.00      | ~ v2_funct_1(k5_relat_1(X0_53,X1_53))
% 3.02/1.00      | ~ v1_relat_1(X0_53)
% 3.02/1.00      | ~ v1_relat_1(X1_53)
% 3.02/1.00      | k1_relat_1(X1_53) != k2_relat_1(X0_53) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_4]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1275,plain,
% 3.02/1.00      ( k1_relat_1(X0_53) != k2_relat_1(X1_53)
% 3.02/1.00      | v1_funct_1(X1_53) != iProver_top
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v2_funct_1(X0_53) = iProver_top
% 3.02/1.00      | v2_funct_1(k5_relat_1(X1_53,X0_53)) != iProver_top
% 3.02/1.00      | v1_relat_1(X1_53) != iProver_top
% 3.02/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_757]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2417,plain,
% 3.02/1.00      ( k2_relat_1(X0_53) != k2_relat_1(sK2)
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.02/1.00      | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
% 3.02/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.02/1.00      | v1_relat_1(X0_53) != iProver_top
% 3.02/1.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_2414,c_1275]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1658,plain,
% 3.02/1.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.02/1.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.02/1.00      | ~ v1_funct_1(sK2)
% 3.02/1.00      | ~ v2_funct_1(sK2)
% 3.02/1.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_749]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1659,plain,
% 3.02/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 3.02/1.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.02/1.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 3.02/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.02/1.00      | v1_funct_1(sK2) != iProver_top
% 3.02/1.00      | v2_funct_1(sK2) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1658]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1864,plain,
% 3.02/1.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 3.02/1.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 3.02/1.00      | v1_relat_1(k2_funct_1(sK2)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_1586]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1868,plain,
% 3.02/1.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 3.02/1.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 3.02/1.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1864]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2663,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_760]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2664,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_2663]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3206,plain,
% 3.02/1.00      ( v1_relat_1(X0_53) != iProver_top
% 3.02/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.02/1.00      | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
% 3.02/1.00      | k2_relat_1(X0_53) != k2_relat_1(sK2)
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2417,c_32,c_33,c_34,c_35,c_744,c_735,c_1653,c_1659,c_1793,
% 3.02/1.00                 c_1868,c_2664]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3207,plain,
% 3.02/1.00      ( k2_relat_1(X0_53) != k2_relat_1(sK2)
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v2_funct_1(k5_relat_1(X0_53,k2_funct_1(sK2))) != iProver_top
% 3.02/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.02/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_3206]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3218,plain,
% 3.02/1.00      ( v1_funct_1(sK2) != iProver_top
% 3.02/1.00      | v2_funct_1(k5_relat_1(sK2,k2_funct_1(sK2))) != iProver_top
% 3.02/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.02/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.02/1.00      inference(equality_resolution,[status(thm)],[c_3207]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_9,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0)
% 3.02/1.00      | ~ v2_funct_1(X0)
% 3.02/1.00      | ~ v1_relat_1(X0)
% 3.02/1.00      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f49]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_752,plain,
% 3.02/1.00      ( ~ v1_funct_1(X0_53)
% 3.02/1.00      | ~ v2_funct_1(X0_53)
% 3.02/1.00      | ~ v1_relat_1(X0_53)
% 3.02/1.00      | k5_relat_1(X0_53,k2_funct_1(X0_53)) = k6_relat_1(k1_relat_1(X0_53)) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_9]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1280,plain,
% 3.02/1.00      ( k5_relat_1(X0_53,k2_funct_1(X0_53)) = k6_relat_1(k1_relat_1(X0_53))
% 3.02/1.00      | v1_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v2_funct_1(X0_53) != iProver_top
% 3.02/1.00      | v1_relat_1(X0_53) != iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_752]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2717,plain,
% 3.02/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
% 3.02/1.00      | v2_funct_1(sK2) != iProver_top
% 3.02/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.02/1.00      inference(superposition,[status(thm)],[c_1290,c_1280]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_826,plain,
% 3.02/1.00      ( ~ v1_funct_1(sK2)
% 3.02/1.00      | ~ v2_funct_1(sK2)
% 3.02/1.00      | ~ v1_relat_1(sK2)
% 3.02/1.00      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 3.02/1.00      inference(instantiation,[status(thm)],[c_752]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2839,plain,
% 3.02/1.00      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_2717,c_25,c_23,c_21,c_826,c_1757,c_1788]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3223,plain,
% 3.02/1.00      ( v1_funct_1(sK2) != iProver_top
% 3.02/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.02/1.00      | v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
% 3.02/1.00      | v1_relat_1(sK2) != iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_3218,c_2839]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1758,plain,
% 3.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.02/1.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 3.02/1.00      | v1_relat_1(sK2) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1757]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1789,plain,
% 3.02/1.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_1788]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3496,plain,
% 3.02/1.00      ( v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top
% 3.02/1.00      | v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_3223,c_32,c_34,c_1758,c_1789]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3497,plain,
% 3.02/1.00      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.02/1.00      | v2_funct_1(k6_relat_1(k1_relat_1(sK2))) != iProver_top ),
% 3.02/1.00      inference(renaming,[status(thm)],[c_3496]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_2,plain,
% 3.02/1.00      ( v2_funct_1(k6_relat_1(X0)) ),
% 3.02/1.00      inference(cnf_transformation,[],[f44]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_759,plain,
% 3.02/1.00      ( v2_funct_1(k6_relat_1(X0_51)) ),
% 3.02/1.00      inference(subtyping,[status(esa)],[c_2]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_1273,plain,
% 3.02/1.00      ( v2_funct_1(k6_relat_1(X0_51)) = iProver_top ),
% 3.02/1.00      inference(predicate_to_equality,[status(thm)],[c_759]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_3502,plain,
% 3.02/1.00      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.02/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_3497,c_1273]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4349,plain,
% 3.02/1.00      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = sK2 ),
% 3.02/1.00      inference(global_propositional_subsumption,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_3977,c_32,c_33,c_34,c_35,c_744,c_735,c_1653,c_1793,c_1995,
% 3.02/1.00                 c_1996,c_2786,c_3236,c_3502]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4351,plain,
% 3.02/1.00      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_4349,c_4131]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4960,plain,
% 3.02/1.00      ( v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.02/1.00      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.02/1.00      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.02/1.00      inference(global_propositional_subsumption,[status(thm)],[c_4148,c_4351]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4964,plain,
% 3.02/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.02/1.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.02/1.00      | v1_funct_1(sK2) != iProver_top ),
% 3.02/1.00      inference(light_normalisation,[status(thm)],[c_4960,c_4351]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4153,plain,
% 3.02/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_4131,c_1995]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4155,plain,
% 3.02/1.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 3.02/1.00      inference(demodulation,[status(thm)],[c_4131,c_1996]) ).
% 3.02/1.00  
% 3.02/1.00  cnf(c_4968,plain,
% 3.02/1.00      ( $false ),
% 3.02/1.00      inference(forward_subsumption_resolution,
% 3.02/1.00                [status(thm)],
% 3.02/1.00                [c_4964,c_1290,c_4153,c_4155]) ).
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.02/1.00  
% 3.02/1.00  ------                               Statistics
% 3.02/1.00  
% 3.02/1.00  ------ General
% 3.02/1.00  
% 3.02/1.00  abstr_ref_over_cycles:                  0
% 3.02/1.00  abstr_ref_under_cycles:                 0
% 3.02/1.00  gc_basic_clause_elim:                   0
% 3.02/1.00  forced_gc_time:                         0
% 3.02/1.00  parsing_time:                           0.015
% 3.02/1.00  unif_index_cands_time:                  0.
% 3.02/1.00  unif_index_add_time:                    0.
% 3.02/1.00  orderings_time:                         0.
% 3.02/1.00  out_proof_time:                         0.036
% 3.02/1.00  total_time:                             0.33
% 3.02/1.00  num_of_symbols:                         59
% 3.02/1.00  num_of_terms:                           5268
% 3.02/1.00  
% 3.02/1.00  ------ Preprocessing
% 3.02/1.00  
% 3.02/1.00  num_of_splits:                          1
% 3.02/1.00  num_of_split_atoms:                     1
% 3.02/1.00  num_of_reused_defs:                     0
% 3.02/1.00  num_eq_ax_congr_red:                    2
% 3.02/1.00  num_of_sem_filtered_clauses:            2
% 3.02/1.00  num_of_subtypes:                        4
% 3.02/1.00  monotx_restored_types:                  0
% 3.02/1.00  sat_num_of_epr_types:                   0
% 3.02/1.00  sat_num_of_non_cyclic_types:            0
% 3.02/1.00  sat_guarded_non_collapsed_types:        1
% 3.02/1.00  num_pure_diseq_elim:                    0
% 3.02/1.00  simp_replaced_by:                       0
% 3.02/1.00  res_preprocessed:                       155
% 3.02/1.00  prep_upred:                             0
% 3.02/1.00  prep_unflattend:                        11
% 3.02/1.00  smt_new_axioms:                         0
% 3.02/1.00  pred_elim_cands:                        5
% 3.02/1.00  pred_elim:                              3
% 3.02/1.00  pred_elim_cl:                           1
% 3.02/1.00  pred_elim_cycles:                       5
% 3.02/1.00  merged_defs:                            0
% 3.02/1.00  merged_defs_ncl:                        0
% 3.02/1.00  bin_hyper_res:                          0
% 3.02/1.00  prep_cycles:                            4
% 3.02/1.00  pred_elim_time:                         0.017
% 3.02/1.00  splitting_time:                         0.
% 3.02/1.00  sem_filter_time:                        0.
% 3.02/1.00  monotx_time:                            0.
% 3.02/1.00  subtype_inf_time:                       0.001
% 3.02/1.00  
% 3.02/1.00  ------ Problem properties
% 3.02/1.00  
% 3.02/1.00  clauses:                                29
% 3.02/1.00  conjectures:                            5
% 3.02/1.00  epr:                                    2
% 3.02/1.00  horn:                                   29
% 3.02/1.00  ground:                                 8
% 3.02/1.00  unary:                                  10
% 3.02/1.00  binary:                                 1
% 3.02/1.00  lits:                                   106
% 3.02/1.00  lits_eq:                                25
% 3.02/1.00  fd_pure:                                0
% 3.02/1.00  fd_pseudo:                              0
% 3.02/1.00  fd_cond:                                0
% 3.02/1.00  fd_pseudo_cond:                         0
% 3.02/1.00  ac_symbols:                             0
% 3.02/1.00  
% 3.02/1.00  ------ Propositional Solver
% 3.02/1.00  
% 3.02/1.00  prop_solver_calls:                      29
% 3.02/1.00  prop_fast_solver_calls:                 1424
% 3.02/1.00  smt_solver_calls:                       0
% 3.02/1.00  smt_fast_solver_calls:                  0
% 3.02/1.00  prop_num_of_clauses:                    1909
% 3.02/1.00  prop_preprocess_simplified:             6104
% 3.02/1.00  prop_fo_subsumed:                       67
% 3.02/1.00  prop_solver_time:                       0.
% 3.02/1.00  smt_solver_time:                        0.
% 3.02/1.00  smt_fast_solver_time:                   0.
% 3.02/1.00  prop_fast_solver_time:                  0.
% 3.02/1.00  prop_unsat_core_time:                   0.
% 3.02/1.00  
% 3.02/1.00  ------ QBF
% 3.02/1.00  
% 3.02/1.00  qbf_q_res:                              0
% 3.02/1.00  qbf_num_tautologies:                    0
% 3.02/1.00  qbf_prep_cycles:                        0
% 3.02/1.00  
% 3.02/1.00  ------ BMC1
% 3.02/1.00  
% 3.02/1.00  bmc1_current_bound:                     -1
% 3.02/1.00  bmc1_last_solved_bound:                 -1
% 3.02/1.00  bmc1_unsat_core_size:                   -1
% 3.02/1.00  bmc1_unsat_core_parents_size:           -1
% 3.02/1.00  bmc1_merge_next_fun:                    0
% 3.02/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.02/1.00  
% 3.02/1.00  ------ Instantiation
% 3.02/1.00  
% 3.02/1.00  inst_num_of_clauses:                    649
% 3.02/1.00  inst_num_in_passive:                    77
% 3.02/1.00  inst_num_in_active:                     329
% 3.02/1.00  inst_num_in_unprocessed:                243
% 3.02/1.00  inst_num_of_loops:                      360
% 3.02/1.00  inst_num_of_learning_restarts:          0
% 3.02/1.00  inst_num_moves_active_passive:          27
% 3.02/1.00  inst_lit_activity:                      0
% 3.02/1.00  inst_lit_activity_moves:                0
% 3.02/1.00  inst_num_tautologies:                   0
% 3.02/1.00  inst_num_prop_implied:                  0
% 3.02/1.00  inst_num_existing_simplified:           0
% 3.02/1.00  inst_num_eq_res_simplified:             0
% 3.02/1.00  inst_num_child_elim:                    0
% 3.02/1.00  inst_num_of_dismatching_blockings:      134
% 3.02/1.00  inst_num_of_non_proper_insts:           602
% 3.02/1.00  inst_num_of_duplicates:                 0
% 3.02/1.00  inst_inst_num_from_inst_to_res:         0
% 3.02/1.00  inst_dismatching_checking_time:         0.
% 3.02/1.00  
% 3.02/1.00  ------ Resolution
% 3.02/1.00  
% 3.02/1.00  res_num_of_clauses:                     0
% 3.02/1.00  res_num_in_passive:                     0
% 3.02/1.00  res_num_in_active:                      0
% 3.02/1.00  res_num_of_loops:                       159
% 3.02/1.00  res_forward_subset_subsumed:            67
% 3.02/1.00  res_backward_subset_subsumed:           0
% 3.02/1.00  res_forward_subsumed:                   0
% 3.02/1.00  res_backward_subsumed:                  0
% 3.02/1.00  res_forward_subsumption_resolution:     0
% 3.02/1.00  res_backward_subsumption_resolution:    0
% 3.02/1.00  res_clause_to_clause_subsumption:       130
% 3.02/1.00  res_orphan_elimination:                 0
% 3.02/1.00  res_tautology_del:                      65
% 3.02/1.00  res_num_eq_res_simplified:              0
% 3.02/1.00  res_num_sel_changes:                    0
% 3.02/1.00  res_moves_from_active_to_pass:          0
% 3.02/1.00  
% 3.02/1.00  ------ Superposition
% 3.02/1.00  
% 3.02/1.00  sup_time_total:                         0.
% 3.02/1.00  sup_time_generating:                    0.
% 3.02/1.00  sup_time_sim_full:                      0.
% 3.02/1.00  sup_time_sim_immed:                     0.
% 3.02/1.00  
% 3.02/1.00  sup_num_of_clauses:                     53
% 3.02/1.00  sup_num_in_active:                      47
% 3.02/1.00  sup_num_in_passive:                     6
% 3.02/1.00  sup_num_of_loops:                       71
% 3.02/1.00  sup_fw_superposition:                   21
% 3.02/1.00  sup_bw_superposition:                   32
% 3.02/1.00  sup_immediate_simplified:               31
% 3.02/1.00  sup_given_eliminated:                   1
% 3.02/1.00  comparisons_done:                       0
% 3.02/1.00  comparisons_avoided:                    0
% 3.02/1.00  
% 3.02/1.00  ------ Simplifications
% 3.02/1.00  
% 3.02/1.00  
% 3.02/1.00  sim_fw_subset_subsumed:                 12
% 3.02/1.00  sim_bw_subset_subsumed:                 0
% 3.02/1.00  sim_fw_subsumed:                        8
% 3.02/1.00  sim_bw_subsumed:                        0
% 3.02/1.00  sim_fw_subsumption_res:                 5
% 3.02/1.00  sim_bw_subsumption_res:                 0
% 3.02/1.00  sim_tautology_del:                      0
% 3.02/1.00  sim_eq_tautology_del:                   6
% 3.02/1.00  sim_eq_res_simp:                        0
% 3.02/1.00  sim_fw_demodulated:                     0
% 3.02/1.00  sim_bw_demodulated:                     25
% 3.02/1.00  sim_light_normalised:                   37
% 3.02/1.00  sim_joinable_taut:                      0
% 3.02/1.00  sim_joinable_simp:                      0
% 3.02/1.00  sim_ac_normalised:                      0
% 3.02/1.00  sim_smt_subsumption:                    0
% 3.02/1.00  
%------------------------------------------------------------------------------
