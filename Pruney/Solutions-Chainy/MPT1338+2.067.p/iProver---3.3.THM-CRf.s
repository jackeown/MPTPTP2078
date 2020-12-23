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
% DateTime   : Thu Dec  3 12:17:13 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :  260 (3293 expanded)
%              Number of clauses        :  157 ( 973 expanded)
%              Number of leaves         :   28 ( 957 expanded)
%              Depth                    :   20
%              Number of atoms          :  853 (22785 expanded)
%              Number of equality atoms :  360 (7663 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f24,conjecture,(
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
                  & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,negated_conjecture,(
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
                 => ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0)
                    & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f24])).

fof(f57,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f58,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f57])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
            | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
          & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
          & v1_funct_1(X2) )
     => ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0)
          | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1) )
        & v2_funct_1(sK2)
        & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
     => ( ? [X2] :
            ( ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0)
              | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1) )
            & v2_funct_1(X2)
            & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1))))
            & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1))
            & v1_funct_1(X2) )
        & l1_struct_0(sK1)
        & ~ v2_struct_0(sK1) ) ) ),
    introduced(choice_axiom,[])).

fof(f63,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0)
                  | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
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
              ( ( k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0)
                | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f66,plain,
    ( ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) )
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f58,f65,f64,f63])).

fof(f109,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f81,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f38,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f84,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f79,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f85,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f105,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f66])).

fof(f107,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f66])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f70,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f99,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f104,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f102,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f66])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f108,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f40,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f86,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f77,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f82,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f46])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f53])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f103,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f48])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f49])).

fof(f94,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f106,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f66])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f91,plain,(
    ! [X2,X0,X3,X1] :
      ( k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f20,axiom,(
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

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f55])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f110,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f66])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X0)
              & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) )
           => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v2_funct_1(X0)
          | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f83,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f59])).

fof(f69,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_36,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1594,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_12,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1608,plain,
    ( v2_funct_1(X0) != iProver_top
    | v2_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1604,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3254,plain,
    ( k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_relat_1(k1_relat_1(k2_funct_1(X0)))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1608,c_1604])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_109,plain,
    ( v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_13,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_112,plain,
    ( v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_10205,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_relat_1(k1_relat_1(k2_funct_1(X0)))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3254,c_109,c_112])).

cnf(c_10206,plain,
    ( k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_relat_1(k1_relat_1(k2_funct_1(X0)))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_10205])).

cnf(c_10216,plain,
    ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_10206])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1605,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3712,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_1605])).

cnf(c_40,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_38,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1922,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_2202,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2878,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2202])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_320,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_321,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_320])).

cnf(c_382,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_321])).

cnf(c_2008,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_382])).

cnf(c_2925,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2008])).

cnf(c_6,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_3656,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4267,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3712,c_40,c_38,c_36,c_1922,c_2878,c_2925,c_3656])).

cnf(c_1593,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_32,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_41,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_531,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_41])).

cnf(c_532,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_43,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_536,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_43])).

cnf(c_537,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_536])).

cnf(c_1639,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1593,c_532,c_537])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1600,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2480,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1639,c_1600])).

cnf(c_37,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1636,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_37,c_532,c_537])).

cnf(c_2725,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2480,c_1636])).

cnf(c_1613,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2200,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_1613])).

cnf(c_2730,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2725,c_2200])).

cnf(c_1590,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_382])).

cnf(c_6495,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2730,c_1590])).

cnf(c_49,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2879,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2878])).

cnf(c_2927,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2925])).

cnf(c_3657,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3656])).

cnf(c_7110,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6495,c_49,c_2879,c_2927,c_3657])).

cnf(c_19,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_funct_1(k2_funct_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1603,plain,
    ( k2_funct_1(k2_funct_1(X0)) = X0
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_3085,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_1603])).

cnf(c_47,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_3279,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3085,c_47])).

cnf(c_7117,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(superposition,[status(thm)],[c_7110,c_3279])).

cnf(c_10220,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_10216,c_4267,c_7117])).

cnf(c_10442,plain,
    ( k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_10220,c_47,c_49,c_2879,c_2927,c_3657])).

cnf(c_8,plain,
    ( k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_10446,plain,
    ( k2_relat_1(k6_relat_1(k2_relat_1(sK2))) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_10442,c_8])).

cnf(c_10448,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_10446,c_8])).

cnf(c_1591,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1609,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_7,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1611,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_2679,plain,
    ( k9_relat_1(k2_funct_1(X0),k1_relat_1(k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1609,c_1611])).

cnf(c_7552,plain,
    ( k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_2679])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1607,plain,
    ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3850,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1594,c_1607])).

cnf(c_1930,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_4271,plain,
    ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3850,c_40,c_38,c_36,c_1930,c_2878,c_2925,c_3656])).

cnf(c_7559,plain,
    ( k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2))
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7552,c_4271])).

cnf(c_7745,plain,
    ( k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7559,c_49,c_2879,c_2927,c_3657])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_33,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_42,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_518,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_42])).

cnf(c_519,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_518])).

cnf(c_55,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_521,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_519,c_42,c_41,c_55])).

cnf(c_543,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_521])).

cnf(c_544,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_543])).

cnf(c_28,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_605,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_544,c_28])).

cnf(c_20,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_621,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_605,c_20])).

cnf(c_1589,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_621])).

cnf(c_1985,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1639,c_1589])).

cnf(c_39,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1592,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_1633,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1592,c_532,c_537])).

cnf(c_2138,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1985,c_47,c_1633])).

cnf(c_7118,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_7110,c_2138])).

cnf(c_2732,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2725,c_1639])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1599,plain,
    ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3384,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_2732,c_1599])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1602,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3642,plain,
    ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_3384,c_1602])).

cnf(c_4473,plain,
    ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3642,c_2732])).

cnf(c_4480,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_4473,c_1613])).

cnf(c_7170,plain,
    ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7118,c_4480])).

cnf(c_8025,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7745,c_7170])).

cnf(c_2727,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2725,c_2480])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1598,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_4563,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_1598])).

cnf(c_50,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2733,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2725,c_1633])).

cnf(c_4929,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4563,c_47,c_50,c_2732,c_2733])).

cnf(c_4937,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4929,c_1600])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1601,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_4936,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_4929,c_1601])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1595,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4021,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2727,c_1595])).

cnf(c_4315,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4021,c_47,c_50,c_2732,c_2733])).

cnf(c_35,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1734,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_35,c_532,c_537])).

cnf(c_2734,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2725,c_1734])).

cnf(c_4318,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4315,c_2734])).

cnf(c_5074,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4936,c_4318])).

cnf(c_5207,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4937,c_5074])).

cnf(c_7164,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_7118,c_5207])).

cnf(c_16,plain,
    ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1606,plain,
    ( k2_relat_1(k5_relat_1(X0,X1)) != k2_relat_1(X1)
    | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) = iProver_top
    | v2_funct_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4552,plain,
    ( k2_relat_1(k6_relat_1(k2_relat_1(sK2))) != k2_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4267,c_1606])).

cnf(c_4553,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_4552,c_8])).

cnf(c_4554,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_4553])).

cnf(c_48,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_58,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_32])).

cnf(c_1885,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_1886,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1885])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1988,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2180,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1988])).

cnf(c_2181,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2180])).

cnf(c_891,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2471,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_891])).

cnf(c_2942,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2471])).

cnf(c_5615,plain,
    ( r1_tarski(k1_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4554,c_41,c_47,c_48,c_49,c_37,c_50,c_58,c_1886,c_2181,c_2879,c_2927,c_2942,c_3657])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1616,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5620,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5615,c_1616])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10448,c_8025,c_7164,c_5620])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:48:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 1.88/1.04  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.04  
% 1.88/1.04  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.88/1.04  
% 1.88/1.04  ------  iProver source info
% 1.88/1.04  
% 1.88/1.04  git: date: 2020-06-30 10:37:57 +0100
% 1.88/1.04  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.88/1.04  git: non_committed_changes: false
% 1.88/1.04  git: last_make_outside_of_git: false
% 1.88/1.04  
% 1.88/1.04  ------ 
% 1.88/1.04  
% 1.88/1.04  ------ Input Options
% 1.88/1.04  
% 1.88/1.04  --out_options                           all
% 1.88/1.04  --tptp_safe_out                         true
% 1.88/1.04  --problem_path                          ""
% 1.88/1.04  --include_path                          ""
% 1.88/1.04  --clausifier                            res/vclausify_rel
% 1.88/1.04  --clausifier_options                    --mode clausify
% 1.88/1.04  --stdin                                 false
% 1.88/1.04  --stats_out                             all
% 1.88/1.04  
% 1.88/1.04  ------ General Options
% 1.88/1.04  
% 1.88/1.04  --fof                                   false
% 1.88/1.04  --time_out_real                         305.
% 1.88/1.04  --time_out_virtual                      -1.
% 1.88/1.04  --symbol_type_check                     false
% 1.88/1.04  --clausify_out                          false
% 1.88/1.04  --sig_cnt_out                           false
% 1.88/1.04  --trig_cnt_out                          false
% 1.88/1.04  --trig_cnt_out_tolerance                1.
% 1.88/1.04  --trig_cnt_out_sk_spl                   false
% 1.88/1.04  --abstr_cl_out                          false
% 1.88/1.04  
% 1.88/1.04  ------ Global Options
% 1.88/1.04  
% 1.88/1.04  --schedule                              default
% 1.88/1.04  --add_important_lit                     false
% 1.88/1.04  --prop_solver_per_cl                    1000
% 1.88/1.04  --min_unsat_core                        false
% 1.88/1.04  --soft_assumptions                      false
% 1.88/1.04  --soft_lemma_size                       3
% 1.88/1.04  --prop_impl_unit_size                   0
% 1.88/1.04  --prop_impl_unit                        []
% 1.88/1.04  --share_sel_clauses                     true
% 1.88/1.04  --reset_solvers                         false
% 1.88/1.04  --bc_imp_inh                            [conj_cone]
% 1.88/1.04  --conj_cone_tolerance                   3.
% 1.88/1.04  --extra_neg_conj                        none
% 1.88/1.04  --large_theory_mode                     true
% 1.88/1.04  --prolific_symb_bound                   200
% 1.88/1.04  --lt_threshold                          2000
% 1.88/1.04  --clause_weak_htbl                      true
% 1.88/1.04  --gc_record_bc_elim                     false
% 1.88/1.04  
% 1.88/1.04  ------ Preprocessing Options
% 1.88/1.04  
% 1.88/1.04  --preprocessing_flag                    true
% 1.88/1.04  --time_out_prep_mult                    0.1
% 1.88/1.04  --splitting_mode                        input
% 1.88/1.04  --splitting_grd                         true
% 1.88/1.04  --splitting_cvd                         false
% 1.88/1.04  --splitting_cvd_svl                     false
% 1.88/1.04  --splitting_nvd                         32
% 1.88/1.04  --sub_typing                            true
% 1.88/1.04  --prep_gs_sim                           true
% 1.88/1.04  --prep_unflatten                        true
% 1.88/1.04  --prep_res_sim                          true
% 1.88/1.04  --prep_upred                            true
% 1.88/1.04  --prep_sem_filter                       exhaustive
% 1.88/1.04  --prep_sem_filter_out                   false
% 1.88/1.04  --pred_elim                             true
% 1.88/1.04  --res_sim_input                         true
% 1.88/1.04  --eq_ax_congr_red                       true
% 1.88/1.04  --pure_diseq_elim                       true
% 1.88/1.04  --brand_transform                       false
% 1.88/1.04  --non_eq_to_eq                          false
% 1.88/1.04  --prep_def_merge                        true
% 1.88/1.04  --prep_def_merge_prop_impl              false
% 1.88/1.04  --prep_def_merge_mbd                    true
% 1.88/1.04  --prep_def_merge_tr_red                 false
% 1.88/1.04  --prep_def_merge_tr_cl                  false
% 1.88/1.04  --smt_preprocessing                     true
% 1.88/1.04  --smt_ac_axioms                         fast
% 1.88/1.04  --preprocessed_out                      false
% 1.88/1.04  --preprocessed_stats                    false
% 1.88/1.04  
% 1.88/1.04  ------ Abstraction refinement Options
% 1.88/1.04  
% 1.88/1.04  --abstr_ref                             []
% 1.88/1.04  --abstr_ref_prep                        false
% 1.88/1.04  --abstr_ref_until_sat                   false
% 1.88/1.04  --abstr_ref_sig_restrict                funpre
% 1.88/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/1.04  --abstr_ref_under                       []
% 1.88/1.04  
% 1.88/1.04  ------ SAT Options
% 1.88/1.04  
% 1.88/1.04  --sat_mode                              false
% 1.88/1.04  --sat_fm_restart_options                ""
% 1.88/1.04  --sat_gr_def                            false
% 1.88/1.04  --sat_epr_types                         true
% 1.88/1.04  --sat_non_cyclic_types                  false
% 1.88/1.04  --sat_finite_models                     false
% 1.88/1.04  --sat_fm_lemmas                         false
% 1.88/1.04  --sat_fm_prep                           false
% 1.88/1.04  --sat_fm_uc_incr                        true
% 1.88/1.04  --sat_out_model                         small
% 1.88/1.04  --sat_out_clauses                       false
% 1.88/1.04  
% 1.88/1.04  ------ QBF Options
% 1.88/1.04  
% 1.88/1.04  --qbf_mode                              false
% 1.88/1.04  --qbf_elim_univ                         false
% 1.88/1.04  --qbf_dom_inst                          none
% 1.88/1.04  --qbf_dom_pre_inst                      false
% 1.88/1.04  --qbf_sk_in                             false
% 1.88/1.04  --qbf_pred_elim                         true
% 1.88/1.04  --qbf_split                             512
% 1.88/1.04  
% 1.88/1.04  ------ BMC1 Options
% 1.88/1.04  
% 1.88/1.04  --bmc1_incremental                      false
% 1.88/1.04  --bmc1_axioms                           reachable_all
% 1.88/1.04  --bmc1_min_bound                        0
% 1.88/1.04  --bmc1_max_bound                        -1
% 1.88/1.04  --bmc1_max_bound_default                -1
% 1.88/1.04  --bmc1_symbol_reachability              true
% 1.88/1.04  --bmc1_property_lemmas                  false
% 1.88/1.04  --bmc1_k_induction                      false
% 1.88/1.04  --bmc1_non_equiv_states                 false
% 1.88/1.04  --bmc1_deadlock                         false
% 1.88/1.04  --bmc1_ucm                              false
% 1.88/1.04  --bmc1_add_unsat_core                   none
% 1.88/1.04  --bmc1_unsat_core_children              false
% 1.88/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/1.04  --bmc1_out_stat                         full
% 1.88/1.04  --bmc1_ground_init                      false
% 1.88/1.04  --bmc1_pre_inst_next_state              false
% 1.88/1.04  --bmc1_pre_inst_state                   false
% 1.88/1.04  --bmc1_pre_inst_reach_state             false
% 1.88/1.04  --bmc1_out_unsat_core                   false
% 1.88/1.04  --bmc1_aig_witness_out                  false
% 1.88/1.04  --bmc1_verbose                          false
% 1.88/1.04  --bmc1_dump_clauses_tptp                false
% 1.88/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.88/1.04  --bmc1_dump_file                        -
% 1.88/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.88/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.88/1.04  --bmc1_ucm_extend_mode                  1
% 1.88/1.04  --bmc1_ucm_init_mode                    2
% 1.88/1.04  --bmc1_ucm_cone_mode                    none
% 1.88/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.88/1.04  --bmc1_ucm_relax_model                  4
% 1.88/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.88/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/1.04  --bmc1_ucm_layered_model                none
% 1.88/1.04  --bmc1_ucm_max_lemma_size               10
% 1.88/1.04  
% 1.88/1.04  ------ AIG Options
% 1.88/1.04  
% 1.88/1.04  --aig_mode                              false
% 1.88/1.04  
% 1.88/1.04  ------ Instantiation Options
% 1.88/1.04  
% 1.88/1.04  --instantiation_flag                    true
% 1.88/1.04  --inst_sos_flag                         false
% 1.88/1.04  --inst_sos_phase                        true
% 1.88/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/1.04  --inst_lit_sel_side                     num_symb
% 1.88/1.04  --inst_solver_per_active                1400
% 1.88/1.04  --inst_solver_calls_frac                1.
% 1.88/1.04  --inst_passive_queue_type               priority_queues
% 1.88/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/1.04  --inst_passive_queues_freq              [25;2]
% 1.88/1.04  --inst_dismatching                      true
% 1.88/1.04  --inst_eager_unprocessed_to_passive     true
% 1.88/1.04  --inst_prop_sim_given                   true
% 1.88/1.04  --inst_prop_sim_new                     false
% 1.88/1.04  --inst_subs_new                         false
% 1.88/1.04  --inst_eq_res_simp                      false
% 1.88/1.04  --inst_subs_given                       false
% 1.88/1.04  --inst_orphan_elimination               true
% 1.88/1.04  --inst_learning_loop_flag               true
% 1.88/1.04  --inst_learning_start                   3000
% 1.88/1.04  --inst_learning_factor                  2
% 1.88/1.04  --inst_start_prop_sim_after_learn       3
% 1.88/1.04  --inst_sel_renew                        solver
% 1.88/1.04  --inst_lit_activity_flag                true
% 1.88/1.04  --inst_restr_to_given                   false
% 1.88/1.04  --inst_activity_threshold               500
% 1.88/1.04  --inst_out_proof                        true
% 1.88/1.04  
% 1.88/1.04  ------ Resolution Options
% 1.88/1.04  
% 1.88/1.04  --resolution_flag                       true
% 1.88/1.04  --res_lit_sel                           adaptive
% 1.88/1.04  --res_lit_sel_side                      none
% 1.88/1.04  --res_ordering                          kbo
% 1.88/1.04  --res_to_prop_solver                    active
% 1.88/1.04  --res_prop_simpl_new                    false
% 1.88/1.04  --res_prop_simpl_given                  true
% 1.88/1.04  --res_passive_queue_type                priority_queues
% 1.88/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/1.04  --res_passive_queues_freq               [15;5]
% 1.88/1.04  --res_forward_subs                      full
% 1.88/1.04  --res_backward_subs                     full
% 1.88/1.04  --res_forward_subs_resolution           true
% 1.88/1.04  --res_backward_subs_resolution          true
% 1.88/1.04  --res_orphan_elimination                true
% 1.88/1.04  --res_time_limit                        2.
% 1.88/1.04  --res_out_proof                         true
% 1.88/1.04  
% 1.88/1.04  ------ Superposition Options
% 1.88/1.04  
% 1.88/1.04  --superposition_flag                    true
% 1.88/1.04  --sup_passive_queue_type                priority_queues
% 1.88/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.88/1.04  --demod_completeness_check              fast
% 1.88/1.04  --demod_use_ground                      true
% 1.88/1.04  --sup_to_prop_solver                    passive
% 1.88/1.04  --sup_prop_simpl_new                    true
% 1.88/1.04  --sup_prop_simpl_given                  true
% 1.88/1.04  --sup_fun_splitting                     false
% 1.88/1.04  --sup_smt_interval                      50000
% 1.88/1.04  
% 1.88/1.04  ------ Superposition Simplification Setup
% 1.88/1.04  
% 1.88/1.04  --sup_indices_passive                   []
% 1.88/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.04  --sup_full_bw                           [BwDemod]
% 1.88/1.04  --sup_immed_triv                        [TrivRules]
% 1.88/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.04  --sup_immed_bw_main                     []
% 1.88/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.04  
% 1.88/1.04  ------ Combination Options
% 1.88/1.04  
% 1.88/1.04  --comb_res_mult                         3
% 1.88/1.04  --comb_sup_mult                         2
% 1.88/1.04  --comb_inst_mult                        10
% 1.88/1.04  
% 1.88/1.04  ------ Debug Options
% 1.88/1.04  
% 1.88/1.04  --dbg_backtrace                         false
% 1.88/1.04  --dbg_dump_prop_clauses                 false
% 1.88/1.04  --dbg_dump_prop_clauses_file            -
% 1.88/1.04  --dbg_out_stat                          false
% 1.88/1.04  ------ Parsing...
% 1.88/1.04  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.88/1.04  
% 1.88/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 6 0s  sf_e  pe_s  pe_e 
% 1.88/1.04  
% 1.88/1.04  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.88/1.04  
% 1.88/1.04  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.88/1.04  ------ Proving...
% 1.88/1.04  ------ Problem Properties 
% 1.88/1.04  
% 1.88/1.04  
% 1.88/1.04  clauses                                 34
% 1.88/1.04  conjectures                             6
% 1.88/1.04  EPR                                     5
% 1.88/1.04  Horn                                    34
% 1.88/1.04  unary                                   11
% 1.88/1.04  binary                                  8
% 1.88/1.04  lits                                    95
% 1.88/1.04  lits eq                                 23
% 1.88/1.04  fd_pure                                 0
% 1.88/1.04  fd_pseudo                               0
% 1.88/1.04  fd_cond                                 0
% 1.88/1.04  fd_pseudo_cond                          2
% 1.88/1.04  AC symbols                              0
% 1.88/1.04  
% 1.88/1.04  ------ Schedule dynamic 5 is on 
% 1.88/1.04  
% 1.88/1.04  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.88/1.04  
% 1.88/1.04  
% 1.88/1.04  ------ 
% 1.88/1.04  Current options:
% 1.88/1.04  ------ 
% 1.88/1.04  
% 1.88/1.04  ------ Input Options
% 1.88/1.04  
% 1.88/1.04  --out_options                           all
% 1.88/1.04  --tptp_safe_out                         true
% 1.88/1.04  --problem_path                          ""
% 1.88/1.04  --include_path                          ""
% 1.88/1.04  --clausifier                            res/vclausify_rel
% 1.88/1.04  --clausifier_options                    --mode clausify
% 1.88/1.04  --stdin                                 false
% 1.88/1.04  --stats_out                             all
% 1.88/1.04  
% 1.88/1.04  ------ General Options
% 1.88/1.04  
% 1.88/1.04  --fof                                   false
% 1.88/1.04  --time_out_real                         305.
% 1.88/1.04  --time_out_virtual                      -1.
% 1.88/1.04  --symbol_type_check                     false
% 1.88/1.04  --clausify_out                          false
% 1.88/1.04  --sig_cnt_out                           false
% 1.88/1.04  --trig_cnt_out                          false
% 1.88/1.04  --trig_cnt_out_tolerance                1.
% 1.88/1.04  --trig_cnt_out_sk_spl                   false
% 1.88/1.04  --abstr_cl_out                          false
% 1.88/1.04  
% 1.88/1.04  ------ Global Options
% 1.88/1.04  
% 1.88/1.04  --schedule                              default
% 1.88/1.04  --add_important_lit                     false
% 1.88/1.04  --prop_solver_per_cl                    1000
% 1.88/1.04  --min_unsat_core                        false
% 1.88/1.04  --soft_assumptions                      false
% 1.88/1.04  --soft_lemma_size                       3
% 1.88/1.04  --prop_impl_unit_size                   0
% 1.88/1.04  --prop_impl_unit                        []
% 1.88/1.04  --share_sel_clauses                     true
% 1.88/1.04  --reset_solvers                         false
% 1.88/1.04  --bc_imp_inh                            [conj_cone]
% 1.88/1.04  --conj_cone_tolerance                   3.
% 1.88/1.04  --extra_neg_conj                        none
% 1.88/1.04  --large_theory_mode                     true
% 1.88/1.04  --prolific_symb_bound                   200
% 1.88/1.04  --lt_threshold                          2000
% 1.88/1.04  --clause_weak_htbl                      true
% 1.88/1.04  --gc_record_bc_elim                     false
% 1.88/1.04  
% 1.88/1.04  ------ Preprocessing Options
% 1.88/1.04  
% 1.88/1.04  --preprocessing_flag                    true
% 1.88/1.04  --time_out_prep_mult                    0.1
% 1.88/1.04  --splitting_mode                        input
% 1.88/1.04  --splitting_grd                         true
% 1.88/1.04  --splitting_cvd                         false
% 1.88/1.04  --splitting_cvd_svl                     false
% 1.88/1.04  --splitting_nvd                         32
% 1.88/1.04  --sub_typing                            true
% 1.88/1.04  --prep_gs_sim                           true
% 1.88/1.04  --prep_unflatten                        true
% 1.88/1.04  --prep_res_sim                          true
% 1.88/1.04  --prep_upred                            true
% 1.88/1.04  --prep_sem_filter                       exhaustive
% 1.88/1.04  --prep_sem_filter_out                   false
% 1.88/1.04  --pred_elim                             true
% 1.88/1.04  --res_sim_input                         true
% 1.88/1.04  --eq_ax_congr_red                       true
% 1.88/1.04  --pure_diseq_elim                       true
% 1.88/1.04  --brand_transform                       false
% 1.88/1.04  --non_eq_to_eq                          false
% 1.88/1.04  --prep_def_merge                        true
% 1.88/1.04  --prep_def_merge_prop_impl              false
% 1.88/1.04  --prep_def_merge_mbd                    true
% 1.88/1.04  --prep_def_merge_tr_red                 false
% 1.88/1.04  --prep_def_merge_tr_cl                  false
% 1.88/1.04  --smt_preprocessing                     true
% 1.88/1.04  --smt_ac_axioms                         fast
% 1.88/1.04  --preprocessed_out                      false
% 1.88/1.04  --preprocessed_stats                    false
% 1.88/1.04  
% 1.88/1.04  ------ Abstraction refinement Options
% 1.88/1.04  
% 1.88/1.04  --abstr_ref                             []
% 1.88/1.04  --abstr_ref_prep                        false
% 1.88/1.04  --abstr_ref_until_sat                   false
% 1.88/1.04  --abstr_ref_sig_restrict                funpre
% 1.88/1.04  --abstr_ref_af_restrict_to_split_sk     false
% 1.88/1.04  --abstr_ref_under                       []
% 1.88/1.04  
% 1.88/1.04  ------ SAT Options
% 1.88/1.04  
% 1.88/1.04  --sat_mode                              false
% 1.88/1.04  --sat_fm_restart_options                ""
% 1.88/1.04  --sat_gr_def                            false
% 1.88/1.04  --sat_epr_types                         true
% 1.88/1.04  --sat_non_cyclic_types                  false
% 1.88/1.04  --sat_finite_models                     false
% 1.88/1.04  --sat_fm_lemmas                         false
% 1.88/1.04  --sat_fm_prep                           false
% 1.88/1.04  --sat_fm_uc_incr                        true
% 1.88/1.04  --sat_out_model                         small
% 1.88/1.04  --sat_out_clauses                       false
% 1.88/1.04  
% 1.88/1.04  ------ QBF Options
% 1.88/1.04  
% 1.88/1.04  --qbf_mode                              false
% 1.88/1.04  --qbf_elim_univ                         false
% 1.88/1.04  --qbf_dom_inst                          none
% 1.88/1.04  --qbf_dom_pre_inst                      false
% 1.88/1.04  --qbf_sk_in                             false
% 1.88/1.04  --qbf_pred_elim                         true
% 1.88/1.04  --qbf_split                             512
% 1.88/1.04  
% 1.88/1.04  ------ BMC1 Options
% 1.88/1.04  
% 1.88/1.04  --bmc1_incremental                      false
% 1.88/1.04  --bmc1_axioms                           reachable_all
% 1.88/1.04  --bmc1_min_bound                        0
% 1.88/1.04  --bmc1_max_bound                        -1
% 1.88/1.04  --bmc1_max_bound_default                -1
% 1.88/1.04  --bmc1_symbol_reachability              true
% 1.88/1.04  --bmc1_property_lemmas                  false
% 1.88/1.04  --bmc1_k_induction                      false
% 1.88/1.04  --bmc1_non_equiv_states                 false
% 1.88/1.04  --bmc1_deadlock                         false
% 1.88/1.04  --bmc1_ucm                              false
% 1.88/1.04  --bmc1_add_unsat_core                   none
% 1.88/1.04  --bmc1_unsat_core_children              false
% 1.88/1.04  --bmc1_unsat_core_extrapolate_axioms    false
% 1.88/1.04  --bmc1_out_stat                         full
% 1.88/1.04  --bmc1_ground_init                      false
% 1.88/1.04  --bmc1_pre_inst_next_state              false
% 1.88/1.04  --bmc1_pre_inst_state                   false
% 1.88/1.04  --bmc1_pre_inst_reach_state             false
% 1.88/1.04  --bmc1_out_unsat_core                   false
% 1.88/1.04  --bmc1_aig_witness_out                  false
% 1.88/1.04  --bmc1_verbose                          false
% 1.88/1.04  --bmc1_dump_clauses_tptp                false
% 1.88/1.04  --bmc1_dump_unsat_core_tptp             false
% 1.88/1.04  --bmc1_dump_file                        -
% 1.88/1.04  --bmc1_ucm_expand_uc_limit              128
% 1.88/1.04  --bmc1_ucm_n_expand_iterations          6
% 1.88/1.04  --bmc1_ucm_extend_mode                  1
% 1.88/1.04  --bmc1_ucm_init_mode                    2
% 1.88/1.04  --bmc1_ucm_cone_mode                    none
% 1.88/1.04  --bmc1_ucm_reduced_relation_type        0
% 1.88/1.04  --bmc1_ucm_relax_model                  4
% 1.88/1.04  --bmc1_ucm_full_tr_after_sat            true
% 1.88/1.04  --bmc1_ucm_expand_neg_assumptions       false
% 1.88/1.04  --bmc1_ucm_layered_model                none
% 1.88/1.04  --bmc1_ucm_max_lemma_size               10
% 1.88/1.04  
% 1.88/1.04  ------ AIG Options
% 1.88/1.04  
% 1.88/1.04  --aig_mode                              false
% 1.88/1.04  
% 1.88/1.04  ------ Instantiation Options
% 1.88/1.04  
% 1.88/1.04  --instantiation_flag                    true
% 1.88/1.04  --inst_sos_flag                         false
% 1.88/1.04  --inst_sos_phase                        true
% 1.88/1.04  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.88/1.04  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.88/1.04  --inst_lit_sel_side                     none
% 1.88/1.04  --inst_solver_per_active                1400
% 1.88/1.04  --inst_solver_calls_frac                1.
% 1.88/1.04  --inst_passive_queue_type               priority_queues
% 1.88/1.04  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.88/1.04  --inst_passive_queues_freq              [25;2]
% 1.88/1.04  --inst_dismatching                      true
% 1.88/1.04  --inst_eager_unprocessed_to_passive     true
% 1.88/1.04  --inst_prop_sim_given                   true
% 1.88/1.04  --inst_prop_sim_new                     false
% 1.88/1.04  --inst_subs_new                         false
% 1.88/1.04  --inst_eq_res_simp                      false
% 1.88/1.04  --inst_subs_given                       false
% 1.88/1.04  --inst_orphan_elimination               true
% 1.88/1.04  --inst_learning_loop_flag               true
% 1.88/1.04  --inst_learning_start                   3000
% 1.88/1.04  --inst_learning_factor                  2
% 1.88/1.04  --inst_start_prop_sim_after_learn       3
% 1.88/1.04  --inst_sel_renew                        solver
% 1.88/1.04  --inst_lit_activity_flag                true
% 1.88/1.04  --inst_restr_to_given                   false
% 1.88/1.04  --inst_activity_threshold               500
% 1.88/1.04  --inst_out_proof                        true
% 1.88/1.04  
% 1.88/1.04  ------ Resolution Options
% 1.88/1.04  
% 1.88/1.04  --resolution_flag                       false
% 1.88/1.04  --res_lit_sel                           adaptive
% 1.88/1.04  --res_lit_sel_side                      none
% 1.88/1.04  --res_ordering                          kbo
% 1.88/1.04  --res_to_prop_solver                    active
% 1.88/1.04  --res_prop_simpl_new                    false
% 1.88/1.04  --res_prop_simpl_given                  true
% 1.88/1.04  --res_passive_queue_type                priority_queues
% 1.88/1.04  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.88/1.04  --res_passive_queues_freq               [15;5]
% 1.88/1.04  --res_forward_subs                      full
% 1.88/1.04  --res_backward_subs                     full
% 1.88/1.04  --res_forward_subs_resolution           true
% 1.88/1.04  --res_backward_subs_resolution          true
% 1.88/1.04  --res_orphan_elimination                true
% 1.88/1.04  --res_time_limit                        2.
% 1.88/1.04  --res_out_proof                         true
% 1.88/1.04  
% 1.88/1.04  ------ Superposition Options
% 1.88/1.04  
% 1.88/1.04  --superposition_flag                    true
% 1.88/1.04  --sup_passive_queue_type                priority_queues
% 1.88/1.04  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.88/1.04  --sup_passive_queues_freq               [8;1;4]
% 1.88/1.04  --demod_completeness_check              fast
% 1.88/1.04  --demod_use_ground                      true
% 1.88/1.04  --sup_to_prop_solver                    passive
% 1.88/1.04  --sup_prop_simpl_new                    true
% 1.88/1.04  --sup_prop_simpl_given                  true
% 1.88/1.04  --sup_fun_splitting                     false
% 1.88/1.04  --sup_smt_interval                      50000
% 1.88/1.04  
% 1.88/1.04  ------ Superposition Simplification Setup
% 1.88/1.04  
% 1.88/1.04  --sup_indices_passive                   []
% 1.88/1.04  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.04  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.04  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.88/1.04  --sup_full_triv                         [TrivRules;PropSubs]
% 1.88/1.04  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.04  --sup_full_bw                           [BwDemod]
% 1.88/1.04  --sup_immed_triv                        [TrivRules]
% 1.88/1.04  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.88/1.04  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.04  --sup_immed_bw_main                     []
% 1.88/1.04  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.04  --sup_input_triv                        [Unflattening;TrivRules]
% 1.88/1.04  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.88/1.04  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.88/1.04  
% 1.88/1.04  ------ Combination Options
% 1.88/1.04  
% 1.88/1.04  --comb_res_mult                         3
% 1.88/1.04  --comb_sup_mult                         2
% 1.88/1.04  --comb_inst_mult                        10
% 1.88/1.04  
% 1.88/1.04  ------ Debug Options
% 1.88/1.04  
% 1.88/1.04  --dbg_backtrace                         false
% 1.88/1.04  --dbg_dump_prop_clauses                 false
% 1.88/1.04  --dbg_dump_prop_clauses_file            -
% 1.88/1.04  --dbg_out_stat                          false
% 1.88/1.04  
% 1.88/1.04  
% 1.88/1.04  
% 1.88/1.04  
% 1.88/1.04  ------ Proving...
% 1.88/1.04  
% 1.88/1.04  
% 1.88/1.04  % SZS status Theorem for theBenchmark.p
% 1.88/1.04  
% 1.88/1.04  % SZS output start CNFRefutation for theBenchmark.p
% 1.88/1.04  
% 1.88/1.04  fof(f24,conjecture,(
% 1.88/1.04    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f25,negated_conjecture,(
% 1.88/1.04    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 1.88/1.04    inference(negated_conjecture,[],[f24])).
% 1.88/1.04  
% 1.88/1.04  fof(f57,plain,(
% 1.88/1.04    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.88/1.04    inference(ennf_transformation,[],[f25])).
% 1.88/1.04  
% 1.88/1.04  fof(f58,plain,(
% 1.88/1.04    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.88/1.04    inference(flattening,[],[f57])).
% 1.88/1.04  
% 1.88/1.04  fof(f65,plain,(
% 1.88/1.04    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 1.88/1.04    introduced(choice_axiom,[])).
% 1.88/1.04  
% 1.88/1.04  fof(f64,plain,(
% 1.88/1.04    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 1.88/1.04    introduced(choice_axiom,[])).
% 1.88/1.04  
% 1.88/1.04  fof(f63,plain,(
% 1.88/1.04    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 1.88/1.04    introduced(choice_axiom,[])).
% 1.88/1.04  
% 1.88/1.04  fof(f66,plain,(
% 1.88/1.04    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.88/1.04    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f58,f65,f64,f63])).
% 1.88/1.04  
% 1.88/1.04  fof(f109,plain,(
% 1.88/1.04    v2_funct_1(sK2)),
% 1.88/1.04    inference(cnf_transformation,[],[f66])).
% 1.88/1.04  
% 1.88/1.04  fof(f8,axiom,(
% 1.88/1.04    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f31,plain,(
% 1.88/1.04    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.88/1.04    inference(ennf_transformation,[],[f8])).
% 1.88/1.04  
% 1.88/1.04  fof(f32,plain,(
% 1.88/1.04    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/1.04    inference(flattening,[],[f31])).
% 1.88/1.04  
% 1.88/1.04  fof(f81,plain,(
% 1.88/1.04    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f32])).
% 1.88/1.04  
% 1.88/1.04  fof(f11,axiom,(
% 1.88/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f37,plain,(
% 1.88/1.04    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.88/1.04    inference(ennf_transformation,[],[f11])).
% 1.88/1.04  
% 1.88/1.04  fof(f38,plain,(
% 1.88/1.04    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/1.04    inference(flattening,[],[f37])).
% 1.88/1.04  
% 1.88/1.04  fof(f84,plain,(
% 1.88/1.04    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f38])).
% 1.88/1.04  
% 1.88/1.04  fof(f79,plain,(
% 1.88/1.04    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f32])).
% 1.88/1.04  
% 1.88/1.04  fof(f80,plain,(
% 1.88/1.04    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f32])).
% 1.88/1.04  
% 1.88/1.04  fof(f85,plain,(
% 1.88/1.04    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f38])).
% 1.88/1.04  
% 1.88/1.04  fof(f105,plain,(
% 1.88/1.04    v1_funct_1(sK2)),
% 1.88/1.04    inference(cnf_transformation,[],[f66])).
% 1.88/1.04  
% 1.88/1.04  fof(f107,plain,(
% 1.88/1.04    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.88/1.04    inference(cnf_transformation,[],[f66])).
% 1.88/1.04  
% 1.88/1.04  fof(f2,axiom,(
% 1.88/1.04    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f61,plain,(
% 1.88/1.04    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 1.88/1.04    inference(nnf_transformation,[],[f2])).
% 1.88/1.04  
% 1.88/1.04  fof(f70,plain,(
% 1.88/1.04    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.88/1.04    inference(cnf_transformation,[],[f61])).
% 1.88/1.04  
% 1.88/1.04  fof(f3,axiom,(
% 1.88/1.04    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f27,plain,(
% 1.88/1.04    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.88/1.04    inference(ennf_transformation,[],[f3])).
% 1.88/1.04  
% 1.88/1.04  fof(f72,plain,(
% 1.88/1.04    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f27])).
% 1.88/1.04  
% 1.88/1.04  fof(f71,plain,(
% 1.88/1.04    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f61])).
% 1.88/1.04  
% 1.88/1.04  fof(f4,axiom,(
% 1.88/1.04    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f73,plain,(
% 1.88/1.04    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.88/1.04    inference(cnf_transformation,[],[f4])).
% 1.88/1.04  
% 1.88/1.04  fof(f21,axiom,(
% 1.88/1.04    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f52,plain,(
% 1.88/1.04    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.88/1.04    inference(ennf_transformation,[],[f21])).
% 1.88/1.04  
% 1.88/1.04  fof(f99,plain,(
% 1.88/1.04    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f52])).
% 1.88/1.04  
% 1.88/1.04  fof(f104,plain,(
% 1.88/1.04    l1_struct_0(sK1)),
% 1.88/1.04    inference(cnf_transformation,[],[f66])).
% 1.88/1.04  
% 1.88/1.04  fof(f102,plain,(
% 1.88/1.04    l1_struct_0(sK0)),
% 1.88/1.04    inference(cnf_transformation,[],[f66])).
% 1.88/1.04  
% 1.88/1.04  fof(f16,axiom,(
% 1.88/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f44,plain,(
% 1.88/1.04    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/1.04    inference(ennf_transformation,[],[f16])).
% 1.88/1.04  
% 1.88/1.04  fof(f90,plain,(
% 1.88/1.04    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/1.04    inference(cnf_transformation,[],[f44])).
% 1.88/1.04  
% 1.88/1.04  fof(f108,plain,(
% 1.88/1.04    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 1.88/1.04    inference(cnf_transformation,[],[f66])).
% 1.88/1.04  
% 1.88/1.04  fof(f12,axiom,(
% 1.88/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f39,plain,(
% 1.88/1.04    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.88/1.04    inference(ennf_transformation,[],[f12])).
% 1.88/1.04  
% 1.88/1.04  fof(f40,plain,(
% 1.88/1.04    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/1.04    inference(flattening,[],[f39])).
% 1.88/1.04  
% 1.88/1.04  fof(f86,plain,(
% 1.88/1.04    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f40])).
% 1.88/1.04  
% 1.88/1.04  fof(f6,axiom,(
% 1.88/1.04    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f76,plain,(
% 1.88/1.04    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.88/1.04    inference(cnf_transformation,[],[f6])).
% 1.88/1.04  
% 1.88/1.04  fof(f7,axiom,(
% 1.88/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f29,plain,(
% 1.88/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.88/1.04    inference(ennf_transformation,[],[f7])).
% 1.88/1.04  
% 1.88/1.04  fof(f30,plain,(
% 1.88/1.04    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/1.04    inference(flattening,[],[f29])).
% 1.88/1.04  
% 1.88/1.04  fof(f77,plain,(
% 1.88/1.04    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f30])).
% 1.88/1.04  
% 1.88/1.04  fof(f5,axiom,(
% 1.88/1.04    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f28,plain,(
% 1.88/1.04    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 1.88/1.04    inference(ennf_transformation,[],[f5])).
% 1.88/1.04  
% 1.88/1.04  fof(f74,plain,(
% 1.88/1.04    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f28])).
% 1.88/1.04  
% 1.88/1.04  fof(f9,axiom,(
% 1.88/1.04    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f33,plain,(
% 1.88/1.04    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 1.88/1.04    inference(ennf_transformation,[],[f9])).
% 1.88/1.04  
% 1.88/1.04  fof(f34,plain,(
% 1.88/1.04    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 1.88/1.04    inference(flattening,[],[f33])).
% 1.88/1.04  
% 1.88/1.04  fof(f82,plain,(
% 1.88/1.04    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f34])).
% 1.88/1.04  
% 1.88/1.04  fof(f18,axiom,(
% 1.88/1.04    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f46,plain,(
% 1.88/1.04    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.88/1.04    inference(ennf_transformation,[],[f18])).
% 1.88/1.04  
% 1.88/1.04  fof(f47,plain,(
% 1.88/1.04    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.88/1.04    inference(flattening,[],[f46])).
% 1.88/1.04  
% 1.88/1.04  fof(f93,plain,(
% 1.88/1.04    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f47])).
% 1.88/1.04  
% 1.88/1.04  fof(f22,axiom,(
% 1.88/1.04    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f53,plain,(
% 1.88/1.04    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.88/1.04    inference(ennf_transformation,[],[f22])).
% 1.88/1.04  
% 1.88/1.04  fof(f54,plain,(
% 1.88/1.04    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.88/1.04    inference(flattening,[],[f53])).
% 1.88/1.04  
% 1.88/1.04  fof(f100,plain,(
% 1.88/1.04    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f54])).
% 1.88/1.04  
% 1.88/1.04  fof(f103,plain,(
% 1.88/1.04    ~v2_struct_0(sK1)),
% 1.88/1.04    inference(cnf_transformation,[],[f66])).
% 1.88/1.04  
% 1.88/1.04  fof(f19,axiom,(
% 1.88/1.04    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f48,plain,(
% 1.88/1.04    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.88/1.04    inference(ennf_transformation,[],[f19])).
% 1.88/1.04  
% 1.88/1.04  fof(f49,plain,(
% 1.88/1.04    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.88/1.04    inference(flattening,[],[f48])).
% 1.88/1.04  
% 1.88/1.04  fof(f62,plain,(
% 1.88/1.04    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.88/1.04    inference(nnf_transformation,[],[f49])).
% 1.88/1.04  
% 1.88/1.04  fof(f94,plain,(
% 1.88/1.04    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f62])).
% 1.88/1.04  
% 1.88/1.04  fof(f13,axiom,(
% 1.88/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f26,plain,(
% 1.88/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 1.88/1.04    inference(pure_predicate_removal,[],[f13])).
% 1.88/1.04  
% 1.88/1.04  fof(f41,plain,(
% 1.88/1.04    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/1.04    inference(ennf_transformation,[],[f26])).
% 1.88/1.04  
% 1.88/1.04  fof(f87,plain,(
% 1.88/1.04    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/1.04    inference(cnf_transformation,[],[f41])).
% 1.88/1.04  
% 1.88/1.04  fof(f106,plain,(
% 1.88/1.04    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.88/1.04    inference(cnf_transformation,[],[f66])).
% 1.88/1.04  
% 1.88/1.04  fof(f17,axiom,(
% 1.88/1.04    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f45,plain,(
% 1.88/1.04    ! [X0,X1,X2,X3] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/1.04    inference(ennf_transformation,[],[f17])).
% 1.88/1.04  
% 1.88/1.04  fof(f91,plain,(
% 1.88/1.04    ( ! [X2,X0,X3,X1] : (k10_relat_1(X2,X3) = k8_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/1.04    inference(cnf_transformation,[],[f45])).
% 1.88/1.04  
% 1.88/1.04  fof(f14,axiom,(
% 1.88/1.04    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f42,plain,(
% 1.88/1.04    ! [X0,X1,X2,X3] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/1.04    inference(ennf_transformation,[],[f14])).
% 1.88/1.04  
% 1.88/1.04  fof(f88,plain,(
% 1.88/1.04    ( ! [X2,X0,X3,X1] : (m1_subset_1(k8_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/1.04    inference(cnf_transformation,[],[f42])).
% 1.88/1.04  
% 1.88/1.04  fof(f20,axiom,(
% 1.88/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f50,plain,(
% 1.88/1.04    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.88/1.04    inference(ennf_transformation,[],[f20])).
% 1.88/1.04  
% 1.88/1.04  fof(f51,plain,(
% 1.88/1.04    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.88/1.04    inference(flattening,[],[f50])).
% 1.88/1.04  
% 1.88/1.04  fof(f98,plain,(
% 1.88/1.04    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f51])).
% 1.88/1.04  
% 1.88/1.04  fof(f15,axiom,(
% 1.88/1.04    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f43,plain,(
% 1.88/1.04    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.88/1.04    inference(ennf_transformation,[],[f15])).
% 1.88/1.04  
% 1.88/1.04  fof(f89,plain,(
% 1.88/1.04    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.88/1.04    inference(cnf_transformation,[],[f43])).
% 1.88/1.04  
% 1.88/1.04  fof(f23,axiom,(
% 1.88/1.04    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f55,plain,(
% 1.88/1.04    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.88/1.04    inference(ennf_transformation,[],[f23])).
% 1.88/1.04  
% 1.88/1.04  fof(f56,plain,(
% 1.88/1.04    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.88/1.04    inference(flattening,[],[f55])).
% 1.88/1.04  
% 1.88/1.04  fof(f101,plain,(
% 1.88/1.04    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f56])).
% 1.88/1.04  
% 1.88/1.04  fof(f110,plain,(
% 1.88/1.04    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 1.88/1.04    inference(cnf_transformation,[],[f66])).
% 1.88/1.04  
% 1.88/1.04  fof(f10,axiom,(
% 1.88/1.04    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X0) & k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))) => r1_tarski(k1_relat_1(X0),k2_relat_1(X1)))))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f35,plain,(
% 1.88/1.04    ! [X0] : (! [X1] : ((r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | (~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.88/1.04    inference(ennf_transformation,[],[f10])).
% 1.88/1.04  
% 1.88/1.04  fof(f36,plain,(
% 1.88/1.04    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.88/1.04    inference(flattening,[],[f35])).
% 1.88/1.04  
% 1.88/1.04  fof(f83,plain,(
% 1.88/1.04    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X0),k2_relat_1(X1)) | ~v2_funct_1(X0) | k2_relat_1(X0) != k2_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f36])).
% 1.88/1.04  
% 1.88/1.04  fof(f96,plain,(
% 1.88/1.04    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f51])).
% 1.88/1.04  
% 1.88/1.04  fof(f1,axiom,(
% 1.88/1.04    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.88/1.04    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.88/1.04  
% 1.88/1.04  fof(f59,plain,(
% 1.88/1.04    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.88/1.04    inference(nnf_transformation,[],[f1])).
% 1.88/1.04  
% 1.88/1.04  fof(f60,plain,(
% 1.88/1.04    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.88/1.04    inference(flattening,[],[f59])).
% 1.88/1.04  
% 1.88/1.04  fof(f69,plain,(
% 1.88/1.04    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 1.88/1.04    inference(cnf_transformation,[],[f60])).
% 1.88/1.04  
% 1.88/1.04  cnf(c_36,negated_conjecture,
% 1.88/1.04      ( v2_funct_1(sK2) ),
% 1.88/1.04      inference(cnf_transformation,[],[f109]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1594,plain,
% 1.88/1.04      ( v2_funct_1(sK2) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_12,plain,
% 1.88/1.04      ( ~ v2_funct_1(X0)
% 1.88/1.04      | v2_funct_1(k2_funct_1(X0))
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | ~ v1_relat_1(X0) ),
% 1.88/1.04      inference(cnf_transformation,[],[f81]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1608,plain,
% 1.88/1.04      ( v2_funct_1(X0) != iProver_top
% 1.88/1.04      | v2_funct_1(k2_funct_1(X0)) = iProver_top
% 1.88/1.04      | v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_18,plain,
% 1.88/1.04      ( ~ v2_funct_1(X0)
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | ~ v1_relat_1(X0)
% 1.88/1.04      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 1.88/1.04      inference(cnf_transformation,[],[f84]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1604,plain,
% 1.88/1.04      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
% 1.88/1.04      | v2_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_3254,plain,
% 1.88/1.04      ( k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_relat_1(k1_relat_1(k2_funct_1(X0)))
% 1.88/1.04      | v2_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_funct_1(k2_funct_1(X0)) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_1608,c_1604]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_14,plain,
% 1.88/1.04      ( ~ v2_funct_1(X0)
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | ~ v1_relat_1(X0)
% 1.88/1.04      | v1_relat_1(k2_funct_1(X0)) ),
% 1.88/1.04      inference(cnf_transformation,[],[f79]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_109,plain,
% 1.88/1.04      ( v2_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_13,plain,
% 1.88/1.04      ( ~ v2_funct_1(X0)
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | v1_funct_1(k2_funct_1(X0))
% 1.88/1.04      | ~ v1_relat_1(X0) ),
% 1.88/1.04      inference(cnf_transformation,[],[f80]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_112,plain,
% 1.88/1.04      ( v2_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_10205,plain,
% 1.88/1.04      ( v1_relat_1(X0) != iProver_top
% 1.88/1.04      | k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_relat_1(k1_relat_1(k2_funct_1(X0)))
% 1.88/1.04      | v2_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_funct_1(X0) != iProver_top ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_3254,c_109,c_112]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_10206,plain,
% 1.88/1.04      ( k5_relat_1(k2_funct_1(X0),k2_funct_1(k2_funct_1(X0))) = k6_relat_1(k1_relat_1(k2_funct_1(X0)))
% 1.88/1.04      | v2_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.88/1.04      inference(renaming,[status(thm)],[c_10205]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_10216,plain,
% 1.88/1.04      ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
% 1.88/1.04      | v1_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_1594,c_10206]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_17,plain,
% 1.88/1.04      ( ~ v2_funct_1(X0)
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | ~ v1_relat_1(X0)
% 1.88/1.04      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) ),
% 1.88/1.04      inference(cnf_transformation,[],[f85]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1605,plain,
% 1.88/1.04      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
% 1.88/1.04      | v2_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_3712,plain,
% 1.88/1.04      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
% 1.88/1.04      | v1_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_1594,c_1605]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_40,negated_conjecture,
% 1.88/1.04      ( v1_funct_1(sK2) ),
% 1.88/1.04      inference(cnf_transformation,[],[f105]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_38,negated_conjecture,
% 1.88/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 1.88/1.04      inference(cnf_transformation,[],[f107]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1922,plain,
% 1.88/1.04      ( ~ v2_funct_1(sK2)
% 1.88/1.04      | ~ v1_funct_1(sK2)
% 1.88/1.04      | ~ v1_relat_1(sK2)
% 1.88/1.04      | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_17]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4,plain,
% 1.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 1.88/1.04      inference(cnf_transformation,[],[f70]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2202,plain,
% 1.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.04      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_4]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2878,plain,
% 1.88/1.04      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.88/1.04      | r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_2202]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_5,plain,
% 1.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.88/1.04      | ~ v1_relat_1(X1)
% 1.88/1.04      | v1_relat_1(X0) ),
% 1.88/1.04      inference(cnf_transformation,[],[f72]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_3,plain,
% 1.88/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.88/1.04      inference(cnf_transformation,[],[f71]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_320,plain,
% 1.88/1.04      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 1.88/1.04      inference(prop_impl,[status(thm)],[c_3]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_321,plain,
% 1.88/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 1.88/1.04      inference(renaming,[status(thm)],[c_320]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_382,plain,
% 1.88/1.04      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 1.88/1.04      inference(bin_hyper_res,[status(thm)],[c_5,c_321]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2008,plain,
% 1.88/1.04      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 1.88/1.04      | v1_relat_1(X0)
% 1.88/1.04      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_382]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2925,plain,
% 1.88/1.04      ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 1.88/1.04      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 1.88/1.04      | v1_relat_1(sK2) ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_2008]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_6,plain,
% 1.88/1.04      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.88/1.04      inference(cnf_transformation,[],[f73]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_3656,plain,
% 1.88/1.04      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_6]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4267,plain,
% 1.88/1.04      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_3712,c_40,c_38,c_36,c_1922,c_2878,c_2925,c_3656]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1593,plain,
% 1.88/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_32,plain,
% 1.88/1.04      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 1.88/1.04      inference(cnf_transformation,[],[f99]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_41,negated_conjecture,
% 1.88/1.04      ( l1_struct_0(sK1) ),
% 1.88/1.04      inference(cnf_transformation,[],[f104]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_531,plain,
% 1.88/1.04      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 1.88/1.04      inference(resolution_lifted,[status(thm)],[c_32,c_41]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_532,plain,
% 1.88/1.04      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.88/1.04      inference(unflattening,[status(thm)],[c_531]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_43,negated_conjecture,
% 1.88/1.04      ( l1_struct_0(sK0) ),
% 1.88/1.04      inference(cnf_transformation,[],[f102]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_536,plain,
% 1.88/1.04      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 1.88/1.04      inference(resolution_lifted,[status(thm)],[c_32,c_43]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_537,plain,
% 1.88/1.04      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 1.88/1.04      inference(unflattening,[status(thm)],[c_536]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1639,plain,
% 1.88/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 1.88/1.04      inference(light_normalisation,[status(thm)],[c_1593,c_532,c_537]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_23,plain,
% 1.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.04      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 1.88/1.04      inference(cnf_transformation,[],[f90]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1600,plain,
% 1.88/1.04      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 1.88/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2480,plain,
% 1.88/1.04      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_1639,c_1600]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_37,negated_conjecture,
% 1.88/1.04      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.88/1.04      inference(cnf_transformation,[],[f108]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1636,plain,
% 1.88/1.04      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 1.88/1.04      inference(light_normalisation,[status(thm)],[c_37,c_532,c_537]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2725,plain,
% 1.88/1.04      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_2480,c_1636]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1613,plain,
% 1.88/1.04      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 1.88/1.04      | r1_tarski(X0,X1) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2200,plain,
% 1.88/1.04      ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) = iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_1639,c_1613]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2730,plain,
% 1.88/1.04      ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) = iProver_top ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_2725,c_2200]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1590,plain,
% 1.88/1.04      ( r1_tarski(X0,X1) != iProver_top
% 1.88/1.04      | v1_relat_1(X1) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_382]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_6495,plain,
% 1.88/1.04      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
% 1.88/1.04      | v1_relat_1(sK2) = iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_2730,c_1590]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_49,plain,
% 1.88/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2879,plain,
% 1.88/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.88/1.04      | r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_2878]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2927,plain,
% 1.88/1.04      ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 1.88/1.04      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 1.88/1.04      | v1_relat_1(sK2) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_2925]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_3657,plain,
% 1.88/1.04      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_3656]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_7110,plain,
% 1.88/1.04      ( v1_relat_1(sK2) = iProver_top ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_6495,c_49,c_2879,c_2927,c_3657]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_19,plain,
% 1.88/1.04      ( ~ v2_funct_1(X0)
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | ~ v1_relat_1(X0)
% 1.88/1.04      | k2_funct_1(k2_funct_1(X0)) = X0 ),
% 1.88/1.04      inference(cnf_transformation,[],[f86]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1603,plain,
% 1.88/1.04      ( k2_funct_1(k2_funct_1(X0)) = X0
% 1.88/1.04      | v2_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_3085,plain,
% 1.88/1.04      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 1.88/1.04      | v1_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_1594,c_1603]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_47,plain,
% 1.88/1.04      ( v1_funct_1(sK2) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_3279,plain,
% 1.88/1.04      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_3085,c_47]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_7117,plain,
% 1.88/1.04      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_7110,c_3279]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_10220,plain,
% 1.88/1.04      ( k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2))
% 1.88/1.04      | v1_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(light_normalisation,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_10216,c_4267,c_7117]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_10442,plain,
% 1.88/1.04      ( k6_relat_1(k1_relat_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2)) ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_10220,c_47,c_49,c_2879,c_2927,c_3657]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_8,plain,
% 1.88/1.04      ( k2_relat_1(k6_relat_1(X0)) = X0 ),
% 1.88/1.04      inference(cnf_transformation,[],[f76]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_10446,plain,
% 1.88/1.04      ( k2_relat_1(k6_relat_1(k2_relat_1(sK2))) = k1_relat_1(k2_funct_1(sK2)) ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_10442,c_8]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_10448,plain,
% 1.88/1.04      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_10446,c_8]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1591,plain,
% 1.88/1.04      ( v1_funct_1(sK2) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_11,plain,
% 1.88/1.04      ( ~ v1_funct_1(X0)
% 1.88/1.04      | ~ v1_relat_1(X0)
% 1.88/1.04      | v1_relat_1(k2_funct_1(X0)) ),
% 1.88/1.04      inference(cnf_transformation,[],[f77]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1609,plain,
% 1.88/1.04      ( v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_7,plain,
% 1.88/1.04      ( ~ v1_relat_1(X0)
% 1.88/1.04      | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 1.88/1.04      inference(cnf_transformation,[],[f74]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1611,plain,
% 1.88/1.04      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 1.88/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2679,plain,
% 1.88/1.04      ( k9_relat_1(k2_funct_1(X0),k1_relat_1(k2_funct_1(X0))) = k2_relat_1(k2_funct_1(X0))
% 1.88/1.04      | v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_1609,c_1611]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_7552,plain,
% 1.88/1.04      ( k9_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2))
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_1591,c_2679]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_15,plain,
% 1.88/1.04      ( ~ v2_funct_1(X0)
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | ~ v1_relat_1(X0)
% 1.88/1.04      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 1.88/1.04      inference(cnf_transformation,[],[f82]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1607,plain,
% 1.88/1.04      ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 1.88/1.04      | v2_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_3850,plain,
% 1.88/1.04      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0)
% 1.88/1.04      | v1_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_1594,c_1607]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1930,plain,
% 1.88/1.04      ( ~ v2_funct_1(sK2)
% 1.88/1.04      | ~ v1_funct_1(sK2)
% 1.88/1.04      | ~ v1_relat_1(sK2)
% 1.88/1.04      | k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_15]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4271,plain,
% 1.88/1.04      ( k9_relat_1(k2_funct_1(sK2),X0) = k10_relat_1(sK2,X0) ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_3850,c_40,c_38,c_36,c_1930,c_2878,c_2925,c_3656]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_7559,plain,
% 1.88/1.04      ( k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2))
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_7552,c_4271]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_7745,plain,
% 1.88/1.04      ( k10_relat_1(sK2,k1_relat_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_7559,c_49,c_2879,c_2927,c_3657]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_25,plain,
% 1.88/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.88/1.04      | v1_partfun1(X0,X1)
% 1.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.04      | v1_xboole_0(X2)
% 1.88/1.04      | ~ v1_funct_1(X0) ),
% 1.88/1.04      inference(cnf_transformation,[],[f93]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_33,plain,
% 1.88/1.04      ( v2_struct_0(X0)
% 1.88/1.04      | ~ l1_struct_0(X0)
% 1.88/1.04      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 1.88/1.04      inference(cnf_transformation,[],[f100]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_42,negated_conjecture,
% 1.88/1.04      ( ~ v2_struct_0(sK1) ),
% 1.88/1.04      inference(cnf_transformation,[],[f103]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_518,plain,
% 1.88/1.04      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 1.88/1.04      inference(resolution_lifted,[status(thm)],[c_33,c_42]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_519,plain,
% 1.88/1.04      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 1.88/1.04      inference(unflattening,[status(thm)],[c_518]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_55,plain,
% 1.88/1.04      ( v2_struct_0(sK1)
% 1.88/1.04      | ~ l1_struct_0(sK1)
% 1.88/1.04      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_33]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_521,plain,
% 1.88/1.04      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_519,c_42,c_41,c_55]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_543,plain,
% 1.88/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.88/1.04      | v1_partfun1(X0,X1)
% 1.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | k2_struct_0(sK1) != X2 ),
% 1.88/1.04      inference(resolution_lifted,[status(thm)],[c_25,c_521]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_544,plain,
% 1.88/1.04      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 1.88/1.04      | v1_partfun1(X0,X1)
% 1.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 1.88/1.04      | ~ v1_funct_1(X0) ),
% 1.88/1.04      inference(unflattening,[status(thm)],[c_543]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_28,plain,
% 1.88/1.04      ( ~ v1_partfun1(X0,X1)
% 1.88/1.04      | ~ v4_relat_1(X0,X1)
% 1.88/1.04      | ~ v1_relat_1(X0)
% 1.88/1.04      | k1_relat_1(X0) = X1 ),
% 1.88/1.04      inference(cnf_transformation,[],[f94]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_605,plain,
% 1.88/1.04      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 1.88/1.04      | ~ v4_relat_1(X0,X1)
% 1.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | ~ v1_relat_1(X0)
% 1.88/1.04      | k1_relat_1(X0) = X1 ),
% 1.88/1.04      inference(resolution,[status(thm)],[c_544,c_28]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_20,plain,
% 1.88/1.04      ( v4_relat_1(X0,X1)
% 1.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 1.88/1.04      inference(cnf_transformation,[],[f87]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_621,plain,
% 1.88/1.04      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 1.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | ~ v1_relat_1(X0)
% 1.88/1.04      | k1_relat_1(X0) = X1 ),
% 1.88/1.04      inference(forward_subsumption_resolution,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_605,c_20]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1589,plain,
% 1.88/1.04      ( k1_relat_1(X0) = X1
% 1.88/1.04      | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
% 1.88/1.04      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
% 1.88/1.04      | v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_621]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1985,plain,
% 1.88/1.04      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 1.88/1.04      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 1.88/1.04      | v1_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_1639,c_1589]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_39,negated_conjecture,
% 1.88/1.04      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 1.88/1.04      inference(cnf_transformation,[],[f106]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1592,plain,
% 1.88/1.04      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1633,plain,
% 1.88/1.04      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 1.88/1.04      inference(light_normalisation,[status(thm)],[c_1592,c_532,c_537]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2138,plain,
% 1.88/1.04      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_1985,c_47,c_1633]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_7118,plain,
% 1.88/1.04      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_7110,c_2138]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2732,plain,
% 1.88/1.04      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_2725,c_1639]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_24,plain,
% 1.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.04      | k8_relset_1(X1,X2,X0,X3) = k10_relat_1(X0,X3) ),
% 1.88/1.04      inference(cnf_transformation,[],[f91]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1599,plain,
% 1.88/1.04      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
% 1.88/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_3384,plain,
% 1.88/1.04      ( k8_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2,X0) = k10_relat_1(sK2,X0) ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_2732,c_1599]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_21,plain,
% 1.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.04      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) ),
% 1.88/1.04      inference(cnf_transformation,[],[f88]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1602,plain,
% 1.88/1.04      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 1.88/1.04      | m1_subset_1(k8_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X1)) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_3642,plain,
% 1.88/1.04      ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top
% 1.88/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_3384,c_1602]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4473,plain,
% 1.88/1.04      ( m1_subset_1(k10_relat_1(sK2,X0),k1_zfmisc_1(k2_struct_0(sK0))) = iProver_top ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_3642,c_2732]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4480,plain,
% 1.88/1.04      ( r1_tarski(k10_relat_1(sK2,X0),k2_struct_0(sK0)) = iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_4473,c_1613]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_7170,plain,
% 1.88/1.04      ( r1_tarski(k10_relat_1(sK2,X0),k1_relat_1(sK2)) = iProver_top ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_7118,c_4480]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_8025,plain,
% 1.88/1.04      ( r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) = iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_7745,c_7170]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2727,plain,
% 1.88/1.04      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_2725,c_2480]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_29,plain,
% 1.88/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.04      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 1.88/1.04      | ~ v2_funct_1(X0)
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.88/1.04      inference(cnf_transformation,[],[f98]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1598,plain,
% 1.88/1.04      ( k2_relset_1(X0,X1,X2) != X1
% 1.88/1.04      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.88/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.88/1.04      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 1.88/1.04      | v2_funct_1(X2) != iProver_top
% 1.88/1.04      | v1_funct_1(X2) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4563,plain,
% 1.88/1.04      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.88/1.04      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top
% 1.88/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.88/1.04      | v2_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_funct_1(sK2) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_2727,c_1598]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_50,plain,
% 1.88/1.04      ( v2_funct_1(sK2) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2733,plain,
% 1.88/1.04      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_2725,c_1633]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4929,plain,
% 1.88/1.04      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) = iProver_top ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_4563,c_47,c_50,c_2732,c_2733]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4937,plain,
% 1.88/1.04      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_4929,c_1600]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_22,plain,
% 1.88/1.04      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.04      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 1.88/1.04      inference(cnf_transformation,[],[f89]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1601,plain,
% 1.88/1.04      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 1.88/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4936,plain,
% 1.88/1.04      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_4929,c_1601]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_34,plain,
% 1.88/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.04      | ~ v2_funct_1(X0)
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 1.88/1.04      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.88/1.04      inference(cnf_transformation,[],[f101]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1595,plain,
% 1.88/1.04      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 1.88/1.04      | k2_relset_1(X0,X1,X2) != X1
% 1.88/1.04      | v1_funct_2(X2,X0,X1) != iProver_top
% 1.88/1.04      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 1.88/1.04      | v2_funct_1(X2) != iProver_top
% 1.88/1.04      | v1_funct_1(X2) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4021,plain,
% 1.88/1.04      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 1.88/1.04      | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 1.88/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 1.88/1.04      | v2_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_funct_1(sK2) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_2727,c_1595]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4315,plain,
% 1.88/1.04      ( k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_4021,c_47,c_50,c_2732,c_2733]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_35,negated_conjecture,
% 1.88/1.04      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 1.88/1.04      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 1.88/1.04      inference(cnf_transformation,[],[f110]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1734,plain,
% 1.88/1.04      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 1.88/1.04      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 1.88/1.04      inference(light_normalisation,[status(thm)],[c_35,c_532,c_537]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2734,plain,
% 1.88/1.04      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_struct_0(sK0)
% 1.88/1.04      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2) ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_2725,c_1734]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4318,plain,
% 1.88/1.04      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 1.88/1.04      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_4315,c_2734]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_5074,plain,
% 1.88/1.04      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 1.88/1.04      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_4936,c_4318]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_5207,plain,
% 1.88/1.04      ( k2_relat_1(k2_funct_1(sK2)) != k2_struct_0(sK0)
% 1.88/1.04      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_4937,c_5074]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_7164,plain,
% 1.88/1.04      ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 1.88/1.04      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_7118,c_5207]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_16,plain,
% 1.88/1.04      ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
% 1.88/1.04      | ~ v2_funct_1(X0)
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | ~ v1_funct_1(X1)
% 1.88/1.04      | ~ v1_relat_1(X0)
% 1.88/1.04      | ~ v1_relat_1(X1)
% 1.88/1.04      | k2_relat_1(k5_relat_1(X1,X0)) != k2_relat_1(X0) ),
% 1.88/1.04      inference(cnf_transformation,[],[f83]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1606,plain,
% 1.88/1.04      ( k2_relat_1(k5_relat_1(X0,X1)) != k2_relat_1(X1)
% 1.88/1.04      | r1_tarski(k1_relat_1(X1),k2_relat_1(X0)) = iProver_top
% 1.88/1.04      | v2_funct_1(X1) != iProver_top
% 1.88/1.04      | v1_funct_1(X1) != iProver_top
% 1.88/1.04      | v1_funct_1(X0) != iProver_top
% 1.88/1.04      | v1_relat_1(X1) != iProver_top
% 1.88/1.04      | v1_relat_1(X0) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4552,plain,
% 1.88/1.04      ( k2_relat_1(k6_relat_1(k2_relat_1(sK2))) != k2_relat_1(sK2)
% 1.88/1.04      | r1_tarski(k1_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top
% 1.88/1.04      | v2_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.88/1.04      | v1_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_4267,c_1606]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4553,plain,
% 1.88/1.04      ( k2_relat_1(sK2) != k2_relat_1(sK2)
% 1.88/1.04      | r1_tarski(k1_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top
% 1.88/1.04      | v2_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.88/1.04      | v1_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(demodulation,[status(thm)],[c_4552,c_8]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_4554,plain,
% 1.88/1.04      ( r1_tarski(k1_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top
% 1.88/1.04      | v2_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 1.88/1.04      | v1_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(equality_resolution_simp,[status(thm)],[c_4553]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_48,plain,
% 1.88/1.04      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_58,plain,
% 1.88/1.04      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_32]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1885,plain,
% 1.88/1.04      ( ~ v1_funct_1(sK2)
% 1.88/1.04      | v1_relat_1(k2_funct_1(sK2))
% 1.88/1.04      | ~ v1_relat_1(sK2) ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_11]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1886,plain,
% 1.88/1.04      ( v1_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 1.88/1.04      | v1_relat_1(sK2) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_1885]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_31,plain,
% 1.88/1.04      ( ~ v1_funct_2(X0,X1,X2)
% 1.88/1.04      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.88/1.04      | ~ v2_funct_1(X0)
% 1.88/1.04      | ~ v1_funct_1(X0)
% 1.88/1.04      | v1_funct_1(k2_funct_1(X0))
% 1.88/1.04      | k2_relset_1(X1,X2,X0) != X2 ),
% 1.88/1.04      inference(cnf_transformation,[],[f96]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1988,plain,
% 1.88/1.04      ( ~ v1_funct_2(sK2,X0,X1)
% 1.88/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 1.88/1.04      | ~ v2_funct_1(sK2)
% 1.88/1.04      | v1_funct_1(k2_funct_1(sK2))
% 1.88/1.04      | ~ v1_funct_1(sK2)
% 1.88/1.04      | k2_relset_1(X0,X1,sK2) != X1 ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_31]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2180,plain,
% 1.88/1.04      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 1.88/1.04      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 1.88/1.04      | ~ v2_funct_1(sK2)
% 1.88/1.04      | v1_funct_1(k2_funct_1(sK2))
% 1.88/1.04      | ~ v1_funct_1(sK2)
% 1.88/1.04      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_1988]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2181,plain,
% 1.88/1.04      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 1.88/1.04      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 1.88/1.04      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 1.88/1.04      | v2_funct_1(sK2) != iProver_top
% 1.88/1.04      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 1.88/1.04      | v1_funct_1(sK2) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_2180]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_891,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2471,plain,
% 1.88/1.04      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 1.88/1.04      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 1.88/1.04      | u1_struct_0(sK1) != X0 ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_891]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_2942,plain,
% 1.88/1.04      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 1.88/1.04      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 1.88/1.04      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 1.88/1.04      inference(instantiation,[status(thm)],[c_2471]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_5615,plain,
% 1.88/1.04      ( r1_tarski(k1_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) = iProver_top ),
% 1.88/1.04      inference(global_propositional_subsumption,
% 1.88/1.04                [status(thm)],
% 1.88/1.04                [c_4554,c_41,c_47,c_48,c_49,c_37,c_50,c_58,c_1886,c_2181,
% 1.88/1.04                 c_2879,c_2927,c_2942,c_3657]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_0,plain,
% 1.88/1.04      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 1.88/1.04      inference(cnf_transformation,[],[f69]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_1616,plain,
% 1.88/1.04      ( X0 = X1
% 1.88/1.04      | r1_tarski(X0,X1) != iProver_top
% 1.88/1.04      | r1_tarski(X1,X0) != iProver_top ),
% 1.88/1.04      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(c_5620,plain,
% 1.88/1.04      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 1.88/1.04      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),k1_relat_1(sK2)) != iProver_top ),
% 1.88/1.04      inference(superposition,[status(thm)],[c_5615,c_1616]) ).
% 1.88/1.04  
% 1.88/1.04  cnf(contradiction,plain,
% 1.88/1.04      ( $false ),
% 1.88/1.04      inference(minisat,[status(thm)],[c_10448,c_8025,c_7164,c_5620]) ).
% 1.88/1.04  
% 1.88/1.04  
% 1.88/1.04  % SZS output end CNFRefutation for theBenchmark.p
% 1.88/1.04  
% 1.88/1.04  ------                               Statistics
% 1.88/1.04  
% 1.88/1.04  ------ General
% 1.88/1.04  
% 1.88/1.04  abstr_ref_over_cycles:                  0
% 1.88/1.04  abstr_ref_under_cycles:                 0
% 1.88/1.04  gc_basic_clause_elim:                   0
% 1.88/1.04  forced_gc_time:                         0
% 1.88/1.04  parsing_time:                           0.014
% 1.88/1.04  unif_index_cands_time:                  0.
% 1.88/1.04  unif_index_add_time:                    0.
% 1.88/1.04  orderings_time:                         0.
% 1.88/1.04  out_proof_time:                         0.014
% 1.88/1.04  total_time:                             0.387
% 1.88/1.04  num_of_symbols:                         60
% 1.88/1.04  num_of_terms:                           9863
% 1.88/1.04  
% 1.88/1.04  ------ Preprocessing
% 1.88/1.04  
% 1.88/1.04  num_of_splits:                          0
% 1.88/1.04  num_of_split_atoms:                     0
% 1.88/1.04  num_of_reused_defs:                     0
% 1.88/1.04  num_eq_ax_congr_red:                    20
% 1.88/1.04  num_of_sem_filtered_clauses:            1
% 1.88/1.04  num_of_subtypes:                        0
% 1.88/1.04  monotx_restored_types:                  0
% 1.88/1.04  sat_num_of_epr_types:                   0
% 1.88/1.04  sat_num_of_non_cyclic_types:            0
% 1.88/1.04  sat_guarded_non_collapsed_types:        0
% 1.88/1.04  num_pure_diseq_elim:                    0
% 1.88/1.04  simp_replaced_by:                       0
% 1.88/1.04  res_preprocessed:                       185
% 1.88/1.04  prep_upred:                             0
% 1.88/1.04  prep_unflattend:                        8
% 1.88/1.04  smt_new_axioms:                         0
% 1.88/1.04  pred_elim_cands:                        6
% 1.88/1.04  pred_elim:                              5
% 1.88/1.04  pred_elim_cl:                           6
% 1.88/1.04  pred_elim_cycles:                       8
% 1.88/1.04  merged_defs:                            8
% 1.88/1.04  merged_defs_ncl:                        0
% 1.88/1.04  bin_hyper_res:                          9
% 1.88/1.04  prep_cycles:                            4
% 1.88/1.04  pred_elim_time:                         0.007
% 1.88/1.04  splitting_time:                         0.
% 1.88/1.04  sem_filter_time:                        0.
% 1.88/1.04  monotx_time:                            0.
% 1.88/1.04  subtype_inf_time:                       0.
% 1.88/1.04  
% 1.88/1.04  ------ Problem properties
% 1.88/1.04  
% 1.88/1.04  clauses:                                34
% 1.88/1.04  conjectures:                            6
% 1.88/1.04  epr:                                    5
% 1.88/1.04  horn:                                   34
% 1.88/1.04  ground:                                 8
% 1.88/1.04  unary:                                  11
% 1.88/1.04  binary:                                 8
% 1.88/1.04  lits:                                   95
% 1.88/1.04  lits_eq:                                23
% 1.88/1.04  fd_pure:                                0
% 1.88/1.04  fd_pseudo:                              0
% 1.88/1.04  fd_cond:                                0
% 1.88/1.04  fd_pseudo_cond:                         2
% 1.88/1.04  ac_symbols:                             0
% 1.88/1.04  
% 1.88/1.04  ------ Propositional Solver
% 1.88/1.04  
% 1.88/1.04  prop_solver_calls:                      29
% 1.88/1.04  prop_fast_solver_calls:                 1459
% 1.88/1.04  smt_solver_calls:                       0
% 1.88/1.04  smt_fast_solver_calls:                  0
% 1.88/1.04  prop_num_of_clauses:                    4320
% 1.88/1.04  prop_preprocess_simplified:             10501
% 1.88/1.04  prop_fo_subsumed:                       67
% 1.88/1.04  prop_solver_time:                       0.
% 1.88/1.04  smt_solver_time:                        0.
% 1.88/1.04  smt_fast_solver_time:                   0.
% 1.88/1.04  prop_fast_solver_time:                  0.
% 1.88/1.04  prop_unsat_core_time:                   0.
% 1.88/1.04  
% 1.88/1.04  ------ QBF
% 1.88/1.04  
% 1.88/1.04  qbf_q_res:                              0
% 1.88/1.04  qbf_num_tautologies:                    0
% 1.88/1.04  qbf_prep_cycles:                        0
% 1.88/1.04  
% 1.88/1.04  ------ BMC1
% 1.88/1.04  
% 1.88/1.04  bmc1_current_bound:                     -1
% 1.88/1.04  bmc1_last_solved_bound:                 -1
% 1.88/1.04  bmc1_unsat_core_size:                   -1
% 1.88/1.04  bmc1_unsat_core_parents_size:           -1
% 1.88/1.04  bmc1_merge_next_fun:                    0
% 1.88/1.04  bmc1_unsat_core_clauses_time:           0.
% 1.88/1.04  
% 1.88/1.04  ------ Instantiation
% 1.88/1.04  
% 1.88/1.04  inst_num_of_clauses:                    1495
% 1.88/1.04  inst_num_in_passive:                    245
% 1.88/1.04  inst_num_in_active:                     663
% 1.88/1.04  inst_num_in_unprocessed:                588
% 1.88/1.04  inst_num_of_loops:                      710
% 1.88/1.04  inst_num_of_learning_restarts:          0
% 1.88/1.04  inst_num_moves_active_passive:          43
% 1.88/1.04  inst_lit_activity:                      0
% 1.88/1.04  inst_lit_activity_moves:                0
% 1.88/1.04  inst_num_tautologies:                   0
% 1.88/1.04  inst_num_prop_implied:                  0
% 1.88/1.04  inst_num_existing_simplified:           0
% 1.88/1.04  inst_num_eq_res_simplified:             0
% 1.88/1.04  inst_num_child_elim:                    0
% 1.88/1.04  inst_num_of_dismatching_blockings:      340
% 1.88/1.04  inst_num_of_non_proper_insts:           1426
% 1.88/1.04  inst_num_of_duplicates:                 0
% 1.88/1.04  inst_inst_num_from_inst_to_res:         0
% 1.88/1.04  inst_dismatching_checking_time:         0.
% 1.88/1.04  
% 1.88/1.04  ------ Resolution
% 1.88/1.04  
% 1.88/1.04  res_num_of_clauses:                     0
% 1.88/1.04  res_num_in_passive:                     0
% 1.88/1.04  res_num_in_active:                      0
% 1.88/1.04  res_num_of_loops:                       189
% 1.88/1.04  res_forward_subset_subsumed:            105
% 1.88/1.04  res_backward_subset_subsumed:           6
% 1.88/1.04  res_forward_subsumed:                   0
% 1.88/1.04  res_backward_subsumed:                  0
% 1.88/1.04  res_forward_subsumption_resolution:     1
% 1.88/1.04  res_backward_subsumption_resolution:    0
% 1.88/1.04  res_clause_to_clause_subsumption:       393
% 1.88/1.04  res_orphan_elimination:                 0
% 1.88/1.04  res_tautology_del:                      120
% 1.88/1.04  res_num_eq_res_simplified:              0
% 1.88/1.04  res_num_sel_changes:                    0
% 1.88/1.04  res_moves_from_active_to_pass:          0
% 1.88/1.04  
% 1.88/1.04  ------ Superposition
% 1.88/1.04  
% 1.88/1.04  sup_time_total:                         0.
% 1.88/1.04  sup_time_generating:                    0.
% 1.88/1.04  sup_time_sim_full:                      0.
% 1.88/1.04  sup_time_sim_immed:                     0.
% 1.88/1.04  
% 1.88/1.04  sup_num_of_clauses:                     143
% 1.88/1.04  sup_num_in_active:                      96
% 1.88/1.04  sup_num_in_passive:                     47
% 1.88/1.04  sup_num_of_loops:                       141
% 1.88/1.04  sup_fw_superposition:                   76
% 1.88/1.04  sup_bw_superposition:                   129
% 1.88/1.04  sup_immediate_simplified:               47
% 1.88/1.04  sup_given_eliminated:                   2
% 1.88/1.04  comparisons_done:                       0
% 1.88/1.04  comparisons_avoided:                    0
% 1.88/1.04  
% 1.88/1.04  ------ Simplifications
% 1.88/1.04  
% 1.88/1.04  
% 1.88/1.04  sim_fw_subset_subsumed:                 19
% 1.88/1.04  sim_bw_subset_subsumed:                 4
% 1.88/1.04  sim_fw_subsumed:                        7
% 1.88/1.04  sim_bw_subsumed:                        0
% 1.88/1.04  sim_fw_subsumption_res:                 2
% 1.88/1.04  sim_bw_subsumption_res:                 0
% 1.88/1.04  sim_tautology_del:                      4
% 1.88/1.04  sim_eq_tautology_del:                   8
% 1.88/1.04  sim_eq_res_simp:                        3
% 1.88/1.04  sim_fw_demodulated:                     14
% 1.88/1.04  sim_bw_demodulated:                     48
% 1.88/1.04  sim_light_normalised:                   17
% 1.88/1.04  sim_joinable_taut:                      0
% 1.88/1.04  sim_joinable_simp:                      0
% 1.88/1.04  sim_ac_normalised:                      0
% 1.88/1.04  sim_smt_subsumption:                    0
% 1.88/1.04  
%------------------------------------------------------------------------------
