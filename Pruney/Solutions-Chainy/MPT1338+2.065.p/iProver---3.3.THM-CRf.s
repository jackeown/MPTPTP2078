%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:13 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :  173 (2153 expanded)
%              Number of clauses        :  105 ( 686 expanded)
%              Number of leaves         :   18 ( 602 expanded)
%              Depth                    :   24
%              Number of atoms          :  521 (14153 expanded)
%              Number of equality atoms :  186 (4644 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f21,conjecture,(
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

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f49,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f50,plain,(
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
    inference(flattening,[],[f49])).

fof(f58,plain,(
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

fof(f57,plain,(
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

fof(f56,plain,
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

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f58,f57,f56])).

fof(f93,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f85,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f90,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f88,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f94,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f68,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f36,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f76,plain,(
    ! [X0] :
      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f95,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f91,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f72,plain,(
    ! [X0] :
      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f73,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f42])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f43])).

fof(f83,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f40])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f86,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f89,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f13])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f96,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_31,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1781,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_25,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_34,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_466,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_34])).

cnf(c_467,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_466])).

cnf(c_36,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_471,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_472,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_471])).

cnf(c_1811,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1781,c_467,c_472])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1782,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2573,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1811,c_1782])).

cnf(c_30,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1808,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_30,c_467,c_472])).

cnf(c_2878,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2573,c_1808])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1794,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2234,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1811,c_1794])).

cnf(c_2881,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2878,c_2234])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_3,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_270,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_3])).

cnf(c_271,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_270])).

cnf(c_329,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_5,c_271])).

cnf(c_1779,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_329])).

cnf(c_4728,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_2881,c_1779])).

cnf(c_42,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2138,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_2353,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_2138])).

cnf(c_2354,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2353])).

cnf(c_2047,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_329])).

cnf(c_2443,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2047])).

cnf(c_2445,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2443])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2818,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2819,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2818])).

cnf(c_4746,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4728,c_42,c_2354,c_2445,c_2819])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_29,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_553,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_554,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_553])).

cnf(c_33,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_556,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_554,c_33])).

cnf(c_1777,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_556])).

cnf(c_4758,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4746,c_1777])).

cnf(c_12,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1787,plain,
    ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4877,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4758,c_1787])).

cnf(c_40,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1975,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_1976,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1975])).

cnf(c_5832,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4877,c_40,c_42,c_1976,c_2354,c_2445,c_2819])).

cnf(c_16,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_567,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_568,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(unflattening,[status(thm)],[c_567])).

cnf(c_570,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_568,c_33])).

cnf(c_1776,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_570])).

cnf(c_4759,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4746,c_1776])).

cnf(c_5836,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5832,c_4759])).

cnf(c_1795,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1783,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_2586,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_1783])).

cnf(c_5842,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5836,c_2586])).

cnf(c_5848,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5842,c_4758])).

cnf(c_2572,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_1782])).

cnf(c_5843,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_5836,c_2572])).

cnf(c_5845,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(light_normalisation,[status(thm)],[c_5843,c_4759])).

cnf(c_24,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_32,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_26,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_35,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_453,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_35])).

cnf(c_454,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_453])).

cnf(c_48,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_456,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_454,c_35,c_34,c_48])).

cnf(c_478,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_456])).

cnf(c_479,plain,
    ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_478])).

cnf(c_512,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_32,c_479])).

cnf(c_513,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_512])).

cnf(c_51,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_515,plain,
    ( v1_partfun1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_513,c_34,c_33,c_51])).

cnf(c_533,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_relat_1(X0)
    | u1_struct_0(sK0) != X1
    | k1_relat_1(X0) = X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_515])).

cnf(c_534,plain,
    ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_533])).

cnf(c_18,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_544,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = u1_struct_0(sK0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_534,c_18])).

cnf(c_1778,plain,
    ( k1_relat_1(sK2) = u1_struct_0(sK0)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_544])).

cnf(c_1906,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1778,c_472])).

cnf(c_1907,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1906,c_472])).

cnf(c_1911,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1907,c_1811])).

cnf(c_4757,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_4746,c_1911])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_501,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2
    | u1_struct_0(sK0) != X1
    | u1_struct_0(sK1) != X2
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_27,c_32])).

cnf(c_502,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_501])).

cnf(c_504,plain,
    ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_502,c_33,c_31,c_29])).

cnf(c_1896,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_504,c_467,c_472,c_1808])).

cnf(c_1897,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_1896])).

cnf(c_1914,plain,
    ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_28,c_467,c_472,c_1897])).

cnf(c_2884,plain,
    ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
    | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2878,c_1914])).

cnf(c_5319,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_4757,c_2884])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_5848,c_5845,c_5319])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 2.78/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.78/1.00  
% 2.78/1.00  ------  iProver source info
% 2.78/1.00  
% 2.78/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.78/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.78/1.00  git: non_committed_changes: false
% 2.78/1.00  git: last_make_outside_of_git: false
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options
% 2.78/1.00  
% 2.78/1.00  --out_options                           all
% 2.78/1.00  --tptp_safe_out                         true
% 2.78/1.00  --problem_path                          ""
% 2.78/1.00  --include_path                          ""
% 2.78/1.00  --clausifier                            res/vclausify_rel
% 2.78/1.00  --clausifier_options                    --mode clausify
% 2.78/1.00  --stdin                                 false
% 2.78/1.00  --stats_out                             all
% 2.78/1.00  
% 2.78/1.00  ------ General Options
% 2.78/1.00  
% 2.78/1.00  --fof                                   false
% 2.78/1.00  --time_out_real                         305.
% 2.78/1.00  --time_out_virtual                      -1.
% 2.78/1.00  --symbol_type_check                     false
% 2.78/1.00  --clausify_out                          false
% 2.78/1.00  --sig_cnt_out                           false
% 2.78/1.00  --trig_cnt_out                          false
% 2.78/1.00  --trig_cnt_out_tolerance                1.
% 2.78/1.00  --trig_cnt_out_sk_spl                   false
% 2.78/1.00  --abstr_cl_out                          false
% 2.78/1.00  
% 2.78/1.00  ------ Global Options
% 2.78/1.00  
% 2.78/1.00  --schedule                              default
% 2.78/1.00  --add_important_lit                     false
% 2.78/1.00  --prop_solver_per_cl                    1000
% 2.78/1.00  --min_unsat_core                        false
% 2.78/1.00  --soft_assumptions                      false
% 2.78/1.00  --soft_lemma_size                       3
% 2.78/1.00  --prop_impl_unit_size                   0
% 2.78/1.00  --prop_impl_unit                        []
% 2.78/1.00  --share_sel_clauses                     true
% 2.78/1.00  --reset_solvers                         false
% 2.78/1.00  --bc_imp_inh                            [conj_cone]
% 2.78/1.00  --conj_cone_tolerance                   3.
% 2.78/1.00  --extra_neg_conj                        none
% 2.78/1.00  --large_theory_mode                     true
% 2.78/1.00  --prolific_symb_bound                   200
% 2.78/1.00  --lt_threshold                          2000
% 2.78/1.00  --clause_weak_htbl                      true
% 2.78/1.00  --gc_record_bc_elim                     false
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing Options
% 2.78/1.00  
% 2.78/1.00  --preprocessing_flag                    true
% 2.78/1.00  --time_out_prep_mult                    0.1
% 2.78/1.00  --splitting_mode                        input
% 2.78/1.00  --splitting_grd                         true
% 2.78/1.00  --splitting_cvd                         false
% 2.78/1.00  --splitting_cvd_svl                     false
% 2.78/1.00  --splitting_nvd                         32
% 2.78/1.00  --sub_typing                            true
% 2.78/1.00  --prep_gs_sim                           true
% 2.78/1.00  --prep_unflatten                        true
% 2.78/1.00  --prep_res_sim                          true
% 2.78/1.00  --prep_upred                            true
% 2.78/1.00  --prep_sem_filter                       exhaustive
% 2.78/1.00  --prep_sem_filter_out                   false
% 2.78/1.00  --pred_elim                             true
% 2.78/1.00  --res_sim_input                         true
% 2.78/1.00  --eq_ax_congr_red                       true
% 2.78/1.00  --pure_diseq_elim                       true
% 2.78/1.00  --brand_transform                       false
% 2.78/1.00  --non_eq_to_eq                          false
% 2.78/1.00  --prep_def_merge                        true
% 2.78/1.00  --prep_def_merge_prop_impl              false
% 2.78/1.00  --prep_def_merge_mbd                    true
% 2.78/1.00  --prep_def_merge_tr_red                 false
% 2.78/1.00  --prep_def_merge_tr_cl                  false
% 2.78/1.00  --smt_preprocessing                     true
% 2.78/1.00  --smt_ac_axioms                         fast
% 2.78/1.00  --preprocessed_out                      false
% 2.78/1.00  --preprocessed_stats                    false
% 2.78/1.00  
% 2.78/1.00  ------ Abstraction refinement Options
% 2.78/1.00  
% 2.78/1.00  --abstr_ref                             []
% 2.78/1.00  --abstr_ref_prep                        false
% 2.78/1.00  --abstr_ref_until_sat                   false
% 2.78/1.00  --abstr_ref_sig_restrict                funpre
% 2.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.00  --abstr_ref_under                       []
% 2.78/1.00  
% 2.78/1.00  ------ SAT Options
% 2.78/1.00  
% 2.78/1.00  --sat_mode                              false
% 2.78/1.00  --sat_fm_restart_options                ""
% 2.78/1.00  --sat_gr_def                            false
% 2.78/1.00  --sat_epr_types                         true
% 2.78/1.00  --sat_non_cyclic_types                  false
% 2.78/1.00  --sat_finite_models                     false
% 2.78/1.00  --sat_fm_lemmas                         false
% 2.78/1.00  --sat_fm_prep                           false
% 2.78/1.00  --sat_fm_uc_incr                        true
% 2.78/1.00  --sat_out_model                         small
% 2.78/1.00  --sat_out_clauses                       false
% 2.78/1.00  
% 2.78/1.00  ------ QBF Options
% 2.78/1.00  
% 2.78/1.00  --qbf_mode                              false
% 2.78/1.00  --qbf_elim_univ                         false
% 2.78/1.00  --qbf_dom_inst                          none
% 2.78/1.00  --qbf_dom_pre_inst                      false
% 2.78/1.00  --qbf_sk_in                             false
% 2.78/1.00  --qbf_pred_elim                         true
% 2.78/1.00  --qbf_split                             512
% 2.78/1.00  
% 2.78/1.00  ------ BMC1 Options
% 2.78/1.00  
% 2.78/1.00  --bmc1_incremental                      false
% 2.78/1.00  --bmc1_axioms                           reachable_all
% 2.78/1.00  --bmc1_min_bound                        0
% 2.78/1.00  --bmc1_max_bound                        -1
% 2.78/1.00  --bmc1_max_bound_default                -1
% 2.78/1.00  --bmc1_symbol_reachability              true
% 2.78/1.00  --bmc1_property_lemmas                  false
% 2.78/1.00  --bmc1_k_induction                      false
% 2.78/1.00  --bmc1_non_equiv_states                 false
% 2.78/1.00  --bmc1_deadlock                         false
% 2.78/1.00  --bmc1_ucm                              false
% 2.78/1.00  --bmc1_add_unsat_core                   none
% 2.78/1.00  --bmc1_unsat_core_children              false
% 2.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.00  --bmc1_out_stat                         full
% 2.78/1.00  --bmc1_ground_init                      false
% 2.78/1.00  --bmc1_pre_inst_next_state              false
% 2.78/1.00  --bmc1_pre_inst_state                   false
% 2.78/1.00  --bmc1_pre_inst_reach_state             false
% 2.78/1.00  --bmc1_out_unsat_core                   false
% 2.78/1.00  --bmc1_aig_witness_out                  false
% 2.78/1.00  --bmc1_verbose                          false
% 2.78/1.00  --bmc1_dump_clauses_tptp                false
% 2.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.00  --bmc1_dump_file                        -
% 2.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.00  --bmc1_ucm_extend_mode                  1
% 2.78/1.00  --bmc1_ucm_init_mode                    2
% 2.78/1.00  --bmc1_ucm_cone_mode                    none
% 2.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.00  --bmc1_ucm_relax_model                  4
% 2.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.00  --bmc1_ucm_layered_model                none
% 2.78/1.00  --bmc1_ucm_max_lemma_size               10
% 2.78/1.00  
% 2.78/1.00  ------ AIG Options
% 2.78/1.00  
% 2.78/1.00  --aig_mode                              false
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation Options
% 2.78/1.00  
% 2.78/1.00  --instantiation_flag                    true
% 2.78/1.00  --inst_sos_flag                         false
% 2.78/1.00  --inst_sos_phase                        true
% 2.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel_side                     num_symb
% 2.78/1.00  --inst_solver_per_active                1400
% 2.78/1.00  --inst_solver_calls_frac                1.
% 2.78/1.00  --inst_passive_queue_type               priority_queues
% 2.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.00  --inst_passive_queues_freq              [25;2]
% 2.78/1.00  --inst_dismatching                      true
% 2.78/1.00  --inst_eager_unprocessed_to_passive     true
% 2.78/1.00  --inst_prop_sim_given                   true
% 2.78/1.00  --inst_prop_sim_new                     false
% 2.78/1.00  --inst_subs_new                         false
% 2.78/1.00  --inst_eq_res_simp                      false
% 2.78/1.00  --inst_subs_given                       false
% 2.78/1.00  --inst_orphan_elimination               true
% 2.78/1.00  --inst_learning_loop_flag               true
% 2.78/1.00  --inst_learning_start                   3000
% 2.78/1.00  --inst_learning_factor                  2
% 2.78/1.00  --inst_start_prop_sim_after_learn       3
% 2.78/1.00  --inst_sel_renew                        solver
% 2.78/1.00  --inst_lit_activity_flag                true
% 2.78/1.00  --inst_restr_to_given                   false
% 2.78/1.00  --inst_activity_threshold               500
% 2.78/1.00  --inst_out_proof                        true
% 2.78/1.00  
% 2.78/1.00  ------ Resolution Options
% 2.78/1.00  
% 2.78/1.00  --resolution_flag                       true
% 2.78/1.00  --res_lit_sel                           adaptive
% 2.78/1.00  --res_lit_sel_side                      none
% 2.78/1.00  --res_ordering                          kbo
% 2.78/1.00  --res_to_prop_solver                    active
% 2.78/1.00  --res_prop_simpl_new                    false
% 2.78/1.00  --res_prop_simpl_given                  true
% 2.78/1.00  --res_passive_queue_type                priority_queues
% 2.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.00  --res_passive_queues_freq               [15;5]
% 2.78/1.00  --res_forward_subs                      full
% 2.78/1.00  --res_backward_subs                     full
% 2.78/1.00  --res_forward_subs_resolution           true
% 2.78/1.00  --res_backward_subs_resolution          true
% 2.78/1.00  --res_orphan_elimination                true
% 2.78/1.00  --res_time_limit                        2.
% 2.78/1.00  --res_out_proof                         true
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Options
% 2.78/1.00  
% 2.78/1.00  --superposition_flag                    true
% 2.78/1.00  --sup_passive_queue_type                priority_queues
% 2.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.00  --demod_completeness_check              fast
% 2.78/1.00  --demod_use_ground                      true
% 2.78/1.00  --sup_to_prop_solver                    passive
% 2.78/1.00  --sup_prop_simpl_new                    true
% 2.78/1.00  --sup_prop_simpl_given                  true
% 2.78/1.00  --sup_fun_splitting                     false
% 2.78/1.00  --sup_smt_interval                      50000
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Simplification Setup
% 2.78/1.00  
% 2.78/1.00  --sup_indices_passive                   []
% 2.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_full_bw                           [BwDemod]
% 2.78/1.00  --sup_immed_triv                        [TrivRules]
% 2.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_immed_bw_main                     []
% 2.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  
% 2.78/1.00  ------ Combination Options
% 2.78/1.00  
% 2.78/1.00  --comb_res_mult                         3
% 2.78/1.00  --comb_sup_mult                         2
% 2.78/1.00  --comb_inst_mult                        10
% 2.78/1.00  
% 2.78/1.00  ------ Debug Options
% 2.78/1.00  
% 2.78/1.00  --dbg_backtrace                         false
% 2.78/1.00  --dbg_dump_prop_clauses                 false
% 2.78/1.00  --dbg_dump_prop_clauses_file            -
% 2.78/1.00  --dbg_out_stat                          false
% 2.78/1.00  ------ Parsing...
% 2.78/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.78/1.00  ------ Proving...
% 2.78/1.00  ------ Problem Properties 
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  clauses                                 28
% 2.78/1.00  conjectures                             4
% 2.78/1.00  EPR                                     4
% 2.78/1.00  Horn                                    28
% 2.78/1.00  unary                                   7
% 2.78/1.00  binary                                  12
% 2.78/1.00  lits                                    58
% 2.78/1.00  lits eq                                 17
% 2.78/1.00  fd_pure                                 0
% 2.78/1.00  fd_pseudo                               0
% 2.78/1.00  fd_cond                                 0
% 2.78/1.00  fd_pseudo_cond                          1
% 2.78/1.00  AC symbols                              0
% 2.78/1.00  
% 2.78/1.00  ------ Schedule dynamic 5 is on 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ 
% 2.78/1.00  Current options:
% 2.78/1.00  ------ 
% 2.78/1.00  
% 2.78/1.00  ------ Input Options
% 2.78/1.00  
% 2.78/1.00  --out_options                           all
% 2.78/1.00  --tptp_safe_out                         true
% 2.78/1.00  --problem_path                          ""
% 2.78/1.00  --include_path                          ""
% 2.78/1.00  --clausifier                            res/vclausify_rel
% 2.78/1.00  --clausifier_options                    --mode clausify
% 2.78/1.00  --stdin                                 false
% 2.78/1.00  --stats_out                             all
% 2.78/1.00  
% 2.78/1.00  ------ General Options
% 2.78/1.00  
% 2.78/1.00  --fof                                   false
% 2.78/1.00  --time_out_real                         305.
% 2.78/1.00  --time_out_virtual                      -1.
% 2.78/1.00  --symbol_type_check                     false
% 2.78/1.00  --clausify_out                          false
% 2.78/1.00  --sig_cnt_out                           false
% 2.78/1.00  --trig_cnt_out                          false
% 2.78/1.00  --trig_cnt_out_tolerance                1.
% 2.78/1.00  --trig_cnt_out_sk_spl                   false
% 2.78/1.00  --abstr_cl_out                          false
% 2.78/1.00  
% 2.78/1.00  ------ Global Options
% 2.78/1.00  
% 2.78/1.00  --schedule                              default
% 2.78/1.00  --add_important_lit                     false
% 2.78/1.00  --prop_solver_per_cl                    1000
% 2.78/1.00  --min_unsat_core                        false
% 2.78/1.00  --soft_assumptions                      false
% 2.78/1.00  --soft_lemma_size                       3
% 2.78/1.00  --prop_impl_unit_size                   0
% 2.78/1.00  --prop_impl_unit                        []
% 2.78/1.00  --share_sel_clauses                     true
% 2.78/1.00  --reset_solvers                         false
% 2.78/1.00  --bc_imp_inh                            [conj_cone]
% 2.78/1.00  --conj_cone_tolerance                   3.
% 2.78/1.00  --extra_neg_conj                        none
% 2.78/1.00  --large_theory_mode                     true
% 2.78/1.00  --prolific_symb_bound                   200
% 2.78/1.00  --lt_threshold                          2000
% 2.78/1.00  --clause_weak_htbl                      true
% 2.78/1.00  --gc_record_bc_elim                     false
% 2.78/1.00  
% 2.78/1.00  ------ Preprocessing Options
% 2.78/1.00  
% 2.78/1.00  --preprocessing_flag                    true
% 2.78/1.00  --time_out_prep_mult                    0.1
% 2.78/1.00  --splitting_mode                        input
% 2.78/1.00  --splitting_grd                         true
% 2.78/1.00  --splitting_cvd                         false
% 2.78/1.00  --splitting_cvd_svl                     false
% 2.78/1.00  --splitting_nvd                         32
% 2.78/1.00  --sub_typing                            true
% 2.78/1.00  --prep_gs_sim                           true
% 2.78/1.00  --prep_unflatten                        true
% 2.78/1.00  --prep_res_sim                          true
% 2.78/1.00  --prep_upred                            true
% 2.78/1.00  --prep_sem_filter                       exhaustive
% 2.78/1.00  --prep_sem_filter_out                   false
% 2.78/1.00  --pred_elim                             true
% 2.78/1.00  --res_sim_input                         true
% 2.78/1.00  --eq_ax_congr_red                       true
% 2.78/1.00  --pure_diseq_elim                       true
% 2.78/1.00  --brand_transform                       false
% 2.78/1.00  --non_eq_to_eq                          false
% 2.78/1.00  --prep_def_merge                        true
% 2.78/1.00  --prep_def_merge_prop_impl              false
% 2.78/1.00  --prep_def_merge_mbd                    true
% 2.78/1.00  --prep_def_merge_tr_red                 false
% 2.78/1.00  --prep_def_merge_tr_cl                  false
% 2.78/1.00  --smt_preprocessing                     true
% 2.78/1.00  --smt_ac_axioms                         fast
% 2.78/1.00  --preprocessed_out                      false
% 2.78/1.00  --preprocessed_stats                    false
% 2.78/1.00  
% 2.78/1.00  ------ Abstraction refinement Options
% 2.78/1.00  
% 2.78/1.00  --abstr_ref                             []
% 2.78/1.00  --abstr_ref_prep                        false
% 2.78/1.00  --abstr_ref_until_sat                   false
% 2.78/1.00  --abstr_ref_sig_restrict                funpre
% 2.78/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.78/1.00  --abstr_ref_under                       []
% 2.78/1.00  
% 2.78/1.00  ------ SAT Options
% 2.78/1.00  
% 2.78/1.00  --sat_mode                              false
% 2.78/1.00  --sat_fm_restart_options                ""
% 2.78/1.00  --sat_gr_def                            false
% 2.78/1.00  --sat_epr_types                         true
% 2.78/1.00  --sat_non_cyclic_types                  false
% 2.78/1.00  --sat_finite_models                     false
% 2.78/1.00  --sat_fm_lemmas                         false
% 2.78/1.00  --sat_fm_prep                           false
% 2.78/1.00  --sat_fm_uc_incr                        true
% 2.78/1.00  --sat_out_model                         small
% 2.78/1.00  --sat_out_clauses                       false
% 2.78/1.00  
% 2.78/1.00  ------ QBF Options
% 2.78/1.00  
% 2.78/1.00  --qbf_mode                              false
% 2.78/1.00  --qbf_elim_univ                         false
% 2.78/1.00  --qbf_dom_inst                          none
% 2.78/1.00  --qbf_dom_pre_inst                      false
% 2.78/1.00  --qbf_sk_in                             false
% 2.78/1.00  --qbf_pred_elim                         true
% 2.78/1.00  --qbf_split                             512
% 2.78/1.00  
% 2.78/1.00  ------ BMC1 Options
% 2.78/1.00  
% 2.78/1.00  --bmc1_incremental                      false
% 2.78/1.00  --bmc1_axioms                           reachable_all
% 2.78/1.00  --bmc1_min_bound                        0
% 2.78/1.00  --bmc1_max_bound                        -1
% 2.78/1.00  --bmc1_max_bound_default                -1
% 2.78/1.00  --bmc1_symbol_reachability              true
% 2.78/1.00  --bmc1_property_lemmas                  false
% 2.78/1.00  --bmc1_k_induction                      false
% 2.78/1.00  --bmc1_non_equiv_states                 false
% 2.78/1.00  --bmc1_deadlock                         false
% 2.78/1.00  --bmc1_ucm                              false
% 2.78/1.00  --bmc1_add_unsat_core                   none
% 2.78/1.00  --bmc1_unsat_core_children              false
% 2.78/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.78/1.00  --bmc1_out_stat                         full
% 2.78/1.00  --bmc1_ground_init                      false
% 2.78/1.00  --bmc1_pre_inst_next_state              false
% 2.78/1.00  --bmc1_pre_inst_state                   false
% 2.78/1.00  --bmc1_pre_inst_reach_state             false
% 2.78/1.00  --bmc1_out_unsat_core                   false
% 2.78/1.00  --bmc1_aig_witness_out                  false
% 2.78/1.00  --bmc1_verbose                          false
% 2.78/1.00  --bmc1_dump_clauses_tptp                false
% 2.78/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.78/1.00  --bmc1_dump_file                        -
% 2.78/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.78/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.78/1.00  --bmc1_ucm_extend_mode                  1
% 2.78/1.00  --bmc1_ucm_init_mode                    2
% 2.78/1.00  --bmc1_ucm_cone_mode                    none
% 2.78/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.78/1.00  --bmc1_ucm_relax_model                  4
% 2.78/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.78/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.78/1.00  --bmc1_ucm_layered_model                none
% 2.78/1.00  --bmc1_ucm_max_lemma_size               10
% 2.78/1.00  
% 2.78/1.00  ------ AIG Options
% 2.78/1.00  
% 2.78/1.00  --aig_mode                              false
% 2.78/1.00  
% 2.78/1.00  ------ Instantiation Options
% 2.78/1.00  
% 2.78/1.00  --instantiation_flag                    true
% 2.78/1.00  --inst_sos_flag                         false
% 2.78/1.00  --inst_sos_phase                        true
% 2.78/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.78/1.00  --inst_lit_sel_side                     none
% 2.78/1.00  --inst_solver_per_active                1400
% 2.78/1.00  --inst_solver_calls_frac                1.
% 2.78/1.00  --inst_passive_queue_type               priority_queues
% 2.78/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.78/1.00  --inst_passive_queues_freq              [25;2]
% 2.78/1.00  --inst_dismatching                      true
% 2.78/1.00  --inst_eager_unprocessed_to_passive     true
% 2.78/1.00  --inst_prop_sim_given                   true
% 2.78/1.00  --inst_prop_sim_new                     false
% 2.78/1.00  --inst_subs_new                         false
% 2.78/1.00  --inst_eq_res_simp                      false
% 2.78/1.00  --inst_subs_given                       false
% 2.78/1.00  --inst_orphan_elimination               true
% 2.78/1.00  --inst_learning_loop_flag               true
% 2.78/1.00  --inst_learning_start                   3000
% 2.78/1.00  --inst_learning_factor                  2
% 2.78/1.00  --inst_start_prop_sim_after_learn       3
% 2.78/1.00  --inst_sel_renew                        solver
% 2.78/1.00  --inst_lit_activity_flag                true
% 2.78/1.00  --inst_restr_to_given                   false
% 2.78/1.00  --inst_activity_threshold               500
% 2.78/1.00  --inst_out_proof                        true
% 2.78/1.00  
% 2.78/1.00  ------ Resolution Options
% 2.78/1.00  
% 2.78/1.00  --resolution_flag                       false
% 2.78/1.00  --res_lit_sel                           adaptive
% 2.78/1.00  --res_lit_sel_side                      none
% 2.78/1.00  --res_ordering                          kbo
% 2.78/1.00  --res_to_prop_solver                    active
% 2.78/1.00  --res_prop_simpl_new                    false
% 2.78/1.00  --res_prop_simpl_given                  true
% 2.78/1.00  --res_passive_queue_type                priority_queues
% 2.78/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.78/1.00  --res_passive_queues_freq               [15;5]
% 2.78/1.00  --res_forward_subs                      full
% 2.78/1.00  --res_backward_subs                     full
% 2.78/1.00  --res_forward_subs_resolution           true
% 2.78/1.00  --res_backward_subs_resolution          true
% 2.78/1.00  --res_orphan_elimination                true
% 2.78/1.00  --res_time_limit                        2.
% 2.78/1.00  --res_out_proof                         true
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Options
% 2.78/1.00  
% 2.78/1.00  --superposition_flag                    true
% 2.78/1.00  --sup_passive_queue_type                priority_queues
% 2.78/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.78/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.78/1.00  --demod_completeness_check              fast
% 2.78/1.00  --demod_use_ground                      true
% 2.78/1.00  --sup_to_prop_solver                    passive
% 2.78/1.00  --sup_prop_simpl_new                    true
% 2.78/1.00  --sup_prop_simpl_given                  true
% 2.78/1.00  --sup_fun_splitting                     false
% 2.78/1.00  --sup_smt_interval                      50000
% 2.78/1.00  
% 2.78/1.00  ------ Superposition Simplification Setup
% 2.78/1.00  
% 2.78/1.00  --sup_indices_passive                   []
% 2.78/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.78/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.78/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_full_bw                           [BwDemod]
% 2.78/1.00  --sup_immed_triv                        [TrivRules]
% 2.78/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.78/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_immed_bw_main                     []
% 2.78/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.78/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.78/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.78/1.00  
% 2.78/1.00  ------ Combination Options
% 2.78/1.00  
% 2.78/1.00  --comb_res_mult                         3
% 2.78/1.00  --comb_sup_mult                         2
% 2.78/1.00  --comb_inst_mult                        10
% 2.78/1.00  
% 2.78/1.00  ------ Debug Options
% 2.78/1.00  
% 2.78/1.00  --dbg_backtrace                         false
% 2.78/1.00  --dbg_dump_prop_clauses                 false
% 2.78/1.00  --dbg_dump_prop_clauses_file            -
% 2.78/1.00  --dbg_out_stat                          false
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  ------ Proving...
% 2.78/1.00  
% 2.78/1.00  
% 2.78/1.00  % SZS status Theorem for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.78/1.00  
% 2.78/1.00  fof(f21,conjecture,(
% 2.78/1.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f22,negated_conjecture,(
% 2.78/1.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 2.78/1.00    inference(negated_conjecture,[],[f21])).
% 2.78/1.00  
% 2.78/1.00  fof(f49,plain,(
% 2.78/1.00    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 2.78/1.00    inference(ennf_transformation,[],[f22])).
% 2.78/1.00  
% 2.78/1.00  fof(f50,plain,(
% 2.78/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 2.78/1.00    inference(flattening,[],[f49])).
% 2.78/1.00  
% 2.78/1.00  fof(f58,plain,(
% 2.78/1.00    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f57,plain,(
% 2.78/1.00    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f56,plain,(
% 2.78/1.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 2.78/1.00    introduced(choice_axiom,[])).
% 2.78/1.00  
% 2.78/1.00  fof(f59,plain,(
% 2.78/1.00    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 2.78/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f50,f58,f57,f56])).
% 2.78/1.00  
% 2.78/1.00  fof(f93,plain,(
% 2.78/1.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 2.78/1.00    inference(cnf_transformation,[],[f59])).
% 2.78/1.00  
% 2.78/1.00  fof(f18,axiom,(
% 2.78/1.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f44,plain,(
% 2.78/1.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.78/1.00    inference(ennf_transformation,[],[f18])).
% 2.78/1.00  
% 2.78/1.00  fof(f85,plain,(
% 2.78/1.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f44])).
% 2.78/1.00  
% 2.78/1.00  fof(f90,plain,(
% 2.78/1.00    l1_struct_0(sK1)),
% 2.78/1.00    inference(cnf_transformation,[],[f59])).
% 2.78/1.00  
% 2.78/1.00  fof(f88,plain,(
% 2.78/1.00    l1_struct_0(sK0)),
% 2.78/1.00    inference(cnf_transformation,[],[f59])).
% 2.78/1.00  
% 2.78/1.00  fof(f15,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f39,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.00    inference(ennf_transformation,[],[f15])).
% 2.78/1.00  
% 2.78/1.00  fof(f80,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f39])).
% 2.78/1.00  
% 2.78/1.00  fof(f94,plain,(
% 2.78/1.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 2.78/1.00    inference(cnf_transformation,[],[f59])).
% 2.78/1.00  
% 2.78/1.00  fof(f2,axiom,(
% 2.78/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f53,plain,(
% 2.78/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 2.78/1.00    inference(nnf_transformation,[],[f2])).
% 2.78/1.00  
% 2.78/1.00  fof(f63,plain,(
% 2.78/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f53])).
% 2.78/1.00  
% 2.78/1.00  fof(f3,axiom,(
% 2.78/1.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f24,plain,(
% 2.78/1.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.78/1.00    inference(ennf_transformation,[],[f3])).
% 2.78/1.00  
% 2.78/1.00  fof(f65,plain,(
% 2.78/1.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f24])).
% 2.78/1.00  
% 2.78/1.00  fof(f64,plain,(
% 2.78/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f53])).
% 2.78/1.00  
% 2.78/1.00  fof(f5,axiom,(
% 2.78/1.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f68,plain,(
% 2.78/1.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f5])).
% 2.78/1.00  
% 2.78/1.00  fof(f12,axiom,(
% 2.78/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0))))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f35,plain,(
% 2.78/1.00    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f12])).
% 2.78/1.00  
% 2.78/1.00  fof(f36,plain,(
% 2.78/1.00    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.78/1.00    inference(flattening,[],[f35])).
% 2.78/1.00  
% 2.78/1.00  fof(f76,plain,(
% 2.78/1.00    ( ! [X0] : (k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f36])).
% 2.78/1.00  
% 2.78/1.00  fof(f95,plain,(
% 2.78/1.00    v2_funct_1(sK2)),
% 2.78/1.00    inference(cnf_transformation,[],[f59])).
% 2.78/1.00  
% 2.78/1.00  fof(f91,plain,(
% 2.78/1.00    v1_funct_1(sK2)),
% 2.78/1.00    inference(cnf_transformation,[],[f59])).
% 2.78/1.00  
% 2.78/1.00  fof(f9,axiom,(
% 2.78/1.00    ! [X0] : (v1_relat_1(X0) => r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f30,plain,(
% 2.78/1.00    ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.78/1.00    inference(ennf_transformation,[],[f9])).
% 2.78/1.00  
% 2.78/1.00  fof(f72,plain,(
% 2.78/1.00    ( ! [X0] : (r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) | ~v1_relat_1(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f30])).
% 2.78/1.00  
% 2.78/1.00  fof(f10,axiom,(
% 2.78/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f31,plain,(
% 2.78/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f10])).
% 2.78/1.00  
% 2.78/1.00  fof(f32,plain,(
% 2.78/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.78/1.00    inference(flattening,[],[f31])).
% 2.78/1.00  
% 2.78/1.00  fof(f73,plain,(
% 2.78/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f32])).
% 2.78/1.00  
% 2.78/1.00  fof(f77,plain,(
% 2.78/1.00    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f36])).
% 2.78/1.00  
% 2.78/1.00  fof(f14,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f38,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.00    inference(ennf_transformation,[],[f14])).
% 2.78/1.00  
% 2.78/1.00  fof(f79,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f38])).
% 2.78/1.00  
% 2.78/1.00  fof(f17,axiom,(
% 2.78/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f42,plain,(
% 2.78/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.78/1.00    inference(ennf_transformation,[],[f17])).
% 2.78/1.00  
% 2.78/1.00  fof(f43,plain,(
% 2.78/1.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.78/1.00    inference(flattening,[],[f42])).
% 2.78/1.00  
% 2.78/1.00  fof(f55,plain,(
% 2.78/1.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.78/1.00    inference(nnf_transformation,[],[f43])).
% 2.78/1.00  
% 2.78/1.00  fof(f83,plain,(
% 2.78/1.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f55])).
% 2.78/1.00  
% 2.78/1.00  fof(f92,plain,(
% 2.78/1.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 2.78/1.00    inference(cnf_transformation,[],[f59])).
% 2.78/1.00  
% 2.78/1.00  fof(f16,axiom,(
% 2.78/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f40,plain,(
% 2.78/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.78/1.00    inference(ennf_transformation,[],[f16])).
% 2.78/1.00  
% 2.78/1.00  fof(f41,plain,(
% 2.78/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.78/1.00    inference(flattening,[],[f40])).
% 2.78/1.00  
% 2.78/1.00  fof(f82,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f41])).
% 2.78/1.00  
% 2.78/1.00  fof(f19,axiom,(
% 2.78/1.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f45,plain,(
% 2.78/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 2.78/1.00    inference(ennf_transformation,[],[f19])).
% 2.78/1.00  
% 2.78/1.00  fof(f46,plain,(
% 2.78/1.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 2.78/1.00    inference(flattening,[],[f45])).
% 2.78/1.00  
% 2.78/1.00  fof(f86,plain,(
% 2.78/1.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f46])).
% 2.78/1.00  
% 2.78/1.00  fof(f89,plain,(
% 2.78/1.00    ~v2_struct_0(sK1)),
% 2.78/1.00    inference(cnf_transformation,[],[f59])).
% 2.78/1.00  
% 2.78/1.00  fof(f13,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f23,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 2.78/1.00    inference(pure_predicate_removal,[],[f13])).
% 2.78/1.00  
% 2.78/1.00  fof(f37,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.78/1.00    inference(ennf_transformation,[],[f23])).
% 2.78/1.00  
% 2.78/1.00  fof(f78,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.78/1.00    inference(cnf_transformation,[],[f37])).
% 2.78/1.00  
% 2.78/1.00  fof(f96,plain,(
% 2.78/1.00    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 2.78/1.00    inference(cnf_transformation,[],[f59])).
% 2.78/1.00  
% 2.78/1.00  fof(f20,axiom,(
% 2.78/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 2.78/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 2.78/1.00  
% 2.78/1.00  fof(f47,plain,(
% 2.78/1.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.78/1.00    inference(ennf_transformation,[],[f20])).
% 2.78/1.00  
% 2.78/1.00  fof(f48,plain,(
% 2.78/1.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.78/1.00    inference(flattening,[],[f47])).
% 2.78/1.00  
% 2.78/1.00  fof(f87,plain,(
% 2.78/1.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 2.78/1.00    inference(cnf_transformation,[],[f48])).
% 2.78/1.00  
% 2.78/1.00  cnf(c_31,negated_conjecture,
% 2.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 2.78/1.00      inference(cnf_transformation,[],[f93]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1781,plain,
% 2.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_25,plain,
% 2.78/1.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f85]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_34,negated_conjecture,
% 2.78/1.00      ( l1_struct_0(sK1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f90]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_466,plain,
% 2.78/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 2.78/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_34]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_467,plain,
% 2.78/1.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.78/1.00      inference(unflattening,[status(thm)],[c_466]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_36,negated_conjecture,
% 2.78/1.00      ( l1_struct_0(sK0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f88]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_471,plain,
% 2.78/1.00      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 2.78/1.00      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_472,plain,
% 2.78/1.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 2.78/1.00      inference(unflattening,[status(thm)],[c_471]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1811,plain,
% 2.78/1.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 2.78/1.00      inference(light_normalisation,[status(thm)],[c_1781,c_467,c_472]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_20,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.78/1.00      inference(cnf_transformation,[],[f80]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1782,plain,
% 2.78/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.78/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2573,plain,
% 2.78/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1811,c_1782]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_30,negated_conjecture,
% 2.78/1.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f94]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1808,plain,
% 2.78/1.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 2.78/1.00      inference(light_normalisation,[status(thm)],[c_30,c_467,c_472]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2878,plain,
% 2.78/1.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 2.78/1.00      inference(demodulation,[status(thm)],[c_2573,c_1808]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_4,plain,
% 2.78/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 2.78/1.00      inference(cnf_transformation,[],[f63]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_1794,plain,
% 2.78/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 2.78/1.00      | r1_tarski(X0,X1) = iProver_top ),
% 2.78/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2234,plain,
% 2.78/1.00      ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) = iProver_top ),
% 2.78/1.00      inference(superposition,[status(thm)],[c_1811,c_1794]) ).
% 2.78/1.00  
% 2.78/1.00  cnf(c_2881,plain,
% 2.78/1.00      ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) = iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_2878,c_2234]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 2.78/1.01      | ~ v1_relat_1(X1)
% 2.78/1.01      | v1_relat_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f65]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_3,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.78/1.01      inference(cnf_transformation,[],[f64]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_270,plain,
% 2.78/1.01      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 2.78/1.01      inference(prop_impl,[status(thm)],[c_3]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_271,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 2.78/1.01      inference(renaming,[status(thm)],[c_270]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_329,plain,
% 2.78/1.01      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 2.78/1.01      inference(bin_hyper_res,[status(thm)],[c_5,c_271]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1779,plain,
% 2.78/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.78/1.01      | v1_relat_1(X1) != iProver_top
% 2.78/1.01      | v1_relat_1(X0) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_329]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4728,plain,
% 2.78/1.01      ( v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) != iProver_top
% 2.78/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_2881,c_1779]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_42,plain,
% 2.78/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2138,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_4]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2353,plain,
% 2.78/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.78/1.01      | r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_2138]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2354,plain,
% 2.78/1.01      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 2.78/1.01      | r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_2353]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2047,plain,
% 2.78/1.01      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 2.78/1.01      | v1_relat_1(X0)
% 2.78/1.01      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_329]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2443,plain,
% 2.78/1.01      ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.78/1.01      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 2.78/1.01      | v1_relat_1(sK2) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_2047]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2445,plain,
% 2.78/1.01      ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.78/1.01      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 2.78/1.01      | v1_relat_1(sK2) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_2443]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_8,plain,
% 2.78/1.01      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 2.78/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2818,plain,
% 2.78/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2819,plain,
% 2.78/1.01      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_2818]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4746,plain,
% 2.78/1.01      ( v1_relat_1(sK2) = iProver_top ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_4728,c_42,c_2354,c_2445,c_2819]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_17,plain,
% 2.78/1.01      ( ~ v2_funct_1(X0)
% 2.78/1.01      | ~ v1_funct_1(X0)
% 2.78/1.01      | ~ v1_relat_1(X0)
% 2.78/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_29,negated_conjecture,
% 2.78/1.01      ( v2_funct_1(sK2) ),
% 2.78/1.01      inference(cnf_transformation,[],[f95]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_553,plain,
% 2.78/1.01      ( ~ v1_funct_1(X0)
% 2.78/1.01      | ~ v1_relat_1(X0)
% 2.78/1.01      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 2.78/1.01      | sK2 != X0 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_554,plain,
% 2.78/1.01      ( ~ v1_funct_1(sK2)
% 2.78/1.01      | ~ v1_relat_1(sK2)
% 2.78/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.78/1.01      inference(unflattening,[status(thm)],[c_553]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_33,negated_conjecture,
% 2.78/1.01      ( v1_funct_1(sK2) ),
% 2.78/1.01      inference(cnf_transformation,[],[f91]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_556,plain,
% 2.78/1.01      ( ~ v1_relat_1(sK2)
% 2.78/1.01      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_554,c_33]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1777,plain,
% 2.78/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 2.78/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_556]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4758,plain,
% 2.78/1.01      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_4746,c_1777]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_12,plain,
% 2.78/1.01      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))
% 2.78/1.01      | ~ v1_relat_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1787,plain,
% 2.78/1.01      ( r1_tarski(X0,k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))) = iProver_top
% 2.78/1.01      | v1_relat_1(X0) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4877,plain,
% 2.78/1.01      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))) = iProver_top
% 2.78/1.01      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_4758,c_1787]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_40,plain,
% 2.78/1.01      ( v1_funct_1(sK2) = iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_14,plain,
% 2.78/1.01      ( ~ v1_funct_1(X0)
% 2.78/1.01      | ~ v1_relat_1(X0)
% 2.78/1.01      | v1_relat_1(k2_funct_1(X0)) ),
% 2.78/1.01      inference(cnf_transformation,[],[f73]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1975,plain,
% 2.78/1.01      ( ~ v1_funct_1(sK2)
% 2.78/1.01      | v1_relat_1(k2_funct_1(sK2))
% 2.78/1.01      | ~ v1_relat_1(sK2) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1976,plain,
% 2.78/1.01      ( v1_funct_1(sK2) != iProver_top
% 2.78/1.01      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 2.78/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_1975]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5832,plain,
% 2.78/1.01      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))) = iProver_top ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_4877,c_40,c_42,c_1976,c_2354,c_2445,c_2819]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_16,plain,
% 2.78/1.01      ( ~ v2_funct_1(X0)
% 2.78/1.01      | ~ v1_funct_1(X0)
% 2.78/1.01      | ~ v1_relat_1(X0)
% 2.78/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f77]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_567,plain,
% 2.78/1.01      ( ~ v1_funct_1(X0)
% 2.78/1.01      | ~ v1_relat_1(X0)
% 2.78/1.01      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 2.78/1.01      | sK2 != X0 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_568,plain,
% 2.78/1.01      ( ~ v1_funct_1(sK2)
% 2.78/1.01      | ~ v1_relat_1(sK2)
% 2.78/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.78/1.01      inference(unflattening,[status(thm)],[c_567]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_570,plain,
% 2.78/1.01      ( ~ v1_relat_1(sK2)
% 2.78/1.01      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_568,c_33]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1776,plain,
% 2.78/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 2.78/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_570]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4759,plain,
% 2.78/1.01      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_4746,c_1776]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5836,plain,
% 2.78/1.01      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) = iProver_top ),
% 2.78/1.01      inference(light_normalisation,[status(thm)],[c_5832,c_4759]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1795,plain,
% 2.78/1.01      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 2.78/1.01      | r1_tarski(X0,X1) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_19,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f79]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1783,plain,
% 2.78/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.78/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2586,plain,
% 2.78/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.78/1.01      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1795,c_1783]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5842,plain,
% 2.78/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_5836,c_2586]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5848,plain,
% 2.78/1.01      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 2.78/1.01      inference(light_normalisation,[status(thm)],[c_5842,c_4758]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2572,plain,
% 2.78/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.78/1.01      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_1795,c_1782]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5843,plain,
% 2.78/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_5836,c_2572]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5845,plain,
% 2.78/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 2.78/1.01      inference(light_normalisation,[status(thm)],[c_5843,c_4759]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_24,plain,
% 2.78/1.01      ( ~ v1_partfun1(X0,X1)
% 2.78/1.01      | ~ v4_relat_1(X0,X1)
% 2.78/1.01      | ~ v1_relat_1(X0)
% 2.78/1.01      | k1_relat_1(X0) = X1 ),
% 2.78/1.01      inference(cnf_transformation,[],[f83]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_32,negated_conjecture,
% 2.78/1.01      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 2.78/1.01      inference(cnf_transformation,[],[f92]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_21,plain,
% 2.78/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.01      | v1_partfun1(X0,X1)
% 2.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | v1_xboole_0(X2)
% 2.78/1.01      | ~ v1_funct_1(X0) ),
% 2.78/1.01      inference(cnf_transformation,[],[f82]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_26,plain,
% 2.78/1.01      ( v2_struct_0(X0)
% 2.78/1.01      | ~ l1_struct_0(X0)
% 2.78/1.01      | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 2.78/1.01      inference(cnf_transformation,[],[f86]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_35,negated_conjecture,
% 2.78/1.01      ( ~ v2_struct_0(sK1) ),
% 2.78/1.01      inference(cnf_transformation,[],[f89]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_453,plain,
% 2.78/1.01      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) | sK1 != X0 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_26,c_35]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_454,plain,
% 2.78/1.01      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.78/1.01      inference(unflattening,[status(thm)],[c_453]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_48,plain,
% 2.78/1.01      ( v2_struct_0(sK1)
% 2.78/1.01      | ~ l1_struct_0(sK1)
% 2.78/1.01      | ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_26]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_456,plain,
% 2.78/1.01      ( ~ v1_xboole_0(k2_struct_0(sK1)) ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_454,c_35,c_34,c_48]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_478,plain,
% 2.78/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.01      | v1_partfun1(X0,X1)
% 2.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | ~ v1_funct_1(X0)
% 2.78/1.01      | k2_struct_0(sK1) != X2 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_21,c_456]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_479,plain,
% 2.78/1.01      ( ~ v1_funct_2(X0,X1,k2_struct_0(sK1))
% 2.78/1.01      | v1_partfun1(X0,X1)
% 2.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.78/1.01      | ~ v1_funct_1(X0) ),
% 2.78/1.01      inference(unflattening,[status(thm)],[c_478]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_512,plain,
% 2.78/1.01      ( v1_partfun1(X0,X1)
% 2.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1))))
% 2.78/1.01      | ~ v1_funct_1(X0)
% 2.78/1.01      | u1_struct_0(sK0) != X1
% 2.78/1.01      | u1_struct_0(sK1) != k2_struct_0(sK1)
% 2.78/1.01      | sK2 != X0 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_32,c_479]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_513,plain,
% 2.78/1.01      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 2.78/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.78/1.01      | ~ v1_funct_1(sK2)
% 2.78/1.01      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.78/1.01      inference(unflattening,[status(thm)],[c_512]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_51,plain,
% 2.78/1.01      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 2.78/1.01      inference(instantiation,[status(thm)],[c_25]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_515,plain,
% 2.78/1.01      ( v1_partfun1(sK2,u1_struct_0(sK0))
% 2.78/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_513,c_34,c_33,c_51]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_533,plain,
% 2.78/1.01      ( ~ v4_relat_1(X0,X1)
% 2.78/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.78/1.01      | ~ v1_relat_1(X0)
% 2.78/1.01      | u1_struct_0(sK0) != X1
% 2.78/1.01      | k1_relat_1(X0) = X1
% 2.78/1.01      | sK2 != X0 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_24,c_515]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_534,plain,
% 2.78/1.01      ( ~ v4_relat_1(sK2,u1_struct_0(sK0))
% 2.78/1.01      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.78/1.01      | ~ v1_relat_1(sK2)
% 2.78/1.01      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.78/1.01      inference(unflattening,[status(thm)],[c_533]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_18,plain,
% 2.78/1.01      ( v4_relat_1(X0,X1)
% 2.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.78/1.01      inference(cnf_transformation,[],[f78]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_544,plain,
% 2.78/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
% 2.78/1.01      | ~ v1_relat_1(sK2)
% 2.78/1.01      | k1_relat_1(sK2) = u1_struct_0(sK0) ),
% 2.78/1.01      inference(forward_subsumption_resolution,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_534,c_18]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1778,plain,
% 2.78/1.01      ( k1_relat_1(sK2) = u1_struct_0(sK0)
% 2.78/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.78/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.78/1.01      inference(predicate_to_equality,[status(thm)],[c_544]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1906,plain,
% 2.78/1.01      ( u1_struct_0(sK0) = k1_relat_1(sK2)
% 2.78/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.78/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.78/1.01      inference(light_normalisation,[status(thm)],[c_1778,c_472]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1907,plain,
% 2.78/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.78/1.01      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 2.78/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_1906,c_472]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1911,plain,
% 2.78/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 2.78/1.01      | v1_relat_1(sK2) != iProver_top ),
% 2.78/1.01      inference(forward_subsumption_resolution,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_1907,c_1811]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_4757,plain,
% 2.78/1.01      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 2.78/1.01      inference(superposition,[status(thm)],[c_4746,c_1911]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_28,negated_conjecture,
% 2.78/1.01      ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
% 2.78/1.01      | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
% 2.78/1.01      inference(cnf_transformation,[],[f96]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_27,plain,
% 2.78/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.78/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | ~ v2_funct_1(X0)
% 2.78/1.01      | ~ v1_funct_1(X0)
% 2.78/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.78/1.01      | k2_relset_1(X1,X2,X0) != X2 ),
% 2.78/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_501,plain,
% 2.78/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.78/1.01      | ~ v2_funct_1(X0)
% 2.78/1.01      | ~ v1_funct_1(X0)
% 2.78/1.01      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 2.78/1.01      | k2_relset_1(X1,X2,X0) != X2
% 2.78/1.01      | u1_struct_0(sK0) != X1
% 2.78/1.01      | u1_struct_0(sK1) != X2
% 2.78/1.01      | sK2 != X0 ),
% 2.78/1.01      inference(resolution_lifted,[status(thm)],[c_27,c_32]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_502,plain,
% 2.78/1.01      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 2.78/1.01      | ~ v2_funct_1(sK2)
% 2.78/1.01      | ~ v1_funct_1(sK2)
% 2.78/1.01      | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.78/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.78/1.01      inference(unflattening,[status(thm)],[c_501]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_504,plain,
% 2.78/1.01      ( k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.78/1.01      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 2.78/1.01      inference(global_propositional_subsumption,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_502,c_33,c_31,c_29]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1896,plain,
% 2.78/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 2.78/1.01      | k2_struct_0(sK1) != k2_struct_0(sK1) ),
% 2.78/1.01      inference(light_normalisation,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_504,c_467,c_472,c_1808]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1897,plain,
% 2.78/1.01      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 2.78/1.01      inference(equality_resolution_simp,[status(thm)],[c_1896]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_1914,plain,
% 2.78/1.01      ( k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.78/1.01      | k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK1) ),
% 2.78/1.01      inference(light_normalisation,
% 2.78/1.01                [status(thm)],
% 2.78/1.01                [c_28,c_467,c_472,c_1897]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_2884,plain,
% 2.78/1.01      ( k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_struct_0(sK0)
% 2.78/1.01      | k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_2878,c_1914]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(c_5319,plain,
% 2.78/1.01      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
% 2.78/1.01      | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 2.78/1.01      inference(demodulation,[status(thm)],[c_4757,c_2884]) ).
% 2.78/1.01  
% 2.78/1.01  cnf(contradiction,plain,
% 2.78/1.01      ( $false ),
% 2.78/1.01      inference(minisat,[status(thm)],[c_5848,c_5845,c_5319]) ).
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.78/1.01  
% 2.78/1.01  ------                               Statistics
% 2.78/1.01  
% 2.78/1.01  ------ General
% 2.78/1.01  
% 2.78/1.01  abstr_ref_over_cycles:                  0
% 2.78/1.01  abstr_ref_under_cycles:                 0
% 2.78/1.01  gc_basic_clause_elim:                   0
% 2.78/1.01  forced_gc_time:                         0
% 2.78/1.01  parsing_time:                           0.012
% 2.78/1.01  unif_index_cands_time:                  0.
% 2.78/1.01  unif_index_add_time:                    0.
% 2.78/1.01  orderings_time:                         0.
% 2.78/1.01  out_proof_time:                         0.013
% 2.78/1.01  total_time:                             0.191
% 2.78/1.01  num_of_symbols:                         57
% 2.78/1.01  num_of_terms:                           4433
% 2.78/1.01  
% 2.78/1.01  ------ Preprocessing
% 2.78/1.01  
% 2.78/1.01  num_of_splits:                          0
% 2.78/1.01  num_of_split_atoms:                     0
% 2.78/1.01  num_of_reused_defs:                     0
% 2.78/1.01  num_eq_ax_congr_red:                    13
% 2.78/1.01  num_of_sem_filtered_clauses:            1
% 2.78/1.01  num_of_subtypes:                        0
% 2.78/1.01  monotx_restored_types:                  0
% 2.78/1.01  sat_num_of_epr_types:                   0
% 2.78/1.01  sat_num_of_non_cyclic_types:            0
% 2.78/1.01  sat_guarded_non_collapsed_types:        0
% 2.78/1.01  num_pure_diseq_elim:                    0
% 2.78/1.01  simp_replaced_by:                       0
% 2.78/1.01  res_preprocessed:                       154
% 2.78/1.01  prep_upred:                             0
% 2.78/1.01  prep_unflattend:                        32
% 2.78/1.01  smt_new_axioms:                         0
% 2.78/1.01  pred_elim_cands:                        5
% 2.78/1.01  pred_elim:                              6
% 2.78/1.01  pred_elim_cl:                           7
% 2.78/1.01  pred_elim_cycles:                       10
% 2.78/1.01  merged_defs:                            8
% 2.78/1.01  merged_defs_ncl:                        0
% 2.78/1.01  bin_hyper_res:                          9
% 2.78/1.01  prep_cycles:                            4
% 2.78/1.01  pred_elim_time:                         0.01
% 2.78/1.01  splitting_time:                         0.
% 2.78/1.01  sem_filter_time:                        0.
% 2.78/1.01  monotx_time:                            0.001
% 2.78/1.01  subtype_inf_time:                       0.
% 2.78/1.01  
% 2.78/1.01  ------ Problem properties
% 2.78/1.01  
% 2.78/1.01  clauses:                                28
% 2.78/1.01  conjectures:                            4
% 2.78/1.01  epr:                                    4
% 2.78/1.01  horn:                                   28
% 2.78/1.01  ground:                                 10
% 2.78/1.01  unary:                                  7
% 2.78/1.01  binary:                                 12
% 2.78/1.01  lits:                                   58
% 2.78/1.01  lits_eq:                                17
% 2.78/1.01  fd_pure:                                0
% 2.78/1.01  fd_pseudo:                              0
% 2.78/1.01  fd_cond:                                0
% 2.78/1.01  fd_pseudo_cond:                         1
% 2.78/1.01  ac_symbols:                             0
% 2.78/1.01  
% 2.78/1.01  ------ Propositional Solver
% 2.78/1.01  
% 2.78/1.01  prop_solver_calls:                      28
% 2.78/1.01  prop_fast_solver_calls:                 965
% 2.78/1.01  smt_solver_calls:                       0
% 2.78/1.01  smt_fast_solver_calls:                  0
% 2.78/1.01  prop_num_of_clauses:                    2102
% 2.78/1.01  prop_preprocess_simplified:             6383
% 2.78/1.01  prop_fo_subsumed:                       15
% 2.78/1.01  prop_solver_time:                       0.
% 2.78/1.01  smt_solver_time:                        0.
% 2.78/1.01  smt_fast_solver_time:                   0.
% 2.78/1.01  prop_fast_solver_time:                  0.
% 2.78/1.01  prop_unsat_core_time:                   0.
% 2.78/1.01  
% 2.78/1.01  ------ QBF
% 2.78/1.01  
% 2.78/1.01  qbf_q_res:                              0
% 2.78/1.01  qbf_num_tautologies:                    0
% 2.78/1.01  qbf_prep_cycles:                        0
% 2.78/1.01  
% 2.78/1.01  ------ BMC1
% 2.78/1.01  
% 2.78/1.01  bmc1_current_bound:                     -1
% 2.78/1.01  bmc1_last_solved_bound:                 -1
% 2.78/1.01  bmc1_unsat_core_size:                   -1
% 2.78/1.01  bmc1_unsat_core_parents_size:           -1
% 2.78/1.01  bmc1_merge_next_fun:                    0
% 2.78/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.78/1.01  
% 2.78/1.01  ------ Instantiation
% 2.78/1.01  
% 2.78/1.01  inst_num_of_clauses:                    591
% 2.78/1.01  inst_num_in_passive:                    32
% 2.78/1.01  inst_num_in_active:                     346
% 2.78/1.01  inst_num_in_unprocessed:                217
% 2.78/1.01  inst_num_of_loops:                      380
% 2.78/1.01  inst_num_of_learning_restarts:          0
% 2.78/1.01  inst_num_moves_active_passive:          31
% 2.78/1.01  inst_lit_activity:                      0
% 2.78/1.01  inst_lit_activity_moves:                0
% 2.78/1.01  inst_num_tautologies:                   0
% 2.78/1.01  inst_num_prop_implied:                  0
% 2.78/1.01  inst_num_existing_simplified:           0
% 2.78/1.01  inst_num_eq_res_simplified:             0
% 2.78/1.01  inst_num_child_elim:                    0
% 2.78/1.01  inst_num_of_dismatching_blockings:      191
% 2.78/1.01  inst_num_of_non_proper_insts:           726
% 2.78/1.01  inst_num_of_duplicates:                 0
% 2.78/1.01  inst_inst_num_from_inst_to_res:         0
% 2.78/1.01  inst_dismatching_checking_time:         0.
% 2.78/1.01  
% 2.78/1.01  ------ Resolution
% 2.78/1.01  
% 2.78/1.01  res_num_of_clauses:                     0
% 2.78/1.01  res_num_in_passive:                     0
% 2.78/1.01  res_num_in_active:                      0
% 2.78/1.01  res_num_of_loops:                       158
% 2.78/1.01  res_forward_subset_subsumed:            66
% 2.78/1.01  res_backward_subset_subsumed:           12
% 2.78/1.01  res_forward_subsumed:                   0
% 2.78/1.01  res_backward_subsumed:                  0
% 2.78/1.01  res_forward_subsumption_resolution:     1
% 2.78/1.01  res_backward_subsumption_resolution:    0
% 2.78/1.01  res_clause_to_clause_subsumption:       238
% 2.78/1.01  res_orphan_elimination:                 0
% 2.78/1.01  res_tautology_del:                      78
% 2.78/1.01  res_num_eq_res_simplified:              0
% 2.78/1.01  res_num_sel_changes:                    0
% 2.78/1.01  res_moves_from_active_to_pass:          0
% 2.78/1.01  
% 2.78/1.01  ------ Superposition
% 2.78/1.01  
% 2.78/1.01  sup_time_total:                         0.
% 2.78/1.01  sup_time_generating:                    0.
% 2.78/1.01  sup_time_sim_full:                      0.
% 2.78/1.01  sup_time_sim_immed:                     0.
% 2.78/1.01  
% 2.78/1.01  sup_num_of_clauses:                     89
% 2.78/1.01  sup_num_in_active:                      55
% 2.78/1.01  sup_num_in_passive:                     34
% 2.78/1.01  sup_num_of_loops:                       75
% 2.78/1.01  sup_fw_superposition:                   44
% 2.78/1.01  sup_bw_superposition:                   45
% 2.78/1.01  sup_immediate_simplified:               9
% 2.78/1.01  sup_given_eliminated:                   0
% 2.78/1.01  comparisons_done:                       0
% 2.78/1.01  comparisons_avoided:                    0
% 2.78/1.01  
% 2.78/1.01  ------ Simplifications
% 2.78/1.01  
% 2.78/1.01  
% 2.78/1.01  sim_fw_subset_subsumed:                 2
% 2.78/1.01  sim_bw_subset_subsumed:                 5
% 2.78/1.01  sim_fw_subsumed:                        1
% 2.78/1.01  sim_bw_subsumed:                        0
% 2.78/1.01  sim_fw_subsumption_res:                 2
% 2.78/1.01  sim_bw_subsumption_res:                 0
% 2.78/1.01  sim_tautology_del:                      5
% 2.78/1.01  sim_eq_tautology_del:                   1
% 2.78/1.01  sim_eq_res_simp:                        1
% 2.78/1.01  sim_fw_demodulated:                     1
% 2.78/1.01  sim_bw_demodulated:                     19
% 2.78/1.01  sim_light_normalised:                   12
% 2.78/1.01  sim_joinable_taut:                      0
% 2.78/1.01  sim_joinable_simp:                      0
% 2.78/1.01  sim_ac_normalised:                      0
% 2.78/1.01  sim_smt_subsumption:                    0
% 2.78/1.01  
%------------------------------------------------------------------------------
