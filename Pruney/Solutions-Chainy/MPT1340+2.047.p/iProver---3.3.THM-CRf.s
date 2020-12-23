%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:31 EST 2020

% Result     : Theorem 3.84s
% Output     : CNFRefutation 3.84s
% Verified   : 
% Statistics : Number of formulae       :  304 (9655 expanded)
%              Number of clauses        :  206 (2983 expanded)
%              Number of leaves         :   24 (2627 expanded)
%              Depth                    :   30
%              Number of atoms          : 1177 (60562 expanded)
%              Number of equality atoms :  528 (9938 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f21])).

fof(f56,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f57,plain,(
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
    inference(flattening,[],[f56])).

fof(f64,plain,(
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

fof(f63,plain,(
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

fof(f62,plain,
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

fof(f65,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f57,f64,f63,f62])).

fof(f105,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f72,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f58])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f111,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(k2_relat_1(X1),X0)
       => ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
          & v1_funct_2(X1,k1_relat_1(X1),X0)
          & v1_funct_1(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
        & v1_funct_2(X1,k1_relat_1(X1),X0)
        & v1_funct_1(X1) )
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f49])).

fof(f98,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0)))
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f109,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f34,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f81,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f107,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f65])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f80,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X1)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f75,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_funct_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f36,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f82,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f99,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f104,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f102,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f41])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f52])).

fof(f100,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f103,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f44])).

fof(f89,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f106,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

fof(f108,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f16,axiom,(
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

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f54])).

fof(f101,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f97,plain,(
    ! [X0,X1] :
      ( v1_funct_2(X1,k1_relat_1(X1),X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f10,axiom,(
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

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f84,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f15,axiom,(
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

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f61,plain,(
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
    inference(nnf_transformation,[],[f46])).

fof(f92,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f114,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f92])).

fof(f110,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_41,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1335,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_5,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1357,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f111])).

cnf(c_1360,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_30,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1341,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1345,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2981,plain,
    ( k2_relset_1(k1_relat_1(X0),X1,X0) = k2_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1341,c_1345])).

cnf(c_5420,plain,
    ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_2981])).

cnf(c_5458,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k2_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_5420])).

cnf(c_6,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_134,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_6263,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k2_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k2_relat_1(k2_funct_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5458,c_134])).

cnf(c_6264,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k2_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6263])).

cnf(c_6272,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(X0))),k2_relat_1(k2_funct_1(k2_funct_1(X0))),k2_funct_1(k2_funct_1(X0))) = k2_relat_1(k2_funct_1(k2_funct_1(X0)))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_6264])).

cnf(c_6419,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(X0))),k2_relat_1(k2_funct_1(k2_funct_1(X0))),k2_funct_1(k2_funct_1(X0))) = k2_relat_1(k2_funct_1(k2_funct_1(X0))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6272,c_134])).

cnf(c_6420,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(X0))),k2_relat_1(k2_funct_1(k2_funct_1(X0))),k2_funct_1(k2_funct_1(X0))) = k2_relat_1(k2_funct_1(k2_funct_1(X0)))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_6419])).

cnf(c_6428,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))),k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))),k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0))))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1357,c_6420])).

cnf(c_7442,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))),k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))),k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6428,c_134])).

cnf(c_7443,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))),k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))),k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0))))
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_7442])).

cnf(c_7452,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))),k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_7443])).

cnf(c_37,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1338,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_14,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1350,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3061,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1338,c_1350])).

cnf(c_39,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1708,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1688,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1908,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1688])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1951,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_3369,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3061,c_41,c_39,c_37,c_1708,c_1908,c_1951])).

cnf(c_15,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1349,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3000,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1338,c_1349])).

cnf(c_1711,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_3239,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3000,c_41,c_39,c_37,c_1711,c_1908,c_1951])).

cnf(c_13,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X0,X1))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X1) != k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1351,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v2_funct_1(X1) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_4149,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK2)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,k2_funct_1(sK2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3239,c_1351])).

cnf(c_48,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_50,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_1682,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1683,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1682])).

cnf(c_1685,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1686,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1685])).

cnf(c_1909,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1908])).

cnf(c_1952,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1951])).

cnf(c_4823,plain,
    ( v1_relat_1(X0) != iProver_top
    | k2_relat_1(X0) != k2_relat_1(sK2)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,k2_funct_1(sK2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4149,c_48,c_50,c_1683,c_1686,c_1909,c_1952])).

cnf(c_4824,plain,
    ( k2_relat_1(X0) != k2_relat_1(sK2)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X0,k2_funct_1(sK2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4823])).

cnf(c_4834,plain,
    ( k1_relat_1(sK2) != k2_relat_1(sK2)
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),k2_funct_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3369,c_4824])).

cnf(c_51,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_7,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(k2_funct_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1693,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1694,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1693])).

cnf(c_4848,plain,
    ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4834,c_48,c_50,c_51,c_1694,c_1909,c_1952])).

cnf(c_4856,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4848,c_1349])).

cnf(c_4860,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(sK2))) = k1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4856,c_3369])).

cnf(c_4929,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(sK2))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4860,c_48,c_50,c_1683,c_1686,c_1909,c_1952])).

cnf(c_12,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(k5_relat_1(X1,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k1_relat_1(X0) != k2_relat_1(X1) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1352,plain,
    ( k1_relat_1(X0) != k2_relat_1(X1)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_4194,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK2)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3369,c_1352])).

cnf(c_5337,plain,
    ( v1_relat_1(X0) != iProver_top
    | k1_relat_1(X0) != k1_relat_1(sK2)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4194,c_48,c_50,c_1683,c_1686,c_1909,c_1952])).

cnf(c_5338,plain,
    ( k1_relat_1(X0) != k1_relat_1(sK2)
    | v2_funct_1(X0) = iProver_top
    | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_5337])).

cnf(c_5349,plain,
    ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4929,c_5338])).

cnf(c_17,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1347,plain,
    ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4854,plain,
    ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4848,c_1347])).

cnf(c_4874,plain,
    ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4854,c_3239])).

cnf(c_5263,plain,
    ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4874,c_48,c_50,c_1683,c_1686,c_1909,c_1952])).

cnf(c_5355,plain,
    ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
    | v2_funct_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5349,c_5263])).

cnf(c_2056,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2057,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2056])).

cnf(c_5902,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5355,c_48,c_50,c_51,c_1683,c_1686,c_1694,c_1909,c_1952,c_2057])).

cnf(c_5910,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5902,c_1349])).

cnf(c_4855,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1(sK2))) = k1_relat_1(k2_funct_1(sK2))
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4848,c_1350])).

cnf(c_4867,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1(sK2))) = k2_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_4855,c_3239])).

cnf(c_4993,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1(sK2))) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4867,c_48,c_50,c_1683,c_1686,c_1909,c_1952])).

cnf(c_5914,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_relat_1(sK2)
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5910,c_4993])).

cnf(c_1818,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_1824,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1818])).

cnf(c_1817,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1826,plain,
    ( v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1817])).

cnf(c_5974,plain,
    ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5914,c_48,c_50,c_1683,c_1686,c_1824,c_1826,c_1909,c_1952])).

cnf(c_5909,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5902,c_1350])).

cnf(c_5921,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5909,c_4929])).

cnf(c_6050,plain,
    ( k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5921,c_48,c_50,c_1683,c_1686,c_1824,c_1826,c_1909,c_1952])).

cnf(c_7460,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k1_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7452,c_5974,c_6050])).

cnf(c_1337,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_33,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_42,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_486,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_42])).

cnf(c_487,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(unflattening,[status(thm)],[c_486])).

cnf(c_44,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_491,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_44])).

cnf(c_492,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(unflattening,[status(thm)],[c_491])).

cnf(c_1380,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1337,c_487,c_492])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_xboole_0(X2)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_34,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_43,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_473,plain,
    ( ~ l1_struct_0(X0)
    | ~ v1_xboole_0(u1_struct_0(X0))
    | sK1 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_43])).

cnf(c_474,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(unflattening,[status(thm)],[c_473])).

cnf(c_57,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(instantiation,[status(thm)],[c_34])).

cnf(c_476,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_474,c_43,c_42,c_57])).

cnf(c_498,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | u1_struct_0(sK1) != X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_476])).

cnf(c_499,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_498])).

cnf(c_24,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_560,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(resolution,[status(thm)],[c_499,c_24])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_576,plain,
    ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_560,c_19])).

cnf(c_1334,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_576])).

cnf(c_1467,plain,
    ( k1_relat_1(X0) = X1
    | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1334,c_487])).

cnf(c_1764,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1380,c_1467])).

cnf(c_40,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1336,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_1374,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1336,c_487,c_492])).

cnf(c_1627,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1374])).

cnf(c_1765,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1764])).

cnf(c_2464,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1764,c_41,c_39,c_1627,c_1765,c_1908,c_1951])).

cnf(c_1875,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1380,c_1345])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1377,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(light_normalisation,[status(thm)],[c_38,c_487,c_492])).

cnf(c_1939,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1875,c_1377])).

cnf(c_1955,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_1939,c_1875])).

cnf(c_2469,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_2464,c_1955])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1342,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(k2_funct_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_3679,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2469,c_1342])).

cnf(c_7240,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3679,c_48,c_50,c_1683,c_1909,c_1952])).

cnf(c_7245,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))),k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))))
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7240,c_6420])).

cnf(c_7256,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7245,c_5974,c_6050])).

cnf(c_7598,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7460,c_48,c_50,c_1686,c_1909,c_1952,c_7256])).

cnf(c_35,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_1339,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_7604,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))))
    | v1_funct_2(k2_funct_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) != iProver_top
    | v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) != iProver_top ),
    inference(superposition,[status(thm)],[c_7598,c_1339])).

cnf(c_1731,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
    | ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2103,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1731])).

cnf(c_2105,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2103])).

cnf(c_2104,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2107,plain,
    ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2104])).

cnf(c_2165,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_2171,plain,
    ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = iProver_top
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2165])).

cnf(c_31,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1736,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
    | ~ r1_tarski(k2_relat_1(sK2),X0)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_2447,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1736])).

cnf(c_2449,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
    | r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2447])).

cnf(c_2498,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))))
    | ~ v2_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_2499,plain,
    ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = iProver_top
    | v2_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2498])).

cnf(c_27,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1787,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_2838,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1787])).

cnf(c_2842,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2838])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1792,plain,
    ( v1_funct_2(k2_funct_1(sK2),X0,X1)
    | ~ v1_funct_2(sK2,X1,X0)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(X1,X0,sK2) != X0 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2846,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1792])).

cnf(c_2847,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2846])).

cnf(c_3242,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3239,c_1341])).

cnf(c_3582,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) = iProver_top
    | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3242,c_48,c_50,c_1683,c_1686,c_1909,c_1952])).

cnf(c_3588,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) = iProver_top
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3582,c_3369])).

cnf(c_3595,plain,
    ( k2_relset_1(k2_relat_1(sK2),X0,k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_3588,c_1345])).

cnf(c_3599,plain,
    ( k2_relset_1(k2_relat_1(sK2),X0,k2_funct_1(sK2)) = k1_relat_1(sK2)
    | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3595,c_3369])).

cnf(c_3617,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1360,c_3599])).

cnf(c_2046,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_4429,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2046])).

cnf(c_4433,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4429])).

cnf(c_2045,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK2)),X0,X1)
    | ~ v1_funct_2(k2_funct_1(sK2),X1,X0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(X1,X0,k2_funct_1(sK2)) != X0 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_4435,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_2045])).

cnf(c_4436,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
    | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4435])).

cnf(c_6429,plain,
    ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(k2_funct_1(k2_funct_1(sK2))),k2_funct_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1335,c_6420])).

cnf(c_6432,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_6429,c_4929,c_4993])).

cnf(c_6623,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6432,c_50,c_1909,c_1952])).

cnf(c_1344,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_6626,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6623,c_1344])).

cnf(c_1343,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v2_funct_1(X2) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6627,plain,
    ( v1_funct_2(k2_funct_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v2_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_6623,c_1343])).

cnf(c_10222,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7604,c_48,c_50,c_51,c_1683,c_1686,c_1694,c_1824,c_1826,c_1909,c_1952,c_2057,c_2105,c_2107,c_2171,c_2449,c_2469,c_2499,c_2842,c_2847,c_3617,c_4433,c_4436,c_6626,c_6627])).

cnf(c_3090,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1338,c_1347])).

cnf(c_1722,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_17])).

cnf(c_3373,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3090,c_41,c_39,c_37,c_1722,c_1908,c_1951])).

cnf(c_18,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
    | k1_relat_1(X0) != k2_relat_1(X1)
    | k2_funct_1(X0) = X1 ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1346,plain,
    ( k5_relat_1(X0,X1) != k6_relat_1(k2_relat_1(X1))
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k2_funct_1(X1) = X0
    | v2_funct_1(X1) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5104,plain,
    ( k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3373,c_1346])).

cnf(c_5113,plain,
    ( k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5104,c_3239,c_3369])).

cnf(c_5114,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2
    | v2_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_5113])).

cnf(c_7691,plain,
    ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5114,c_48,c_50,c_51,c_1683,c_1686,c_1694,c_1909,c_1952])).

cnf(c_10224,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_10222,c_7691])).

cnf(c_25,plain,
    ( r2_funct_2(X0,X1,X2,X2)
    | ~ v1_funct_2(X2,X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_36,negated_conjecture,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_595,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
    | u1_struct_0(sK1) != X2
    | u1_struct_0(sK0) != X1
    | sK2 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_36])).

cnf(c_596,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(unflattening,[status(thm)],[c_595])).

cnf(c_1333,plain,
    ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_596])).

cnf(c_1598,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1333,c_487,c_492])).

cnf(c_1809,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v2_funct_1(sK2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1377,c_1339])).

cnf(c_1893,plain,
    ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1809,c_48,c_51,c_1380,c_1374])).

cnf(c_1932,plain,
    ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1598,c_1893])).

cnf(c_1956,plain,
    ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
    inference(demodulation,[status(thm)],[c_1939,c_1932])).

cnf(c_2768,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
    | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_1956,c_2464])).

cnf(c_10226,plain,
    ( sK2 != sK2
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_10224,c_2768])).

cnf(c_811,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1878,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_811])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10226,c_2449,c_2107,c_2105,c_1952,c_1909,c_1878,c_50,c_48])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n011.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 16:08:42 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.84/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.84/0.99  
% 3.84/0.99  ------  iProver source info
% 3.84/0.99  
% 3.84/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.84/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.84/0.99  git: non_committed_changes: false
% 3.84/0.99  git: last_make_outside_of_git: false
% 3.84/0.99  
% 3.84/0.99  ------ 
% 3.84/0.99  
% 3.84/0.99  ------ Input Options
% 3.84/0.99  
% 3.84/0.99  --out_options                           all
% 3.84/0.99  --tptp_safe_out                         true
% 3.84/0.99  --problem_path                          ""
% 3.84/0.99  --include_path                          ""
% 3.84/0.99  --clausifier                            res/vclausify_rel
% 3.84/0.99  --clausifier_options                    --mode clausify
% 3.84/0.99  --stdin                                 false
% 3.84/0.99  --stats_out                             all
% 3.84/0.99  
% 3.84/0.99  ------ General Options
% 3.84/0.99  
% 3.84/0.99  --fof                                   false
% 3.84/0.99  --time_out_real                         305.
% 3.84/0.99  --time_out_virtual                      -1.
% 3.84/0.99  --symbol_type_check                     false
% 3.84/0.99  --clausify_out                          false
% 3.84/0.99  --sig_cnt_out                           false
% 3.84/0.99  --trig_cnt_out                          false
% 3.84/0.99  --trig_cnt_out_tolerance                1.
% 3.84/0.99  --trig_cnt_out_sk_spl                   false
% 3.84/0.99  --abstr_cl_out                          false
% 3.84/0.99  
% 3.84/0.99  ------ Global Options
% 3.84/0.99  
% 3.84/0.99  --schedule                              default
% 3.84/0.99  --add_important_lit                     false
% 3.84/0.99  --prop_solver_per_cl                    1000
% 3.84/0.99  --min_unsat_core                        false
% 3.84/0.99  --soft_assumptions                      false
% 3.84/0.99  --soft_lemma_size                       3
% 3.84/0.99  --prop_impl_unit_size                   0
% 3.84/0.99  --prop_impl_unit                        []
% 3.84/0.99  --share_sel_clauses                     true
% 3.84/0.99  --reset_solvers                         false
% 3.84/0.99  --bc_imp_inh                            [conj_cone]
% 3.84/0.99  --conj_cone_tolerance                   3.
% 3.84/0.99  --extra_neg_conj                        none
% 3.84/0.99  --large_theory_mode                     true
% 3.84/0.99  --prolific_symb_bound                   200
% 3.84/0.99  --lt_threshold                          2000
% 3.84/0.99  --clause_weak_htbl                      true
% 3.84/0.99  --gc_record_bc_elim                     false
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing Options
% 3.84/0.99  
% 3.84/0.99  --preprocessing_flag                    true
% 3.84/0.99  --time_out_prep_mult                    0.1
% 3.84/0.99  --splitting_mode                        input
% 3.84/0.99  --splitting_grd                         true
% 3.84/0.99  --splitting_cvd                         false
% 3.84/0.99  --splitting_cvd_svl                     false
% 3.84/0.99  --splitting_nvd                         32
% 3.84/0.99  --sub_typing                            true
% 3.84/0.99  --prep_gs_sim                           true
% 3.84/0.99  --prep_unflatten                        true
% 3.84/0.99  --prep_res_sim                          true
% 3.84/0.99  --prep_upred                            true
% 3.84/0.99  --prep_sem_filter                       exhaustive
% 3.84/0.99  --prep_sem_filter_out                   false
% 3.84/0.99  --pred_elim                             true
% 3.84/0.99  --res_sim_input                         true
% 3.84/0.99  --eq_ax_congr_red                       true
% 3.84/0.99  --pure_diseq_elim                       true
% 3.84/0.99  --brand_transform                       false
% 3.84/0.99  --non_eq_to_eq                          false
% 3.84/0.99  --prep_def_merge                        true
% 3.84/0.99  --prep_def_merge_prop_impl              false
% 3.84/0.99  --prep_def_merge_mbd                    true
% 3.84/0.99  --prep_def_merge_tr_red                 false
% 3.84/0.99  --prep_def_merge_tr_cl                  false
% 3.84/0.99  --smt_preprocessing                     true
% 3.84/0.99  --smt_ac_axioms                         fast
% 3.84/0.99  --preprocessed_out                      false
% 3.84/0.99  --preprocessed_stats                    false
% 3.84/0.99  
% 3.84/0.99  ------ Abstraction refinement Options
% 3.84/0.99  
% 3.84/0.99  --abstr_ref                             []
% 3.84/0.99  --abstr_ref_prep                        false
% 3.84/0.99  --abstr_ref_until_sat                   false
% 3.84/0.99  --abstr_ref_sig_restrict                funpre
% 3.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.99  --abstr_ref_under                       []
% 3.84/0.99  
% 3.84/0.99  ------ SAT Options
% 3.84/0.99  
% 3.84/0.99  --sat_mode                              false
% 3.84/0.99  --sat_fm_restart_options                ""
% 3.84/0.99  --sat_gr_def                            false
% 3.84/0.99  --sat_epr_types                         true
% 3.84/0.99  --sat_non_cyclic_types                  false
% 3.84/0.99  --sat_finite_models                     false
% 3.84/0.99  --sat_fm_lemmas                         false
% 3.84/0.99  --sat_fm_prep                           false
% 3.84/0.99  --sat_fm_uc_incr                        true
% 3.84/0.99  --sat_out_model                         small
% 3.84/0.99  --sat_out_clauses                       false
% 3.84/0.99  
% 3.84/0.99  ------ QBF Options
% 3.84/0.99  
% 3.84/0.99  --qbf_mode                              false
% 3.84/0.99  --qbf_elim_univ                         false
% 3.84/0.99  --qbf_dom_inst                          none
% 3.84/0.99  --qbf_dom_pre_inst                      false
% 3.84/0.99  --qbf_sk_in                             false
% 3.84/0.99  --qbf_pred_elim                         true
% 3.84/0.99  --qbf_split                             512
% 3.84/0.99  
% 3.84/0.99  ------ BMC1 Options
% 3.84/0.99  
% 3.84/0.99  --bmc1_incremental                      false
% 3.84/0.99  --bmc1_axioms                           reachable_all
% 3.84/0.99  --bmc1_min_bound                        0
% 3.84/0.99  --bmc1_max_bound                        -1
% 3.84/0.99  --bmc1_max_bound_default                -1
% 3.84/0.99  --bmc1_symbol_reachability              true
% 3.84/0.99  --bmc1_property_lemmas                  false
% 3.84/0.99  --bmc1_k_induction                      false
% 3.84/0.99  --bmc1_non_equiv_states                 false
% 3.84/0.99  --bmc1_deadlock                         false
% 3.84/0.99  --bmc1_ucm                              false
% 3.84/0.99  --bmc1_add_unsat_core                   none
% 3.84/0.99  --bmc1_unsat_core_children              false
% 3.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.99  --bmc1_out_stat                         full
% 3.84/0.99  --bmc1_ground_init                      false
% 3.84/0.99  --bmc1_pre_inst_next_state              false
% 3.84/0.99  --bmc1_pre_inst_state                   false
% 3.84/0.99  --bmc1_pre_inst_reach_state             false
% 3.84/0.99  --bmc1_out_unsat_core                   false
% 3.84/0.99  --bmc1_aig_witness_out                  false
% 3.84/0.99  --bmc1_verbose                          false
% 3.84/0.99  --bmc1_dump_clauses_tptp                false
% 3.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.99  --bmc1_dump_file                        -
% 3.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.99  --bmc1_ucm_extend_mode                  1
% 3.84/0.99  --bmc1_ucm_init_mode                    2
% 3.84/0.99  --bmc1_ucm_cone_mode                    none
% 3.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.99  --bmc1_ucm_relax_model                  4
% 3.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.99  --bmc1_ucm_layered_model                none
% 3.84/0.99  --bmc1_ucm_max_lemma_size               10
% 3.84/0.99  
% 3.84/0.99  ------ AIG Options
% 3.84/0.99  
% 3.84/0.99  --aig_mode                              false
% 3.84/0.99  
% 3.84/0.99  ------ Instantiation Options
% 3.84/0.99  
% 3.84/0.99  --instantiation_flag                    true
% 3.84/0.99  --inst_sos_flag                         false
% 3.84/0.99  --inst_sos_phase                        true
% 3.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel_side                     num_symb
% 3.84/0.99  --inst_solver_per_active                1400
% 3.84/0.99  --inst_solver_calls_frac                1.
% 3.84/0.99  --inst_passive_queue_type               priority_queues
% 3.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.99  --inst_passive_queues_freq              [25;2]
% 3.84/0.99  --inst_dismatching                      true
% 3.84/0.99  --inst_eager_unprocessed_to_passive     true
% 3.84/0.99  --inst_prop_sim_given                   true
% 3.84/0.99  --inst_prop_sim_new                     false
% 3.84/0.99  --inst_subs_new                         false
% 3.84/0.99  --inst_eq_res_simp                      false
% 3.84/0.99  --inst_subs_given                       false
% 3.84/0.99  --inst_orphan_elimination               true
% 3.84/0.99  --inst_learning_loop_flag               true
% 3.84/0.99  --inst_learning_start                   3000
% 3.84/0.99  --inst_learning_factor                  2
% 3.84/0.99  --inst_start_prop_sim_after_learn       3
% 3.84/0.99  --inst_sel_renew                        solver
% 3.84/0.99  --inst_lit_activity_flag                true
% 3.84/0.99  --inst_restr_to_given                   false
% 3.84/0.99  --inst_activity_threshold               500
% 3.84/0.99  --inst_out_proof                        true
% 3.84/0.99  
% 3.84/0.99  ------ Resolution Options
% 3.84/0.99  
% 3.84/0.99  --resolution_flag                       true
% 3.84/0.99  --res_lit_sel                           adaptive
% 3.84/0.99  --res_lit_sel_side                      none
% 3.84/0.99  --res_ordering                          kbo
% 3.84/0.99  --res_to_prop_solver                    active
% 3.84/0.99  --res_prop_simpl_new                    false
% 3.84/0.99  --res_prop_simpl_given                  true
% 3.84/0.99  --res_passive_queue_type                priority_queues
% 3.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.99  --res_passive_queues_freq               [15;5]
% 3.84/0.99  --res_forward_subs                      full
% 3.84/0.99  --res_backward_subs                     full
% 3.84/0.99  --res_forward_subs_resolution           true
% 3.84/0.99  --res_backward_subs_resolution          true
% 3.84/0.99  --res_orphan_elimination                true
% 3.84/0.99  --res_time_limit                        2.
% 3.84/0.99  --res_out_proof                         true
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Options
% 3.84/0.99  
% 3.84/0.99  --superposition_flag                    true
% 3.84/0.99  --sup_passive_queue_type                priority_queues
% 3.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.84/0.99  --demod_completeness_check              fast
% 3.84/0.99  --demod_use_ground                      true
% 3.84/0.99  --sup_to_prop_solver                    passive
% 3.84/0.99  --sup_prop_simpl_new                    true
% 3.84/0.99  --sup_prop_simpl_given                  true
% 3.84/0.99  --sup_fun_splitting                     false
% 3.84/0.99  --sup_smt_interval                      50000
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Simplification Setup
% 3.84/0.99  
% 3.84/0.99  --sup_indices_passive                   []
% 3.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_full_bw                           [BwDemod]
% 3.84/0.99  --sup_immed_triv                        [TrivRules]
% 3.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_immed_bw_main                     []
% 3.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  
% 3.84/0.99  ------ Combination Options
% 3.84/0.99  
% 3.84/0.99  --comb_res_mult                         3
% 3.84/0.99  --comb_sup_mult                         2
% 3.84/0.99  --comb_inst_mult                        10
% 3.84/0.99  
% 3.84/0.99  ------ Debug Options
% 3.84/0.99  
% 3.84/0.99  --dbg_backtrace                         false
% 3.84/0.99  --dbg_dump_prop_clauses                 false
% 3.84/0.99  --dbg_dump_prop_clauses_file            -
% 3.84/0.99  --dbg_out_stat                          false
% 3.84/0.99  ------ Parsing...
% 3.84/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 7 0s  sf_e  pe_s  pe_e 
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.84/0.99  ------ Proving...
% 3.84/0.99  ------ Problem Properties 
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  clauses                                 32
% 3.84/0.99  conjectures                             5
% 3.84/0.99  EPR                                     4
% 3.84/0.99  Horn                                    32
% 3.84/0.99  unary                                   9
% 3.84/0.99  binary                                  1
% 3.84/0.99  lits                                    120
% 3.84/0.99  lits eq                                 21
% 3.84/0.99  fd_pure                                 0
% 3.84/0.99  fd_pseudo                               0
% 3.84/0.99  fd_cond                                 0
% 3.84/0.99  fd_pseudo_cond                          3
% 3.84/0.99  AC symbols                              0
% 3.84/0.99  
% 3.84/0.99  ------ Schedule dynamic 5 is on 
% 3.84/0.99  
% 3.84/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  ------ 
% 3.84/0.99  Current options:
% 3.84/0.99  ------ 
% 3.84/0.99  
% 3.84/0.99  ------ Input Options
% 3.84/0.99  
% 3.84/0.99  --out_options                           all
% 3.84/0.99  --tptp_safe_out                         true
% 3.84/0.99  --problem_path                          ""
% 3.84/0.99  --include_path                          ""
% 3.84/0.99  --clausifier                            res/vclausify_rel
% 3.84/0.99  --clausifier_options                    --mode clausify
% 3.84/0.99  --stdin                                 false
% 3.84/0.99  --stats_out                             all
% 3.84/0.99  
% 3.84/0.99  ------ General Options
% 3.84/0.99  
% 3.84/0.99  --fof                                   false
% 3.84/0.99  --time_out_real                         305.
% 3.84/0.99  --time_out_virtual                      -1.
% 3.84/0.99  --symbol_type_check                     false
% 3.84/0.99  --clausify_out                          false
% 3.84/0.99  --sig_cnt_out                           false
% 3.84/0.99  --trig_cnt_out                          false
% 3.84/0.99  --trig_cnt_out_tolerance                1.
% 3.84/0.99  --trig_cnt_out_sk_spl                   false
% 3.84/0.99  --abstr_cl_out                          false
% 3.84/0.99  
% 3.84/0.99  ------ Global Options
% 3.84/0.99  
% 3.84/0.99  --schedule                              default
% 3.84/0.99  --add_important_lit                     false
% 3.84/0.99  --prop_solver_per_cl                    1000
% 3.84/0.99  --min_unsat_core                        false
% 3.84/0.99  --soft_assumptions                      false
% 3.84/0.99  --soft_lemma_size                       3
% 3.84/0.99  --prop_impl_unit_size                   0
% 3.84/0.99  --prop_impl_unit                        []
% 3.84/0.99  --share_sel_clauses                     true
% 3.84/0.99  --reset_solvers                         false
% 3.84/0.99  --bc_imp_inh                            [conj_cone]
% 3.84/0.99  --conj_cone_tolerance                   3.
% 3.84/0.99  --extra_neg_conj                        none
% 3.84/0.99  --large_theory_mode                     true
% 3.84/0.99  --prolific_symb_bound                   200
% 3.84/0.99  --lt_threshold                          2000
% 3.84/0.99  --clause_weak_htbl                      true
% 3.84/0.99  --gc_record_bc_elim                     false
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing Options
% 3.84/0.99  
% 3.84/0.99  --preprocessing_flag                    true
% 3.84/0.99  --time_out_prep_mult                    0.1
% 3.84/0.99  --splitting_mode                        input
% 3.84/0.99  --splitting_grd                         true
% 3.84/0.99  --splitting_cvd                         false
% 3.84/0.99  --splitting_cvd_svl                     false
% 3.84/0.99  --splitting_nvd                         32
% 3.84/0.99  --sub_typing                            true
% 3.84/0.99  --prep_gs_sim                           true
% 3.84/0.99  --prep_unflatten                        true
% 3.84/0.99  --prep_res_sim                          true
% 3.84/0.99  --prep_upred                            true
% 3.84/0.99  --prep_sem_filter                       exhaustive
% 3.84/0.99  --prep_sem_filter_out                   false
% 3.84/0.99  --pred_elim                             true
% 3.84/0.99  --res_sim_input                         true
% 3.84/0.99  --eq_ax_congr_red                       true
% 3.84/0.99  --pure_diseq_elim                       true
% 3.84/0.99  --brand_transform                       false
% 3.84/0.99  --non_eq_to_eq                          false
% 3.84/0.99  --prep_def_merge                        true
% 3.84/0.99  --prep_def_merge_prop_impl              false
% 3.84/0.99  --prep_def_merge_mbd                    true
% 3.84/0.99  --prep_def_merge_tr_red                 false
% 3.84/0.99  --prep_def_merge_tr_cl                  false
% 3.84/0.99  --smt_preprocessing                     true
% 3.84/0.99  --smt_ac_axioms                         fast
% 3.84/0.99  --preprocessed_out                      false
% 3.84/0.99  --preprocessed_stats                    false
% 3.84/0.99  
% 3.84/0.99  ------ Abstraction refinement Options
% 3.84/0.99  
% 3.84/0.99  --abstr_ref                             []
% 3.84/0.99  --abstr_ref_prep                        false
% 3.84/0.99  --abstr_ref_until_sat                   false
% 3.84/0.99  --abstr_ref_sig_restrict                funpre
% 3.84/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.84/0.99  --abstr_ref_under                       []
% 3.84/0.99  
% 3.84/0.99  ------ SAT Options
% 3.84/0.99  
% 3.84/0.99  --sat_mode                              false
% 3.84/0.99  --sat_fm_restart_options                ""
% 3.84/0.99  --sat_gr_def                            false
% 3.84/0.99  --sat_epr_types                         true
% 3.84/0.99  --sat_non_cyclic_types                  false
% 3.84/0.99  --sat_finite_models                     false
% 3.84/0.99  --sat_fm_lemmas                         false
% 3.84/0.99  --sat_fm_prep                           false
% 3.84/0.99  --sat_fm_uc_incr                        true
% 3.84/0.99  --sat_out_model                         small
% 3.84/0.99  --sat_out_clauses                       false
% 3.84/0.99  
% 3.84/0.99  ------ QBF Options
% 3.84/0.99  
% 3.84/0.99  --qbf_mode                              false
% 3.84/0.99  --qbf_elim_univ                         false
% 3.84/0.99  --qbf_dom_inst                          none
% 3.84/0.99  --qbf_dom_pre_inst                      false
% 3.84/0.99  --qbf_sk_in                             false
% 3.84/0.99  --qbf_pred_elim                         true
% 3.84/0.99  --qbf_split                             512
% 3.84/0.99  
% 3.84/0.99  ------ BMC1 Options
% 3.84/0.99  
% 3.84/0.99  --bmc1_incremental                      false
% 3.84/0.99  --bmc1_axioms                           reachable_all
% 3.84/0.99  --bmc1_min_bound                        0
% 3.84/0.99  --bmc1_max_bound                        -1
% 3.84/0.99  --bmc1_max_bound_default                -1
% 3.84/0.99  --bmc1_symbol_reachability              true
% 3.84/0.99  --bmc1_property_lemmas                  false
% 3.84/0.99  --bmc1_k_induction                      false
% 3.84/0.99  --bmc1_non_equiv_states                 false
% 3.84/0.99  --bmc1_deadlock                         false
% 3.84/0.99  --bmc1_ucm                              false
% 3.84/0.99  --bmc1_add_unsat_core                   none
% 3.84/0.99  --bmc1_unsat_core_children              false
% 3.84/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.84/0.99  --bmc1_out_stat                         full
% 3.84/0.99  --bmc1_ground_init                      false
% 3.84/0.99  --bmc1_pre_inst_next_state              false
% 3.84/0.99  --bmc1_pre_inst_state                   false
% 3.84/0.99  --bmc1_pre_inst_reach_state             false
% 3.84/0.99  --bmc1_out_unsat_core                   false
% 3.84/0.99  --bmc1_aig_witness_out                  false
% 3.84/0.99  --bmc1_verbose                          false
% 3.84/0.99  --bmc1_dump_clauses_tptp                false
% 3.84/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.84/0.99  --bmc1_dump_file                        -
% 3.84/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.84/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.84/0.99  --bmc1_ucm_extend_mode                  1
% 3.84/0.99  --bmc1_ucm_init_mode                    2
% 3.84/0.99  --bmc1_ucm_cone_mode                    none
% 3.84/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.84/0.99  --bmc1_ucm_relax_model                  4
% 3.84/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.84/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.84/0.99  --bmc1_ucm_layered_model                none
% 3.84/0.99  --bmc1_ucm_max_lemma_size               10
% 3.84/0.99  
% 3.84/0.99  ------ AIG Options
% 3.84/0.99  
% 3.84/0.99  --aig_mode                              false
% 3.84/0.99  
% 3.84/0.99  ------ Instantiation Options
% 3.84/0.99  
% 3.84/0.99  --instantiation_flag                    true
% 3.84/0.99  --inst_sos_flag                         false
% 3.84/0.99  --inst_sos_phase                        true
% 3.84/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.84/0.99  --inst_lit_sel_side                     none
% 3.84/0.99  --inst_solver_per_active                1400
% 3.84/0.99  --inst_solver_calls_frac                1.
% 3.84/0.99  --inst_passive_queue_type               priority_queues
% 3.84/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.84/0.99  --inst_passive_queues_freq              [25;2]
% 3.84/0.99  --inst_dismatching                      true
% 3.84/0.99  --inst_eager_unprocessed_to_passive     true
% 3.84/0.99  --inst_prop_sim_given                   true
% 3.84/0.99  --inst_prop_sim_new                     false
% 3.84/0.99  --inst_subs_new                         false
% 3.84/0.99  --inst_eq_res_simp                      false
% 3.84/0.99  --inst_subs_given                       false
% 3.84/0.99  --inst_orphan_elimination               true
% 3.84/0.99  --inst_learning_loop_flag               true
% 3.84/0.99  --inst_learning_start                   3000
% 3.84/0.99  --inst_learning_factor                  2
% 3.84/0.99  --inst_start_prop_sim_after_learn       3
% 3.84/0.99  --inst_sel_renew                        solver
% 3.84/0.99  --inst_lit_activity_flag                true
% 3.84/0.99  --inst_restr_to_given                   false
% 3.84/0.99  --inst_activity_threshold               500
% 3.84/0.99  --inst_out_proof                        true
% 3.84/0.99  
% 3.84/0.99  ------ Resolution Options
% 3.84/0.99  
% 3.84/0.99  --resolution_flag                       false
% 3.84/0.99  --res_lit_sel                           adaptive
% 3.84/0.99  --res_lit_sel_side                      none
% 3.84/0.99  --res_ordering                          kbo
% 3.84/0.99  --res_to_prop_solver                    active
% 3.84/0.99  --res_prop_simpl_new                    false
% 3.84/0.99  --res_prop_simpl_given                  true
% 3.84/0.99  --res_passive_queue_type                priority_queues
% 3.84/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.84/0.99  --res_passive_queues_freq               [15;5]
% 3.84/0.99  --res_forward_subs                      full
% 3.84/0.99  --res_backward_subs                     full
% 3.84/0.99  --res_forward_subs_resolution           true
% 3.84/0.99  --res_backward_subs_resolution          true
% 3.84/0.99  --res_orphan_elimination                true
% 3.84/0.99  --res_time_limit                        2.
% 3.84/0.99  --res_out_proof                         true
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Options
% 3.84/0.99  
% 3.84/0.99  --superposition_flag                    true
% 3.84/0.99  --sup_passive_queue_type                priority_queues
% 3.84/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.84/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.84/0.99  --demod_completeness_check              fast
% 3.84/0.99  --demod_use_ground                      true
% 3.84/0.99  --sup_to_prop_solver                    passive
% 3.84/0.99  --sup_prop_simpl_new                    true
% 3.84/0.99  --sup_prop_simpl_given                  true
% 3.84/0.99  --sup_fun_splitting                     false
% 3.84/0.99  --sup_smt_interval                      50000
% 3.84/0.99  
% 3.84/0.99  ------ Superposition Simplification Setup
% 3.84/0.99  
% 3.84/0.99  --sup_indices_passive                   []
% 3.84/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.84/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.84/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_full_bw                           [BwDemod]
% 3.84/0.99  --sup_immed_triv                        [TrivRules]
% 3.84/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.84/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_immed_bw_main                     []
% 3.84/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.84/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.84/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.84/0.99  
% 3.84/0.99  ------ Combination Options
% 3.84/0.99  
% 3.84/0.99  --comb_res_mult                         3
% 3.84/0.99  --comb_sup_mult                         2
% 3.84/0.99  --comb_inst_mult                        10
% 3.84/0.99  
% 3.84/0.99  ------ Debug Options
% 3.84/0.99  
% 3.84/0.99  --dbg_backtrace                         false
% 3.84/0.99  --dbg_dump_prop_clauses                 false
% 3.84/0.99  --dbg_dump_prop_clauses_file            -
% 3.84/0.99  --dbg_out_stat                          false
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  ------ Proving...
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  % SZS status Theorem for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  fof(f21,conjecture,(
% 3.84/0.99    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f22,negated_conjecture,(
% 3.84/0.99    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 3.84/0.99    inference(negated_conjecture,[],[f21])).
% 3.84/0.99  
% 3.84/0.99  fof(f56,plain,(
% 3.84/0.99    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f22])).
% 3.84/0.99  
% 3.84/0.99  fof(f57,plain,(
% 3.84/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 3.84/0.99    inference(flattening,[],[f56])).
% 3.84/0.99  
% 3.84/0.99  fof(f64,plain,(
% 3.84/0.99    ( ! [X0,X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f63,plain,(
% 3.84/0.99    ( ! [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f62,plain,(
% 3.84/0.99    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 3.84/0.99    introduced(choice_axiom,[])).
% 3.84/0.99  
% 3.84/0.99  fof(f65,plain,(
% 3.84/0.99    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 3.84/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f57,f64,f63,f62])).
% 3.84/0.99  
% 3.84/0.99  fof(f105,plain,(
% 3.84/0.99    v1_funct_1(sK2)),
% 3.84/0.99    inference(cnf_transformation,[],[f65])).
% 3.84/0.99  
% 3.84/0.99  fof(f4,axiom,(
% 3.84/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f25,plain,(
% 3.84/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f4])).
% 3.84/0.99  
% 3.84/0.99  fof(f26,plain,(
% 3.84/0.99    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.84/0.99    inference(flattening,[],[f25])).
% 3.84/0.99  
% 3.84/0.99  fof(f72,plain,(
% 3.84/0.99    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f26])).
% 3.84/0.99  
% 3.84/0.99  fof(f1,axiom,(
% 3.84/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f58,plain,(
% 3.84/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/0.99    inference(nnf_transformation,[],[f1])).
% 3.84/0.99  
% 3.84/0.99  fof(f59,plain,(
% 3.84/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.84/0.99    inference(flattening,[],[f58])).
% 3.84/0.99  
% 3.84/0.99  fof(f67,plain,(
% 3.84/0.99    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.84/0.99    inference(cnf_transformation,[],[f59])).
% 3.84/0.99  
% 3.84/0.99  fof(f111,plain,(
% 3.84/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.84/0.99    inference(equality_resolution,[],[f67])).
% 3.84/0.99  
% 3.84/0.99  fof(f17,axiom,(
% 3.84/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(k2_relat_1(X1),X0) => (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f49,plain,(
% 3.84/0.99    ! [X0,X1] : (((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.84/0.99    inference(ennf_transformation,[],[f17])).
% 3.84/0.99  
% 3.84/0.99  fof(f50,plain,(
% 3.84/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) & v1_funct_2(X1,k1_relat_1(X1),X0) & v1_funct_1(X1)) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.84/0.99    inference(flattening,[],[f49])).
% 3.84/0.99  
% 3.84/0.99  fof(f98,plain,(
% 3.84/0.99    ( ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X1),X0))) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f50])).
% 3.84/0.99  
% 3.84/0.99  fof(f12,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f40,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.84/0.99    inference(ennf_transformation,[],[f12])).
% 3.84/0.99  
% 3.84/0.99  fof(f86,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f40])).
% 3.84/0.99  
% 3.84/0.99  fof(f71,plain,(
% 3.84/0.99    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f26])).
% 3.84/0.99  
% 3.84/0.99  fof(f109,plain,(
% 3.84/0.99    v2_funct_1(sK2)),
% 3.84/0.99    inference(cnf_transformation,[],[f65])).
% 3.84/0.99  
% 3.84/0.99  fof(f8,axiom,(
% 3.84/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f33,plain,(
% 3.84/0.99    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f8])).
% 3.84/0.99  
% 3.84/0.99  fof(f34,plain,(
% 3.84/0.99    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.84/0.99    inference(flattening,[],[f33])).
% 3.84/0.99  
% 3.84/0.99  fof(f81,plain,(
% 3.84/0.99    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f34])).
% 3.84/0.99  
% 3.84/0.99  fof(f107,plain,(
% 3.84/0.99    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 3.84/0.99    inference(cnf_transformation,[],[f65])).
% 3.84/0.99  
% 3.84/0.99  fof(f2,axiom,(
% 3.84/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f24,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f2])).
% 3.84/0.99  
% 3.84/0.99  fof(f69,plain,(
% 3.84/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f24])).
% 3.84/0.99  
% 3.84/0.99  fof(f3,axiom,(
% 3.84/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f70,plain,(
% 3.84/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f3])).
% 3.84/0.99  
% 3.84/0.99  fof(f80,plain,(
% 3.84/0.99    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f34])).
% 3.84/0.99  
% 3.84/0.99  fof(f7,axiom,(
% 3.84/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f31,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f7])).
% 3.84/0.99  
% 3.84/0.99  fof(f32,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.84/0.99    inference(flattening,[],[f31])).
% 3.84/0.99  
% 3.84/0.99  fof(f78,plain,(
% 3.84/0.99    ( ! [X0,X1] : (v2_funct_1(X1) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f32])).
% 3.84/0.99  
% 3.84/0.99  fof(f5,axiom,(
% 3.84/0.99    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f27,plain,(
% 3.84/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f5])).
% 3.84/0.99  
% 3.84/0.99  fof(f28,plain,(
% 3.84/0.99    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.84/0.99    inference(flattening,[],[f27])).
% 3.84/0.99  
% 3.84/0.99  fof(f75,plain,(
% 3.84/0.99    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f28])).
% 3.84/0.99  
% 3.84/0.99  fof(f79,plain,(
% 3.84/0.99    ( ! [X0,X1] : (v2_funct_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f32])).
% 3.84/0.99  
% 3.84/0.99  fof(f9,axiom,(
% 3.84/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f35,plain,(
% 3.84/0.99    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f9])).
% 3.84/0.99  
% 3.84/0.99  fof(f36,plain,(
% 3.84/0.99    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.84/0.99    inference(flattening,[],[f35])).
% 3.84/0.99  
% 3.84/0.99  fof(f82,plain,(
% 3.84/0.99    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f36])).
% 3.84/0.99  
% 3.84/0.99  fof(f18,axiom,(
% 3.84/0.99    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f51,plain,(
% 3.84/0.99    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 3.84/0.99    inference(ennf_transformation,[],[f18])).
% 3.84/0.99  
% 3.84/0.99  fof(f99,plain,(
% 3.84/0.99    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f51])).
% 3.84/0.99  
% 3.84/0.99  fof(f104,plain,(
% 3.84/0.99    l1_struct_0(sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f65])).
% 3.84/0.99  
% 3.84/0.99  fof(f102,plain,(
% 3.84/0.99    l1_struct_0(sK0)),
% 3.84/0.99    inference(cnf_transformation,[],[f65])).
% 3.84/0.99  
% 3.84/0.99  fof(f13,axiom,(
% 3.84/0.99    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f41,plain,(
% 3.84/0.99    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.84/0.99    inference(ennf_transformation,[],[f13])).
% 3.84/0.99  
% 3.84/0.99  fof(f42,plain,(
% 3.84/0.99    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 3.84/0.99    inference(flattening,[],[f41])).
% 3.84/0.99  
% 3.84/0.99  fof(f88,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f42])).
% 3.84/0.99  
% 3.84/0.99  fof(f19,axiom,(
% 3.84/0.99    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f52,plain,(
% 3.84/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f19])).
% 3.84/0.99  
% 3.84/0.99  fof(f53,plain,(
% 3.84/0.99    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 3.84/0.99    inference(flattening,[],[f52])).
% 3.84/0.99  
% 3.84/0.99  fof(f100,plain,(
% 3.84/0.99    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f53])).
% 3.84/0.99  
% 3.84/0.99  fof(f103,plain,(
% 3.84/0.99    ~v2_struct_0(sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f65])).
% 3.84/0.99  
% 3.84/0.99  fof(f14,axiom,(
% 3.84/0.99    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f43,plain,(
% 3.84/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.84/0.99    inference(ennf_transformation,[],[f14])).
% 3.84/0.99  
% 3.84/0.99  fof(f44,plain,(
% 3.84/0.99    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.84/0.99    inference(flattening,[],[f43])).
% 3.84/0.99  
% 3.84/0.99  fof(f60,plain,(
% 3.84/0.99    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.84/0.99    inference(nnf_transformation,[],[f44])).
% 3.84/0.99  
% 3.84/0.99  fof(f89,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f60])).
% 3.84/0.99  
% 3.84/0.99  fof(f11,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f23,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.84/0.99    inference(pure_predicate_removal,[],[f11])).
% 3.84/0.99  
% 3.84/0.99  fof(f39,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.84/0.99    inference(ennf_transformation,[],[f23])).
% 3.84/0.99  
% 3.84/0.99  fof(f85,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.84/0.99    inference(cnf_transformation,[],[f39])).
% 3.84/0.99  
% 3.84/0.99  fof(f106,plain,(
% 3.84/0.99    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 3.84/0.99    inference(cnf_transformation,[],[f65])).
% 3.84/0.99  
% 3.84/0.99  fof(f108,plain,(
% 3.84/0.99    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 3.84/0.99    inference(cnf_transformation,[],[f65])).
% 3.84/0.99  
% 3.84/0.99  fof(f16,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f47,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.84/0.99    inference(ennf_transformation,[],[f16])).
% 3.84/0.99  
% 3.84/0.99  fof(f48,plain,(
% 3.84/0.99    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.84/0.99    inference(flattening,[],[f47])).
% 3.84/0.99  
% 3.84/0.99  fof(f93,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f48])).
% 3.84/0.99  
% 3.84/0.99  fof(f20,axiom,(
% 3.84/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f54,plain,(
% 3.84/0.99    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.84/0.99    inference(ennf_transformation,[],[f20])).
% 3.84/0.99  
% 3.84/0.99  fof(f55,plain,(
% 3.84/0.99    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.84/0.99    inference(flattening,[],[f54])).
% 3.84/0.99  
% 3.84/0.99  fof(f101,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f55])).
% 3.84/0.99  
% 3.84/0.99  fof(f97,plain,(
% 3.84/0.99    ( ! [X0,X1] : (v1_funct_2(X1,k1_relat_1(X1),X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f50])).
% 3.84/0.99  
% 3.84/0.99  fof(f95,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f48])).
% 3.84/0.99  
% 3.84/0.99  fof(f94,plain,(
% 3.84/0.99    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f48])).
% 3.84/0.99  
% 3.84/0.99  fof(f10,axiom,(
% 3.84/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f37,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.84/0.99    inference(ennf_transformation,[],[f10])).
% 3.84/0.99  
% 3.84/0.99  fof(f38,plain,(
% 3.84/0.99    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.84/0.99    inference(flattening,[],[f37])).
% 3.84/0.99  
% 3.84/0.99  fof(f84,plain,(
% 3.84/0.99    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f38])).
% 3.84/0.99  
% 3.84/0.99  fof(f15,axiom,(
% 3.84/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 3.84/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.84/0.99  
% 3.84/0.99  fof(f45,plain,(
% 3.84/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 3.84/0.99    inference(ennf_transformation,[],[f15])).
% 3.84/0.99  
% 3.84/0.99  fof(f46,plain,(
% 3.84/0.99    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.84/0.99    inference(flattening,[],[f45])).
% 3.84/0.99  
% 3.84/0.99  fof(f61,plain,(
% 3.84/0.99    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 3.84/0.99    inference(nnf_transformation,[],[f46])).
% 3.84/0.99  
% 3.84/0.99  fof(f92,plain,(
% 3.84/0.99    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 3.84/0.99    inference(cnf_transformation,[],[f61])).
% 3.84/0.99  
% 3.84/0.99  fof(f114,plain,(
% 3.84/0.99    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.84/0.99    inference(equality_resolution,[],[f92])).
% 3.84/0.99  
% 3.84/0.99  fof(f110,plain,(
% 3.84/0.99    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 3.84/0.99    inference(cnf_transformation,[],[f65])).
% 3.84/0.99  
% 3.84/0.99  cnf(c_41,negated_conjecture,
% 3.84/0.99      ( v1_funct_1(sK2) ),
% 3.84/0.99      inference(cnf_transformation,[],[f105]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1335,plain,
% 3.84/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5,plain,
% 3.84/0.99      ( ~ v1_funct_1(X0)
% 3.84/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.84/0.99      | ~ v1_relat_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1357,plain,
% 3.84/0.99      ( v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1,plain,
% 3.84/0.99      ( r1_tarski(X0,X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f111]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1360,plain,
% 3.84/0.99      ( r1_tarski(X0,X0) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_30,plain,
% 3.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1)))
% 3.84/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | ~ v1_relat_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f98]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1341,plain,
% 3.84/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),X1))) = iProver_top
% 3.84/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_20,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f86]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1345,plain,
% 3.84/0.99      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.84/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2981,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(X0),X1,X0) = k2_relat_1(X0)
% 3.84/0.99      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1341,c_1345]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5420,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(X0),k2_relat_1(X0),X0) = k2_relat_1(X0)
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1360,c_2981]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5458,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k2_relat_1(k2_funct_1(X0))
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1357,c_5420]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6,plain,
% 3.84/0.99      ( ~ v1_funct_1(X0)
% 3.84/0.99      | ~ v1_relat_1(X0)
% 3.84/0.99      | v1_relat_1(k2_funct_1(X0)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_134,plain,
% 3.84/0.99      ( v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6263,plain,
% 3.84/0.99      ( v1_relat_1(X0) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | k2_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k2_relat_1(k2_funct_1(X0)) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_5458,c_134]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6264,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(k2_funct_1(X0)),k2_relat_1(k2_funct_1(X0)),k2_funct_1(X0)) = k2_relat_1(k2_funct_1(X0))
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_6263]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6272,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(X0))),k2_relat_1(k2_funct_1(k2_funct_1(X0))),k2_funct_1(k2_funct_1(X0))) = k2_relat_1(k2_funct_1(k2_funct_1(X0)))
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1357,c_6264]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6419,plain,
% 3.84/0.99      ( v1_relat_1(X0) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(X0))),k2_relat_1(k2_funct_1(k2_funct_1(X0))),k2_funct_1(k2_funct_1(X0))) = k2_relat_1(k2_funct_1(k2_funct_1(X0))) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_6272,c_134]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6420,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(X0))),k2_relat_1(k2_funct_1(k2_funct_1(X0))),k2_funct_1(k2_funct_1(X0))) = k2_relat_1(k2_funct_1(k2_funct_1(X0)))
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_6419]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6428,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))),k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))),k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0))))
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1357,c_6420]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7442,plain,
% 3.84/0.99      ( v1_relat_1(X0) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))),k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))),k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_6428,c_134]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7443,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))),k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0)))),k2_funct_1(k2_funct_1(k2_funct_1(X0)))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(X0))))
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_7442]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7452,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))),k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))))
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1335,c_7443]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_37,negated_conjecture,
% 3.84/0.99      ( v2_funct_1(sK2) ),
% 3.84/0.99      inference(cnf_transformation,[],[f109]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1338,plain,
% 3.84/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_14,plain,
% 3.84/0.99      ( ~ v2_funct_1(X0)
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | ~ v1_relat_1(X0)
% 3.84/0.99      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f81]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1350,plain,
% 3.84/0.99      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.84/0.99      | v2_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3061,plain,
% 3.84/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1338,c_1350]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_39,negated_conjecture,
% 3.84/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 3.84/0.99      inference(cnf_transformation,[],[f107]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1708,plain,
% 3.84/0.99      ( ~ v2_funct_1(sK2)
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | ~ v1_relat_1(sK2)
% 3.84/0.99      | k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_14]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.84/0.99      | ~ v1_relat_1(X1)
% 3.84/0.99      | v1_relat_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1688,plain,
% 3.84/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | v1_relat_1(X0)
% 3.84/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_3]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1908,plain,
% 3.84/0.99      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.84/0.99      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 3.84/0.99      | v1_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1688]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4,plain,
% 3.84/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1951,plain,
% 3.84/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_4]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3369,plain,
% 3.84/0.99      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_3061,c_41,c_39,c_37,c_1708,c_1908,c_1951]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_15,plain,
% 3.84/0.99      ( ~ v2_funct_1(X0)
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | ~ v1_relat_1(X0)
% 3.84/0.99      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1349,plain,
% 3.84/0.99      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.84/0.99      | v2_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3000,plain,
% 3.84/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1338,c_1349]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1711,plain,
% 3.84/0.99      ( ~ v2_funct_1(sK2)
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | ~ v1_relat_1(sK2)
% 3.84/0.99      | k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_15]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3239,plain,
% 3.84/0.99      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_3000,c_41,c_39,c_37,c_1711,c_1908,c_1951]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_13,plain,
% 3.84/0.99      ( v2_funct_1(X0)
% 3.84/0.99      | ~ v2_funct_1(k5_relat_1(X0,X1))
% 3.84/0.99      | ~ v1_funct_1(X1)
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | ~ v1_relat_1(X1)
% 3.84/0.99      | ~ v1_relat_1(X0)
% 3.84/0.99      | k1_relat_1(X1) != k2_relat_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f78]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1351,plain,
% 3.84/0.99      ( k1_relat_1(X0) != k2_relat_1(X1)
% 3.84/0.99      | v2_funct_1(X1) = iProver_top
% 3.84/0.99      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 3.84/0.99      | v1_funct_1(X1) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X1) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4149,plain,
% 3.84/0.99      ( k2_relat_1(X0) != k2_relat_1(sK2)
% 3.84/0.99      | v2_funct_1(X0) = iProver_top
% 3.84/0.99      | v2_funct_1(k5_relat_1(X0,k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3239,c_1351]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_48,plain,
% 3.84/0.99      ( v1_funct_1(sK2) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_50,plain,
% 3.84/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1682,plain,
% 3.84/0.99      ( v1_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | ~ v1_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1683,plain,
% 3.84/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1682]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1685,plain,
% 3.84/0.99      ( ~ v1_funct_1(sK2)
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2))
% 3.84/0.99      | ~ v1_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1686,plain,
% 3.84/0.99      ( v1_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1685]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1909,plain,
% 3.84/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 3.84/0.99      | v1_relat_1(sK2) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1908]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1952,plain,
% 3.84/0.99      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1951]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4823,plain,
% 3.84/0.99      ( v1_relat_1(X0) != iProver_top
% 3.84/0.99      | k2_relat_1(X0) != k2_relat_1(sK2)
% 3.84/0.99      | v2_funct_1(X0) = iProver_top
% 3.84/0.99      | v2_funct_1(k5_relat_1(X0,k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_4149,c_48,c_50,c_1683,c_1686,c_1909,c_1952]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4824,plain,
% 3.84/0.99      ( k2_relat_1(X0) != k2_relat_1(sK2)
% 3.84/0.99      | v2_funct_1(X0) = iProver_top
% 3.84/0.99      | v2_funct_1(k5_relat_1(X0,k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_4823]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4834,plain,
% 3.84/0.99      ( k1_relat_1(sK2) != k2_relat_1(sK2)
% 3.84/0.99      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3369,c_4824]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_51,plain,
% 3.84/0.99      ( v2_funct_1(sK2) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7,plain,
% 3.84/0.99      ( ~ v2_funct_1(X0)
% 3.84/0.99      | v2_funct_1(k2_funct_1(X0))
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | ~ v1_relat_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1693,plain,
% 3.84/0.99      ( v2_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | ~ v2_funct_1(sK2)
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | ~ v1_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1694,plain,
% 3.84/0.99      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.84/0.99      | v2_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1693]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4848,plain,
% 3.84/0.99      ( v2_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_4834,c_48,c_50,c_51,c_1694,c_1909,c_1952]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4856,plain,
% 3.84/0.99      ( k1_relat_1(k2_funct_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(sK2))
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_4848,c_1349]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4860,plain,
% 3.84/0.99      ( k1_relat_1(k2_funct_1(k2_funct_1(sK2))) = k1_relat_1(sK2)
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_4856,c_3369]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4929,plain,
% 3.84/0.99      ( k1_relat_1(k2_funct_1(k2_funct_1(sK2))) = k1_relat_1(sK2) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_4860,c_48,c_50,c_1683,c_1686,c_1909,c_1952]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_12,plain,
% 3.84/0.99      ( v2_funct_1(X0)
% 3.84/0.99      | ~ v2_funct_1(k5_relat_1(X1,X0))
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | ~ v1_funct_1(X1)
% 3.84/0.99      | ~ v1_relat_1(X0)
% 3.84/0.99      | ~ v1_relat_1(X1)
% 3.84/0.99      | k1_relat_1(X0) != k2_relat_1(X1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f79]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1352,plain,
% 3.84/0.99      ( k1_relat_1(X0) != k2_relat_1(X1)
% 3.84/0.99      | v2_funct_1(X0) = iProver_top
% 3.84/0.99      | v2_funct_1(k5_relat_1(X1,X0)) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_funct_1(X1) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4194,plain,
% 3.84/0.99      ( k1_relat_1(X0) != k1_relat_1(sK2)
% 3.84/0.99      | v2_funct_1(X0) = iProver_top
% 3.84/0.99      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3369,c_1352]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5337,plain,
% 3.84/0.99      ( v1_relat_1(X0) != iProver_top
% 3.84/0.99      | k1_relat_1(X0) != k1_relat_1(sK2)
% 3.84/0.99      | v2_funct_1(X0) = iProver_top
% 3.84/0.99      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_4194,c_48,c_50,c_1683,c_1686,c_1909,c_1952]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5338,plain,
% 3.84/0.99      ( k1_relat_1(X0) != k1_relat_1(sK2)
% 3.84/0.99      | v2_funct_1(X0) = iProver_top
% 3.84/0.99      | v2_funct_1(k5_relat_1(k2_funct_1(sK2),X0)) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(renaming,[status(thm)],[c_5337]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5349,plain,
% 3.84/0.99      ( v2_funct_1(k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2)))) != iProver_top
% 3.84/0.99      | v2_funct_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_4929,c_5338]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_17,plain,
% 3.84/0.99      ( ~ v2_funct_1(X0)
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | ~ v1_relat_1(X0)
% 3.84/0.99      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1347,plain,
% 3.84/0.99      ( k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
% 3.84/0.99      | v2_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4854,plain,
% 3.84/0.99      ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k1_relat_1(k2_funct_1(sK2)))
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_4848,c_1347]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4874,plain,
% 3.84/0.99      ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2))
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_4854,c_3239]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5263,plain,
% 3.84/0.99      ( k5_relat_1(k2_funct_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k6_relat_1(k2_relat_1(sK2)) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_4874,c_48,c_50,c_1683,c_1686,c_1909,c_1952]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5355,plain,
% 3.84/0.99      ( v2_funct_1(k6_relat_1(k2_relat_1(sK2))) != iProver_top
% 3.84/0.99      | v2_funct_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_5349,c_5263]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2056,plain,
% 3.84/0.99      ( v2_funct_1(k2_funct_1(k2_funct_1(sK2)))
% 3.84/0.99      | ~ v2_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | ~ v1_relat_1(k2_funct_1(sK2)) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2057,plain,
% 3.84/0.99      ( v2_funct_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top
% 3.84/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2056]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5902,plain,
% 3.84/0.99      ( v2_funct_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_5355,c_48,c_50,c_51,c_1683,c_1686,c_1694,c_1909,
% 3.84/0.99                 c_1952,c_2057]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5910,plain,
% 3.84/0.99      ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))
% 3.84/0.99      | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_5902,c_1349]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4855,plain,
% 3.84/0.99      ( k2_relat_1(k2_funct_1(k2_funct_1(sK2))) = k1_relat_1(k2_funct_1(sK2))
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_4848,c_1350]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4867,plain,
% 3.84/0.99      ( k2_relat_1(k2_funct_1(k2_funct_1(sK2))) = k2_relat_1(sK2)
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_4855,c_3239]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4993,plain,
% 3.84/0.99      ( k2_relat_1(k2_funct_1(k2_funct_1(sK2))) = k2_relat_1(sK2) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_4867,c_48,c_50,c_1683,c_1686,c_1909,c_1952]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5914,plain,
% 3.84/0.99      ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_relat_1(sK2)
% 3.84/0.99      | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_5910,c_4993]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1818,plain,
% 3.84/0.99      ( v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
% 3.84/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | ~ v1_relat_1(k2_funct_1(sK2)) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1824,plain,
% 3.84/0.99      ( v1_funct_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1818]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1817,plain,
% 3.84/0.99      ( ~ v1_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | v1_relat_1(k2_funct_1(k2_funct_1(sK2)))
% 3.84/0.99      | ~ v1_relat_1(k2_funct_1(sK2)) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_6]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1826,plain,
% 3.84/0.99      ( v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) = iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_1817]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5974,plain,
% 3.84/0.99      ( k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_relat_1(sK2) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_5914,c_48,c_50,c_1683,c_1686,c_1824,c_1826,c_1909,
% 3.84/0.99                 c_1952]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5909,plain,
% 3.84/0.99      ( k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k1_relat_1(k2_funct_1(k2_funct_1(sK2)))
% 3.84/0.99      | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_5902,c_1350]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5921,plain,
% 3.84/0.99      ( k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k1_relat_1(sK2)
% 3.84/0.99      | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_5909,c_4929]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6050,plain,
% 3.84/0.99      ( k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k1_relat_1(sK2) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_5921,c_48,c_50,c_1683,c_1686,c_1824,c_1826,c_1909,
% 3.84/0.99                 c_1952]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7460,plain,
% 3.84/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k1_relat_1(sK2)
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_7452,c_5974,c_6050]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1337,plain,
% 3.84/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_33,plain,
% 3.84/0.99      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f99]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_42,negated_conjecture,
% 3.84/0.99      ( l1_struct_0(sK1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f104]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_486,plain,
% 3.84/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK1 != X0 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_42]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_487,plain,
% 3.84/0.99      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_486]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_44,negated_conjecture,
% 3.84/0.99      ( l1_struct_0(sK0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f102]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_491,plain,
% 3.84/0.99      ( u1_struct_0(X0) = k2_struct_0(X0) | sK0 != X0 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_33,c_44]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_492,plain,
% 3.84/0.99      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_491]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1380,plain,
% 3.84/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_1337,c_487,c_492]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_21,plain,
% 3.84/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.84/0.99      | v1_partfun1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | v1_xboole_0(X2)
% 3.84/0.99      | ~ v1_funct_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f88]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_34,plain,
% 3.84/0.99      ( v2_struct_0(X0)
% 3.84/0.99      | ~ l1_struct_0(X0)
% 3.84/0.99      | ~ v1_xboole_0(u1_struct_0(X0)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f100]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_43,negated_conjecture,
% 3.84/0.99      ( ~ v2_struct_0(sK1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f103]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_473,plain,
% 3.84/0.99      ( ~ l1_struct_0(X0) | ~ v1_xboole_0(u1_struct_0(X0)) | sK1 != X0 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_34,c_43]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_474,plain,
% 3.84/0.99      ( ~ l1_struct_0(sK1) | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_473]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_57,plain,
% 3.84/0.99      ( v2_struct_0(sK1)
% 3.84/0.99      | ~ l1_struct_0(sK1)
% 3.84/0.99      | ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_34]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_476,plain,
% 3.84/0.99      ( ~ v1_xboole_0(u1_struct_0(sK1)) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_474,c_43,c_42,c_57]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_498,plain,
% 3.84/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.84/0.99      | v1_partfun1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | u1_struct_0(sK1) != X2 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_476]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_499,plain,
% 3.84/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.84/0.99      | v1_partfun1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.84/0.99      | ~ v1_funct_1(X0) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_498]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_24,plain,
% 3.84/0.99      ( ~ v1_partfun1(X0,X1)
% 3.84/0.99      | ~ v4_relat_1(X0,X1)
% 3.84/0.99      | ~ v1_relat_1(X0)
% 3.84/0.99      | k1_relat_1(X0) = X1 ),
% 3.84/0.99      inference(cnf_transformation,[],[f89]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_560,plain,
% 3.84/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.84/0.99      | ~ v4_relat_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | ~ v1_relat_1(X0)
% 3.84/0.99      | k1_relat_1(X0) = X1 ),
% 3.84/0.99      inference(resolution,[status(thm)],[c_499,c_24]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_19,plain,
% 3.84/0.99      ( v4_relat_1(X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.84/0.99      inference(cnf_transformation,[],[f85]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_576,plain,
% 3.84/0.99      ( ~ v1_funct_2(X0,X1,u1_struct_0(sK1))
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1))))
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | ~ v1_relat_1(X0)
% 3.84/0.99      | k1_relat_1(X0) = X1 ),
% 3.84/0.99      inference(forward_subsumption_resolution,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_560,c_19]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1334,plain,
% 3.84/0.99      ( k1_relat_1(X0) = X1
% 3.84/0.99      | v1_funct_2(X0,X1,u1_struct_0(sK1)) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,u1_struct_0(sK1)))) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_576]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1467,plain,
% 3.84/0.99      ( k1_relat_1(X0) = X1
% 3.84/0.99      | v1_funct_2(X0,X1,k2_struct_0(sK1)) != iProver_top
% 3.84/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_struct_0(sK1)))) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_1334,c_487]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1764,plain,
% 3.84/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 3.84/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1380,c_1467]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_40,negated_conjecture,
% 3.84/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 3.84/0.99      inference(cnf_transformation,[],[f106]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1336,plain,
% 3.84/0.99      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1374,plain,
% 3.84/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_1336,c_487,c_492]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1627,plain,
% 3.84/0.99      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
% 3.84/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1374]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1765,plain,
% 3.84/0.99      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | ~ v1_relat_1(sK2)
% 3.84/0.99      | k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.84/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_1764]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2464,plain,
% 3.84/0.99      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_1764,c_41,c_39,c_1627,c_1765,c_1908,c_1951]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1875,plain,
% 3.84/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1380,c_1345]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_38,negated_conjecture,
% 3.84/0.99      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.84/0.99      inference(cnf_transformation,[],[f108]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1377,plain,
% 3.84/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_38,c_487,c_492]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1939,plain,
% 3.84/0.99      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_1875,c_1377]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1955,plain,
% 3.84/0.99      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_1939,c_1875]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2469,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_2464,c_1955]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_29,plain,
% 3.84/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | ~ v2_funct_1(X0)
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | v1_funct_1(k2_funct_1(X0))
% 3.84/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.84/0.99      inference(cnf_transformation,[],[f93]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1342,plain,
% 3.84/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.84/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.84/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.84/0.99      | v2_funct_1(X2) != iProver_top
% 3.84/0.99      | v1_funct_1(X2) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(X2)) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3679,plain,
% 3.84/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.84/0.99      | v2_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_2469,c_1342]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7240,plain,
% 3.84/0.99      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_3679,c_48,c_50,c_1683,c_1909,c_1952]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7245,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))),k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_relat_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))))
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_7240,c_6420]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7256,plain,
% 3.84/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k1_relat_1(sK2)
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_7245,c_5974,c_6050]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7598,plain,
% 3.84/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k1_relat_1(sK2) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_7460,c_48,c_50,c_1686,c_1909,c_1952,c_7256]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_35,plain,
% 3.84/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | ~ v2_funct_1(X0)
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 3.84/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.84/0.99      inference(cnf_transformation,[],[f101]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1339,plain,
% 3.84/0.99      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 3.84/0.99      | k2_relset_1(X0,X1,X2) != X1
% 3.84/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.84/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.84/0.99      | v2_funct_1(X2) != iProver_top
% 3.84/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7604,plain,
% 3.84/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))))
% 3.84/0.99      | v1_funct_2(k2_funct_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.84/0.99      | v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_7598,c_1339]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1731,plain,
% 3.84/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),X0)))
% 3.84/0.99      | ~ r1_tarski(k2_relat_1(sK2),X0)
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | ~ v1_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_30]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2103,plain,
% 3.84/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.84/0.99      | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | ~ v1_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1731]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2105,plain,
% 3.84/0.99      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 3.84/0.99      | r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2103]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2104,plain,
% 3.84/0.99      ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2107,plain,
% 3.84/0.99      ( r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2104]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2165,plain,
% 3.84/0.99      ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))))
% 3.84/0.99      | ~ v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
% 3.84/0.99      | ~ v1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_5]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2171,plain,
% 3.84/0.99      ( v1_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2165]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_31,plain,
% 3.84/0.99      ( v1_funct_2(X0,k1_relat_1(X0),X1)
% 3.84/0.99      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | ~ v1_relat_1(X0) ),
% 3.84/0.99      inference(cnf_transformation,[],[f97]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1736,plain,
% 3.84/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),X0)
% 3.84/0.99      | ~ r1_tarski(k2_relat_1(sK2),X0)
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | ~ v1_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_31]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2447,plain,
% 3.84/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.84/0.99      | ~ r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2))
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | ~ v1_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1736]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2449,plain,
% 3.84/0.99      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
% 3.84/0.99      | r1_tarski(k2_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2447]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2498,plain,
% 3.84/0.99      ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))))
% 3.84/0.99      | ~ v2_funct_1(k2_funct_1(k2_funct_1(sK2)))
% 3.84/0.99      | ~ v1_funct_1(k2_funct_1(k2_funct_1(sK2)))
% 3.84/0.99      | ~ v1_relat_1(k2_funct_1(k2_funct_1(sK2))) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_7]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2499,plain,
% 3.84/0.99      ( v2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = iProver_top
% 3.84/0.99      | v2_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2498]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_27,plain,
% 3.84/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 3.84/0.99      | ~ v2_funct_1(X0)
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.84/0.99      inference(cnf_transformation,[],[f95]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1787,plain,
% 3.84/0.99      ( ~ v1_funct_2(sK2,X0,X1)
% 3.84/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.84/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.84/0.99      | ~ v2_funct_1(sK2)
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | k2_relset_1(X0,X1,sK2) != X1 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_27]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2838,plain,
% 3.84/0.99      ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.84/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
% 3.84/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.84/0.99      | ~ v2_funct_1(sK2)
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1787]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2842,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 3.84/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.84/0.99      | v2_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2838]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_28,plain,
% 3.84/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.84/0.99      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | ~ v2_funct_1(X0)
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | k2_relset_1(X1,X2,X0) != X2 ),
% 3.84/0.99      inference(cnf_transformation,[],[f94]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1792,plain,
% 3.84/0.99      ( v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.84/0.99      | ~ v1_funct_2(sK2,X1,X0)
% 3.84/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.84/0.99      | ~ v2_funct_1(sK2)
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | k2_relset_1(X1,X0,sK2) != X0 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2846,plain,
% 3.84/0.99      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
% 3.84/0.99      | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
% 3.84/0.99      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.84/0.99      | ~ v2_funct_1(sK2)
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_1792]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2847,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_relat_1(sK2)
% 3.84/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 3.84/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.84/0.99      | v2_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_2846]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3242,plain,
% 3.84/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) = iProver_top
% 3.84/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3239,c_1341]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3582,plain,
% 3.84/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) = iProver_top
% 3.84/0.99      | r1_tarski(k2_relat_1(k2_funct_1(sK2)),X0) != iProver_top ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_3242,c_48,c_50,c_1683,c_1686,c_1909,c_1952]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3588,plain,
% 3.84/0.99      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),X0))) = iProver_top
% 3.84/0.99      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_3582,c_3369]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3595,plain,
% 3.84/0.99      ( k2_relset_1(k2_relat_1(sK2),X0,k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
% 3.84/0.99      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3588,c_1345]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3599,plain,
% 3.84/0.99      ( k2_relset_1(k2_relat_1(sK2),X0,k2_funct_1(sK2)) = k1_relat_1(sK2)
% 3.84/0.99      | r1_tarski(k1_relat_1(sK2),X0) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_3595,c_3369]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3617,plain,
% 3.84/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1360,c_3599]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2046,plain,
% 3.84/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),X0,X1)
% 3.84/0.99      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.84/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.84/0.99      | ~ v2_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | k2_relset_1(X0,X1,k2_funct_1(sK2)) != X1 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_27]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4429,plain,
% 3.84/0.99      ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
% 3.84/0.99      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
% 3.84/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
% 3.84/0.99      | ~ v2_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_2046]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4433,plain,
% 3.84/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.84/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top
% 3.84/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.84/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_4429]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2045,plain,
% 3.84/0.99      ( v1_funct_2(k2_funct_1(k2_funct_1(sK2)),X0,X1)
% 3.84/0.99      | ~ v1_funct_2(k2_funct_1(sK2),X1,X0)
% 3.84/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 3.84/0.99      | ~ v2_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | k2_relset_1(X1,X0,k2_funct_1(sK2)) != X0 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_28]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4435,plain,
% 3.84/0.99      ( v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2))
% 3.84/0.99      | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
% 3.84/0.99      | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
% 3.84/0.99      | ~ v2_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | ~ v1_funct_1(k2_funct_1(sK2))
% 3.84/0.99      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_2045]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_4436,plain,
% 3.84/0.99      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
% 3.84/0.99      | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top
% 3.84/0.99      | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) != iProver_top
% 3.84/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_4435]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6429,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(k2_funct_1(k2_funct_1(sK2))),k2_funct_1(k2_funct_1(sK2))) = k2_relat_1(k2_funct_1(k2_funct_1(sK2)))
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1335,c_6420]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6432,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k2_relat_1(sK2)
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_6429,c_4929,c_4993]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6623,plain,
% 3.84/0.99      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2))) = k2_relat_1(sK2) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_6432,c_50,c_1909,c_1952]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1344,plain,
% 3.84/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.84/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.84/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 3.84/0.99      | v2_funct_1(X2) != iProver_top
% 3.84/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6626,plain,
% 3.84/0.99      ( v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2))),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 3.84/0.99      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.84/0.99      | v2_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_6623,c_1344]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1343,plain,
% 3.84/0.99      ( k2_relset_1(X0,X1,X2) != X1
% 3.84/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.84/0.99      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 3.84/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.84/0.99      | v2_funct_1(X2) != iProver_top
% 3.84/0.99      | v1_funct_1(X2) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_6627,plain,
% 3.84/0.99      ( v1_funct_2(k2_funct_1(k2_funct_1(k2_funct_1(sK2))),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 3.84/0.99      | v1_funct_2(k2_funct_1(k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_funct_1(k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.84/0.99      | v2_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_6623,c_1343]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10222,plain,
% 3.84/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) = k2_funct_1(k2_funct_1(k2_funct_1(k2_funct_1(sK2)))) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_7604,c_48,c_50,c_51,c_1683,c_1686,c_1694,c_1824,
% 3.84/0.99                 c_1826,c_1909,c_1952,c_2057,c_2105,c_2107,c_2171,c_2449,
% 3.84/0.99                 c_2469,c_2499,c_2842,c_2847,c_3617,c_4433,c_4436,c_6626,
% 3.84/0.99                 c_6627]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3090,plain,
% 3.84/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1338,c_1347]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1722,plain,
% 3.84/0.99      ( ~ v2_funct_1(sK2)
% 3.84/0.99      | ~ v1_funct_1(sK2)
% 3.84/0.99      | ~ v1_relat_1(sK2)
% 3.84/0.99      | k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_17]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_3373,plain,
% 3.84/0.99      ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_3090,c_41,c_39,c_37,c_1722,c_1908,c_1951]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_18,plain,
% 3.84/0.99      ( ~ v2_funct_1(X0)
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | ~ v1_funct_1(X1)
% 3.84/0.99      | ~ v1_relat_1(X0)
% 3.84/0.99      | ~ v1_relat_1(X1)
% 3.84/0.99      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
% 3.84/0.99      | k1_relat_1(X0) != k2_relat_1(X1)
% 3.84/0.99      | k2_funct_1(X0) = X1 ),
% 3.84/0.99      inference(cnf_transformation,[],[f84]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1346,plain,
% 3.84/0.99      ( k5_relat_1(X0,X1) != k6_relat_1(k2_relat_1(X1))
% 3.84/0.99      | k1_relat_1(X1) != k2_relat_1(X0)
% 3.84/0.99      | k2_funct_1(X1) = X0
% 3.84/0.99      | v2_funct_1(X1) != iProver_top
% 3.84/0.99      | v1_funct_1(X1) != iProver_top
% 3.84/0.99      | v1_funct_1(X0) != iProver_top
% 3.84/0.99      | v1_relat_1(X1) != iProver_top
% 3.84/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5104,plain,
% 3.84/0.99      ( k6_relat_1(k2_relat_1(k2_funct_1(sK2))) != k6_relat_1(k1_relat_1(sK2))
% 3.84/0.99      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 3.84/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.84/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_3373,c_1346]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5113,plain,
% 3.84/0.99      ( k6_relat_1(k1_relat_1(sK2)) != k6_relat_1(k1_relat_1(sK2))
% 3.84/0.99      | k2_relat_1(sK2) != k2_relat_1(sK2)
% 3.84/0.99      | k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.84/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_5104,c_3239,c_3369]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_5114,plain,
% 3.84/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2
% 3.84/0.99      | v2_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 3.84/0.99      | v1_relat_1(sK2) != iProver_top ),
% 3.84/0.99      inference(equality_resolution_simp,[status(thm)],[c_5113]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_7691,plain,
% 3.84/0.99      ( k2_funct_1(k2_funct_1(sK2)) = sK2 ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_5114,c_48,c_50,c_51,c_1683,c_1686,c_1694,c_1909,
% 3.84/0.99                 c_1952]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10224,plain,
% 3.84/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = sK2 ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_10222,c_7691]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_25,plain,
% 3.84/0.99      ( r2_funct_2(X0,X1,X2,X2)
% 3.84/0.99      | ~ v1_funct_2(X2,X0,X1)
% 3.84/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.84/0.99      | ~ v1_funct_1(X2) ),
% 3.84/0.99      inference(cnf_transformation,[],[f114]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_36,negated_conjecture,
% 3.84/0.99      ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
% 3.84/0.99      inference(cnf_transformation,[],[f110]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_595,plain,
% 3.84/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.84/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.84/0.99      | ~ v1_funct_1(X0)
% 3.84/0.99      | k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != X0
% 3.84/0.99      | u1_struct_0(sK1) != X2
% 3.84/0.99      | u1_struct_0(sK0) != X1
% 3.84/0.99      | sK2 != X0 ),
% 3.84/0.99      inference(resolution_lifted,[status(thm)],[c_25,c_36]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_596,plain,
% 3.84/0.99      ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1))
% 3.84/0.99      | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 3.84/0.99      | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
% 3.84/0.99      | sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
% 3.84/0.99      inference(unflattening,[status(thm)],[c_595]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1333,plain,
% 3.84/0.99      ( sK2 != k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
% 3.84/0.99      | v1_funct_2(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) != iProver_top ),
% 3.84/0.99      inference(predicate_to_equality,[status(thm)],[c_596]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1598,plain,
% 3.84/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != sK2
% 3.84/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_1333,c_487,c_492]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1809,plain,
% 3.84/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
% 3.84/0.99      | v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.84/0.99      | v2_funct_1(sK2) != iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.84/0.99      inference(superposition,[status(thm)],[c_1377,c_1339]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1893,plain,
% 3.84/0.99      ( k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) ),
% 3.84/0.99      inference(global_propositional_subsumption,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_1809,c_48,c_51,c_1380,c_1374]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1932,plain,
% 3.84/0.99      ( k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 3.84/0.99      | v1_funct_2(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_1598,c_1893]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1956,plain,
% 3.84/0.99      ( k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)) != sK2
% 3.84/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_1939,c_1932]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_2768,plain,
% 3.84/0.99      ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != sK2
% 3.84/0.99      | v1_funct_2(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.84/0.99      | m1_subset_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.84/0.99      | v1_funct_1(k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))) != iProver_top ),
% 3.84/0.99      inference(light_normalisation,[status(thm)],[c_1956,c_2464]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_10226,plain,
% 3.84/0.99      ( sK2 != sK2
% 3.84/0.99      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 3.84/0.99      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 3.84/0.99      | v1_funct_1(sK2) != iProver_top ),
% 3.84/0.99      inference(demodulation,[status(thm)],[c_10224,c_2768]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_811,plain,( X0 = X0 ),theory(equality) ).
% 3.84/0.99  
% 3.84/0.99  cnf(c_1878,plain,
% 3.84/0.99      ( sK2 = sK2 ),
% 3.84/0.99      inference(instantiation,[status(thm)],[c_811]) ).
% 3.84/0.99  
% 3.84/0.99  cnf(contradiction,plain,
% 3.84/0.99      ( $false ),
% 3.84/0.99      inference(minisat,
% 3.84/0.99                [status(thm)],
% 3.84/0.99                [c_10226,c_2449,c_2107,c_2105,c_1952,c_1909,c_1878,c_50,
% 3.84/0.99                 c_48]) ).
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.84/0.99  
% 3.84/0.99  ------                               Statistics
% 3.84/0.99  
% 3.84/0.99  ------ General
% 3.84/0.99  
% 3.84/0.99  abstr_ref_over_cycles:                  0
% 3.84/0.99  abstr_ref_under_cycles:                 0
% 3.84/0.99  gc_basic_clause_elim:                   0
% 3.84/0.99  forced_gc_time:                         0
% 3.84/0.99  parsing_time:                           0.009
% 3.84/0.99  unif_index_cands_time:                  0.
% 3.84/0.99  unif_index_add_time:                    0.
% 3.84/0.99  orderings_time:                         0.
% 3.84/0.99  out_proof_time:                         0.02
% 3.84/0.99  total_time:                             0.353
% 3.84/0.99  num_of_symbols:                         57
% 3.84/0.99  num_of_terms:                           8496
% 3.84/0.99  
% 3.84/0.99  ------ Preprocessing
% 3.84/0.99  
% 3.84/0.99  num_of_splits:                          0
% 3.84/0.99  num_of_split_atoms:                     0
% 3.84/0.99  num_of_reused_defs:                     0
% 3.84/0.99  num_eq_ax_congr_red:                    8
% 3.84/0.99  num_of_sem_filtered_clauses:            1
% 3.84/0.99  num_of_subtypes:                        0
% 3.84/0.99  monotx_restored_types:                  0
% 3.84/0.99  sat_num_of_epr_types:                   0
% 3.84/0.99  sat_num_of_non_cyclic_types:            0
% 3.84/0.99  sat_guarded_non_collapsed_types:        0
% 3.84/0.99  num_pure_diseq_elim:                    0
% 3.84/0.99  simp_replaced_by:                       0
% 3.84/0.99  res_preprocessed:                       173
% 3.84/0.99  prep_upred:                             0
% 3.84/0.99  prep_unflattend:                        15
% 3.84/0.99  smt_new_axioms:                         0
% 3.84/0.99  pred_elim_cands:                        6
% 3.84/0.99  pred_elim:                              6
% 3.84/0.99  pred_elim_cl:                           8
% 3.84/0.99  pred_elim_cycles:                       9
% 3.84/0.99  merged_defs:                            0
% 3.84/0.99  merged_defs_ncl:                        0
% 3.84/0.99  bin_hyper_res:                          0
% 3.84/0.99  prep_cycles:                            4
% 3.84/0.99  pred_elim_time:                         0.004
% 3.84/0.99  splitting_time:                         0.
% 3.84/0.99  sem_filter_time:                        0.
% 3.84/0.99  monotx_time:                            0.001
% 3.84/0.99  subtype_inf_time:                       0.
% 3.84/0.99  
% 3.84/0.99  ------ Problem properties
% 3.84/0.99  
% 3.84/0.99  clauses:                                32
% 3.84/0.99  conjectures:                            5
% 3.84/0.99  epr:                                    4
% 3.84/0.99  horn:                                   32
% 3.84/0.99  ground:                                 8
% 3.84/0.99  unary:                                  9
% 3.84/0.99  binary:                                 1
% 3.84/0.99  lits:                                   120
% 3.84/0.99  lits_eq:                                21
% 3.84/0.99  fd_pure:                                0
% 3.84/0.99  fd_pseudo:                              0
% 3.84/0.99  fd_cond:                                0
% 3.84/0.99  fd_pseudo_cond:                         3
% 3.84/0.99  ac_symbols:                             0
% 3.84/0.99  
% 3.84/0.99  ------ Propositional Solver
% 3.84/0.99  
% 3.84/0.99  prop_solver_calls:                      31
% 3.84/0.99  prop_fast_solver_calls:                 2150
% 3.84/0.99  smt_solver_calls:                       0
% 3.84/0.99  smt_fast_solver_calls:                  0
% 3.84/0.99  prop_num_of_clauses:                    4064
% 3.84/0.99  prop_preprocess_simplified:             8699
% 3.84/0.99  prop_fo_subsumed:                       254
% 3.84/0.99  prop_solver_time:                       0.
% 3.84/0.99  smt_solver_time:                        0.
% 3.84/0.99  smt_fast_solver_time:                   0.
% 3.84/0.99  prop_fast_solver_time:                  0.
% 3.84/0.99  prop_unsat_core_time:                   0.
% 3.84/0.99  
% 3.84/0.99  ------ QBF
% 3.84/0.99  
% 3.84/0.99  qbf_q_res:                              0
% 3.84/0.99  qbf_num_tautologies:                    0
% 3.84/0.99  qbf_prep_cycles:                        0
% 3.84/0.99  
% 3.84/0.99  ------ BMC1
% 3.84/0.99  
% 3.84/0.99  bmc1_current_bound:                     -1
% 3.84/0.99  bmc1_last_solved_bound:                 -1
% 3.84/0.99  bmc1_unsat_core_size:                   -1
% 3.84/0.99  bmc1_unsat_core_parents_size:           -1
% 3.84/0.99  bmc1_merge_next_fun:                    0
% 3.84/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.84/0.99  
% 3.84/0.99  ------ Instantiation
% 3.84/0.99  
% 3.84/0.99  inst_num_of_clauses:                    1238
% 3.84/0.99  inst_num_in_passive:                    269
% 3.84/0.99  inst_num_in_active:                     653
% 3.84/0.99  inst_num_in_unprocessed:                317
% 3.84/0.99  inst_num_of_loops:                      710
% 3.84/0.99  inst_num_of_learning_restarts:          0
% 3.84/0.99  inst_num_moves_active_passive:          52
% 3.84/0.99  inst_lit_activity:                      0
% 3.84/0.99  inst_lit_activity_moves:                1
% 3.84/0.99  inst_num_tautologies:                   0
% 3.84/0.99  inst_num_prop_implied:                  0
% 3.84/0.99  inst_num_existing_simplified:           0
% 3.84/0.99  inst_num_eq_res_simplified:             0
% 3.84/0.99  inst_num_child_elim:                    0
% 3.84/0.99  inst_num_of_dismatching_blockings:      87
% 3.84/0.99  inst_num_of_non_proper_insts:           853
% 3.84/0.99  inst_num_of_duplicates:                 0
% 3.84/0.99  inst_inst_num_from_inst_to_res:         0
% 3.84/0.99  inst_dismatching_checking_time:         0.
% 3.84/0.99  
% 3.84/0.99  ------ Resolution
% 3.84/0.99  
% 3.84/0.99  res_num_of_clauses:                     0
% 3.84/0.99  res_num_in_passive:                     0
% 3.84/0.99  res_num_in_active:                      0
% 3.84/0.99  res_num_of_loops:                       177
% 3.84/0.99  res_forward_subset_subsumed:            79
% 3.84/0.99  res_backward_subset_subsumed:           4
% 3.84/0.99  res_forward_subsumed:                   0
% 3.84/0.99  res_backward_subsumed:                  0
% 3.84/0.99  res_forward_subsumption_resolution:     1
% 3.84/0.99  res_backward_subsumption_resolution:    0
% 3.84/0.99  res_clause_to_clause_subsumption:       755
% 3.84/0.99  res_orphan_elimination:                 0
% 3.84/0.99  res_tautology_del:                      92
% 3.84/0.99  res_num_eq_res_simplified:              0
% 3.84/0.99  res_num_sel_changes:                    0
% 3.84/0.99  res_moves_from_active_to_pass:          0
% 3.84/0.99  
% 3.84/0.99  ------ Superposition
% 3.84/0.99  
% 3.84/0.99  sup_time_total:                         0.
% 3.84/0.99  sup_time_generating:                    0.
% 3.84/0.99  sup_time_sim_full:                      0.
% 3.84/0.99  sup_time_sim_immed:                     0.
% 3.84/0.99  
% 3.84/0.99  sup_num_of_clauses:                     146
% 3.84/0.99  sup_num_in_active:                      111
% 3.84/0.99  sup_num_in_passive:                     35
% 3.84/0.99  sup_num_of_loops:                       141
% 3.84/0.99  sup_fw_superposition:                   130
% 3.84/0.99  sup_bw_superposition:                   87
% 3.84/0.99  sup_immediate_simplified:               82
% 3.84/0.99  sup_given_eliminated:                   0
% 3.84/0.99  comparisons_done:                       0
% 3.84/0.99  comparisons_avoided:                    0
% 3.84/0.99  
% 3.84/0.99  ------ Simplifications
% 3.84/0.99  
% 3.84/0.99  
% 3.84/0.99  sim_fw_subset_subsumed:                 22
% 3.84/0.99  sim_bw_subset_subsumed:                 2
% 3.84/0.99  sim_fw_subsumed:                        7
% 3.84/0.99  sim_bw_subsumed:                        0
% 3.84/0.99  sim_fw_subsumption_res:                 0
% 3.84/0.99  sim_bw_subsumption_res:                 0
% 3.84/0.99  sim_tautology_del:                      1
% 3.84/0.99  sim_eq_tautology_del:                   42
% 3.84/0.99  sim_eq_res_simp:                        3
% 3.84/0.99  sim_fw_demodulated:                     0
% 3.84/0.99  sim_bw_demodulated:                     30
% 3.84/0.99  sim_light_normalised:                   87
% 3.84/0.99  sim_joinable_taut:                      0
% 3.84/0.99  sim_joinable_simp:                      0
% 3.84/0.99  sim_ac_normalised:                      0
% 3.84/0.99  sim_smt_subsumption:                    0
% 3.84/0.99  
%------------------------------------------------------------------------------
