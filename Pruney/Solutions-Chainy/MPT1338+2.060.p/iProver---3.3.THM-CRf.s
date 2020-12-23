%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:17:11 EST 2020

% Result     : Theorem 11.73s
% Output     : CNFRefutation 11.73s
% Verified   : 
% Statistics : Number of formulae       :  301 (246445 expanded)
%              Number of clauses        :  205 (78206 expanded)
%              Number of leaves         :   28 (70408 expanded)
%              Depth                    :   34
%              Number of atoms          :  864 (1684739 expanded)
%              Number of equality atoms :  426 (585604 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal clause size      :   20 (   2 average)
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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

fof(f54,plain,(
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

fof(f55,plain,(
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
    inference(flattening,[],[f54])).

fof(f64,plain,(
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

fof(f63,plain,(
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

fof(f62,plain,
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

fof(f65,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f55,f64,f63,f62])).

fof(f103,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f56])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f57])).

fof(f110,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f67])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f80,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f102,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f21,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f97,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f105,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f65])).

fof(f100,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f65])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f106,plain,(
    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f17,axiom,(
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
    inference(ennf_transformation,[],[f17])).

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

fof(f101,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f104,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f65])).

fof(f22,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f50])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f92,plain,(
    ! [X0,X1] :
      ( k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f76,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f77,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f32,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f31])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

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
    inference(ennf_transformation,[],[f20])).

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

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f107,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f65])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_funct_1(X2),X1,X0)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f66,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f52])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f108,plain,
    ( k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0)
    | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f65])).

fof(f18,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_funct_2(X2,X0,X1)
              & ~ v1_xboole_0(X2)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_funct_2(X2,X0,X1)
            & ~ v1_xboole_0(X2)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f43])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f58])).

fof(f72,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f59])).

fof(f111,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f72])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_1485,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f110])).

cnf(c_1511,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_14,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1505,plain,
    ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7247,plain,
    ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_1505])).

cnf(c_37130,plain,
    ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1485,c_7247])).

cnf(c_40,negated_conjecture,
    ( l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_1484,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_31,plain,
    ( ~ l1_struct_0(X0)
    | u1_struct_0(X0) = k2_struct_0(X0) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_1491,plain,
    ( u1_struct_0(X0) = k2_struct_0(X0)
    | l1_struct_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2295,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(superposition,[status(thm)],[c_1484,c_1491])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1487,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_2302,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2295,c_1487])).

cnf(c_42,negated_conjecture,
    ( l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1482,plain,
    ( l1_struct_0(sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_2296,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(superposition,[status(thm)],[c_1482,c_1491])).

cnf(c_2850,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2302,c_2296])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1499,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3382,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_2850,c_1499])).

cnf(c_36,negated_conjecture,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_2305,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_2295,c_36])).

cnf(c_2503,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    inference(demodulation,[status(thm)],[c_2296,c_2305])).

cnf(c_3658,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3382,c_2503])).

cnf(c_3663,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3658,c_2850])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1498,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | v1_partfun1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_4468,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_xboole_0(k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3663,c_1498])).

cnf(c_41,negated_conjecture,
    ( ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_44,plain,
    ( v2_struct_0(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_45,plain,
    ( l1_struct_0(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_46,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1486,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_2303,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2295,c_1486])).

cnf(c_2771,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_2303,c_2296])).

cnf(c_3664,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3658,c_2771])).

cnf(c_32,plain,
    ( v2_struct_0(X0)
    | ~ l1_struct_0(X0)
    | ~ v1_xboole_0(k2_struct_0(X0)) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1490,plain,
    ( v2_struct_0(X0) = iProver_top
    | l1_struct_0(X0) != iProver_top
    | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3683,plain,
    ( v2_struct_0(sK1) = iProver_top
    | l1_struct_0(sK1) != iProver_top
    | v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3658,c_1490])).

cnf(c_4969,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4468,c_44,c_45,c_46,c_3664,c_3683])).

cnf(c_27,plain,
    ( ~ v1_partfun1(X0,X1)
    | ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k1_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1495,plain,
    ( k1_relat_1(X0) = X1
    | v1_partfun1(X0,X1) != iProver_top
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8679,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | v4_relat_1(sK2,k2_struct_0(sK0)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_4969,c_1495])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1955,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(resolution,[status(thm)],[c_9,c_37])).

cnf(c_660,plain,
    ( X0 != X1
    | k2_struct_0(X0) = k2_struct_0(X1) ),
    theory(equality)).

cnf(c_2056,plain,
    ( k2_struct_0(sK0) = k2_struct_0(X0)
    | sK0 != X0 ),
    inference(instantiation,[status(thm)],[c_660])).

cnf(c_2439,plain,
    ( k2_struct_0(sK0) = k2_struct_0(sK0)
    | sK0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2056])).

cnf(c_643,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2440,plain,
    ( sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_643])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_249,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_250,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_249])).

cnf(c_315,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_250])).

cnf(c_1987,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_315])).

cnf(c_2802,plain,
    ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_1987])).

cnf(c_15,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1504,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_3197,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2850,c_1504])).

cnf(c_3215,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3197])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3365,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_3682,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3664])).

cnf(c_3684,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(k2_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3683])).

cnf(c_4491,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | v1_xboole_0(k2_relat_1(sK2)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4468])).

cnf(c_5288,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_27])).

cnf(c_644,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2054,plain,
    ( X0 != X1
    | k2_struct_0(sK0) != X1
    | k2_struct_0(sK0) = X0 ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_2464,plain,
    ( X0 != k2_struct_0(sK0)
    | k2_struct_0(sK0) = X0
    | k2_struct_0(sK0) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2054])).

cnf(c_7784,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_relat_1(sK2) != k2_struct_0(sK0) ),
    inference(instantiation,[status(thm)],[c_2464])).

cnf(c_9066,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8679,c_41,c_40,c_39,c_1955,c_2439,c_2440,c_2802,c_3215,c_3365,c_3682,c_3684,c_4491,c_5288,c_7784])).

cnf(c_13,plain,
    ( ~ v4_relat_1(X0,X1)
    | ~ v1_relat_1(X0)
    | k7_relat_1(X0,X1) = X0 ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1506,plain,
    ( k7_relat_1(X0,X1) = X0
    | v4_relat_1(X0,X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5378,plain,
    ( k7_relat_1(sK2,k2_struct_0(sK0)) = sK2
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3197,c_1506])).

cnf(c_5290,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | k7_relat_1(sK2,k2_struct_0(sK0)) = sK2 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_5527,plain,
    ( k7_relat_1(sK2,k2_struct_0(sK0)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5378,c_1955,c_2802,c_3215,c_3365,c_5290])).

cnf(c_9071,plain,
    ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
    inference(demodulation,[status(thm)],[c_9066,c_5527])).

cnf(c_1509,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2853,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) = iProver_top ),
    inference(superposition,[status(thm)],[c_2850,c_1509])).

cnf(c_3661,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3658,c_2853])).

cnf(c_9077,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9066,c_3661])).

cnf(c_1480,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_315])).

cnf(c_17276,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_9077,c_1480])).

cnf(c_1956,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1955])).

cnf(c_2804,plain,
    ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2802])).

cnf(c_3366,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3365])).

cnf(c_17387,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17276,c_1956,c_2804,c_3366])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_1507,plain,
    ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_17392,plain,
    ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
    inference(superposition,[status(thm)],[c_17387,c_1507])).

cnf(c_17395,plain,
    ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_9071,c_17392])).

cnf(c_3660,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_3658,c_3382])).

cnf(c_9078,plain,
    ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_9066,c_3660])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1494,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_22885,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9078,c_1494])).

cnf(c_35,negated_conjecture,
    ( v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_49,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_9076,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9066,c_3663])).

cnf(c_9079,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9066,c_3664])).

cnf(c_23163,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22885,c_46,c_49,c_9076,c_9079])).

cnf(c_23175,plain,
    ( v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23163,c_1504])).

cnf(c_23449,plain,
    ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_23175,c_1506])).

cnf(c_47,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_48,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_57,plain,
    ( ~ l1_struct_0(sK1)
    | u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_31])).

cnf(c_1972,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2107,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1972])).

cnf(c_2108,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2107])).

cnf(c_2286,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | u1_struct_0(sK1) != X0 ),
    inference(instantiation,[status(thm)],[c_644])).

cnf(c_2833,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | u1_struct_0(sK1) != k2_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_2286])).

cnf(c_2132,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_3485,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_2132])).

cnf(c_3498,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
    | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3485])).

cnf(c_4829,plain,
    ( ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(instantiation,[status(thm)],[c_1987])).

cnf(c_4833,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4829])).

cnf(c_7076,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_7077,plain,
    ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7076])).

cnf(c_25903,plain,
    ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23449,c_40,c_46,c_47,c_48,c_36,c_49,c_57,c_2108,c_2833,c_3498,c_4833,c_7077])).

cnf(c_23168,plain,
    ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_23163,c_1509])).

cnf(c_23454,plain,
    ( v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23168,c_1480])).

cnf(c_26241,plain,
    ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23454,c_40,c_46,c_47,c_48,c_36,c_49,c_57,c_2108,c_2833,c_3498,c_4833,c_7077])).

cnf(c_26247,plain,
    ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
    inference(superposition,[status(thm)],[c_26241,c_1507])).

cnf(c_29238,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_25903,c_26247])).

cnf(c_37141,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v2_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_37130,c_17395,c_29238])).

cnf(c_38154,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37141,c_49,c_1956,c_2804,c_3366])).

cnf(c_38168,plain,
    ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_38154,c_29238])).

cnf(c_23174,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
    | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) = iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23163,c_1498])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1967,plain,
    ( ~ v1_funct_2(sK2,X0,X1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(X0,X1,sK2) != X1 ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_2104,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
    inference(instantiation,[status(thm)],[c_1967])).

cnf(c_2105,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
    | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2104])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(k2_funct_1(X0),X2,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1493,plain,
    ( k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_16784,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9078,c_1493])).

cnf(c_25576,plain,
    ( v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) = iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_23174,c_40,c_46,c_47,c_48,c_36,c_49,c_57,c_2105,c_2833,c_9076,c_9079,c_16784])).

cnf(c_25582,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_25576,c_1495])).

cnf(c_27717,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_25582,c_40,c_46,c_47,c_48,c_36,c_49,c_57,c_2108,c_2833,c_3498,c_4833,c_7077,c_23175])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1503,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_6332,plain,
    ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_3663,c_1503])).

cnf(c_9069,plain,
    ( v1_xboole_0(k1_relat_1(sK2)) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9066,c_6332])).

cnf(c_27730,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_xboole_0(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_27717,c_9069])).

cnf(c_0,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1513,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_27972,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27730,c_1513])).

cnf(c_23170,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_23163,c_1499])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1500,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_23169,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    inference(superposition,[status(thm)],[c_23163,c_1500])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
    | k2_relset_1(X1,X2,X0) != X2 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_1489,plain,
    ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
    | k2_relset_1(X0,X1,X2) != X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v2_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_16336,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v2_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9078,c_1489])).

cnf(c_16411,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_16336,c_46,c_49,c_9076,c_9079])).

cnf(c_34,negated_conjecture,
    ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_2304,plain,
    ( k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2295,c_34])).

cnf(c_2502,plain,
    ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_2296,c_2304])).

cnf(c_3662,plain,
    ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_struct_0(sK0) ),
    inference(demodulation,[status(thm)],[c_3658,c_2502])).

cnf(c_9080,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_9066,c_3662])).

cnf(c_16414,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_16411,c_9080])).

cnf(c_23664,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
    | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_23169,c_16414])).

cnf(c_24209,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_23170,c_23664])).

cnf(c_28581,plain,
    ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27972,c_24209])).

cnf(c_38170,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | sK2 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_38154,c_28581])).

cnf(c_38207,plain,
    ( sK2 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_38170])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1497,plain,
    ( v1_funct_2(X0,X1,X2) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3140,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
    | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2850,c_1497])).

cnf(c_4470,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
    | v1_xboole_0(k2_relat_1(sK2)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_3663,c_1497])).

cnf(c_4707,plain,
    ( v1_xboole_0(k2_struct_0(sK0)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3140,c_44,c_45,c_46,c_3664,c_3683,c_4470])).

cnf(c_9075,plain,
    ( v1_xboole_0(k1_relat_1(sK2)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9066,c_4707])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1502,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_23173,plain,
    ( v1_xboole_0(k1_relat_1(sK2)) != iProver_top
    | v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_23163,c_1502])).

cnf(c_24276,plain,
    ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9075,c_23173])).

cnf(c_24505,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_24276,c_1513])).

cnf(c_27975,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | k2_funct_1(sK2) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_27730,c_24505])).

cnf(c_28771,plain,
    ( k2_funct_1(sK2) = k1_xboole_0
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_27975,c_24209])).

cnf(c_38169,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | k2_funct_1(sK2) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_38154,c_28771])).

cnf(c_38239,plain,
    ( k2_funct_1(sK2) = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_38169])).

cnf(c_38240,plain,
    ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_38239,c_38207])).

cnf(c_38273,plain,
    ( k9_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
    inference(light_normalisation,[status(thm)],[c_38168,c_38207,c_38240])).

cnf(c_1510,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_4,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f111])).

cnf(c_3198,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1504])).

cnf(c_3374,plain,
    ( v4_relat_1(X0,X1) = iProver_top
    | r1_tarski(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1510,c_3198])).

cnf(c_5802,plain,
    ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1511,c_3374])).

cnf(c_5930,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5802,c_1506])).

cnf(c_1508,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2063,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_4,c_1508])).

cnf(c_5945,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5930,c_2063])).

cnf(c_2763,plain,
    ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
    inference(superposition,[status(thm)],[c_2063,c_1507])).

cnf(c_5949,plain,
    ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_5945,c_2763])).

cnf(c_38275,plain,
    ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_38273,c_5949])).

cnf(c_38177,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
    | k1_relat_1(sK2) != k1_relat_1(sK2) ),
    inference(demodulation,[status(thm)],[c_38154,c_24209])).

cnf(c_38181,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
    inference(equality_resolution_simp,[status(thm)],[c_38177])).

cnf(c_38214,plain,
    ( k1_relat_1(k2_funct_1(k1_xboole_0)) != k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_38207,c_38181])).

cnf(c_38246,plain,
    ( k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_38240,c_38214])).

cnf(c_38279,plain,
    ( k2_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
    inference(demodulation,[status(thm)],[c_38275,c_38246])).

cnf(c_38286,plain,
    ( $false ),
    inference(equality_resolution_simp,[status(thm)],[c_38279])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:25:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.73/2.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.73/2.00  
% 11.73/2.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.73/2.00  
% 11.73/2.00  ------  iProver source info
% 11.73/2.00  
% 11.73/2.00  git: date: 2020-06-30 10:37:57 +0100
% 11.73/2.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.73/2.00  git: non_committed_changes: false
% 11.73/2.00  git: last_make_outside_of_git: false
% 11.73/2.00  
% 11.73/2.00  ------ 
% 11.73/2.00  ------ Parsing...
% 11.73/2.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.73/2.00  
% 11.73/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 11.73/2.00  
% 11.73/2.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.73/2.00  
% 11.73/2.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.73/2.00  ------ Proving...
% 11.73/2.00  ------ Problem Properties 
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  clauses                                 39
% 11.73/2.00  conjectures                             9
% 11.73/2.00  EPR                                     10
% 11.73/2.00  Horn                                    36
% 11.73/2.00  unary                                   12
% 11.73/2.00  binary                                  10
% 11.73/2.00  lits                                    103
% 11.73/2.00  lits eq                                 22
% 11.73/2.00  fd_pure                                 0
% 11.73/2.00  fd_pseudo                               0
% 11.73/2.00  fd_cond                                 2
% 11.73/2.00  fd_pseudo_cond                          2
% 11.73/2.00  AC symbols                              0
% 11.73/2.00  
% 11.73/2.00  ------ Input Options Time Limit: Unbounded
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  ------ 
% 11.73/2.00  Current options:
% 11.73/2.00  ------ 
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  ------ Proving...
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  % SZS status Theorem for theBenchmark.p
% 11.73/2.00  
% 11.73/2.00   Resolution empty clause
% 11.73/2.00  
% 11.73/2.00  % SZS output start CNFRefutation for theBenchmark.p
% 11.73/2.00  
% 11.73/2.00  fof(f24,conjecture,(
% 11.73/2.00    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f25,negated_conjecture,(
% 11.73/2.00    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X0) & k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k2_struct_0(X1))))))),
% 11.73/2.00    inference(negated_conjecture,[],[f24])).
% 11.73/2.00  
% 11.73/2.00  fof(f54,plain,(
% 11.73/2.00    ? [X0] : (? [X1] : (? [X2] : (((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 11.73/2.00    inference(ennf_transformation,[],[f25])).
% 11.73/2.00  
% 11.73/2.00  fof(f55,plain,(
% 11.73/2.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 11.73/2.00    inference(flattening,[],[f54])).
% 11.73/2.00  
% 11.73/2.00  fof(f64,plain,(
% 11.73/2.00    ( ! [X0,X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) != k2_struct_0(X1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) = k2_struct_0(X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(sK2))) )),
% 11.73/2.00    introduced(choice_axiom,[])).
% 11.73/2.00  
% 11.73/2.00  fof(f63,plain,(
% 11.73/2.00    ( ! [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(sK1),X2)) != k2_struct_0(sK1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))) )),
% 11.73/2.00    introduced(choice_axiom,[])).
% 11.73/2.00  
% 11.73/2.00  fof(f62,plain,(
% 11.73/2.00    ? [X0] : (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k2_struct_0(X1)) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 11.73/2.00    introduced(choice_axiom,[])).
% 11.73/2.00  
% 11.73/2.00  fof(f65,plain,(
% 11.73/2.00    (((k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)) & v2_funct_1(sK2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 11.73/2.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f55,f64,f63,f62])).
% 11.73/2.00  
% 11.73/2.00  fof(f103,plain,(
% 11.73/2.00    v1_funct_1(sK2)),
% 11.73/2.00    inference(cnf_transformation,[],[f65])).
% 11.73/2.00  
% 11.73/2.00  fof(f2,axiom,(
% 11.73/2.00    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f56,plain,(
% 11.73/2.00    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.73/2.00    inference(nnf_transformation,[],[f2])).
% 11.73/2.00  
% 11.73/2.00  fof(f57,plain,(
% 11.73/2.00    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.73/2.00    inference(flattening,[],[f56])).
% 11.73/2.00  
% 11.73/2.00  fof(f67,plain,(
% 11.73/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.73/2.00    inference(cnf_transformation,[],[f57])).
% 11.73/2.00  
% 11.73/2.00  fof(f110,plain,(
% 11.73/2.00    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.73/2.00    inference(equality_resolution,[],[f67])).
% 11.73/2.00  
% 11.73/2.00  fof(f10,axiom,(
% 11.73/2.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f33,plain,(
% 11.73/2.00    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.73/2.00    inference(ennf_transformation,[],[f10])).
% 11.73/2.00  
% 11.73/2.00  fof(f34,plain,(
% 11.73/2.00    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.73/2.00    inference(flattening,[],[f33])).
% 11.73/2.00  
% 11.73/2.00  fof(f80,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f34])).
% 11.73/2.00  
% 11.73/2.00  fof(f102,plain,(
% 11.73/2.00    l1_struct_0(sK1)),
% 11.73/2.00    inference(cnf_transformation,[],[f65])).
% 11.73/2.00  
% 11.73/2.00  fof(f21,axiom,(
% 11.73/2.00    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f49,plain,(
% 11.73/2.00    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 11.73/2.00    inference(ennf_transformation,[],[f21])).
% 11.73/2.00  
% 11.73/2.00  fof(f97,plain,(
% 11.73/2.00    ( ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f49])).
% 11.73/2.00  
% 11.73/2.00  fof(f105,plain,(
% 11.73/2.00    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 11.73/2.00    inference(cnf_transformation,[],[f65])).
% 11.73/2.00  
% 11.73/2.00  fof(f100,plain,(
% 11.73/2.00    l1_struct_0(sK0)),
% 11.73/2.00    inference(cnf_transformation,[],[f65])).
% 11.73/2.00  
% 11.73/2.00  fof(f16,axiom,(
% 11.73/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f40,plain,(
% 11.73/2.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.73/2.00    inference(ennf_transformation,[],[f16])).
% 11.73/2.00  
% 11.73/2.00  fof(f86,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.73/2.00    inference(cnf_transformation,[],[f40])).
% 11.73/2.00  
% 11.73/2.00  fof(f106,plain,(
% 11.73/2.00    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 11.73/2.00    inference(cnf_transformation,[],[f65])).
% 11.73/2.00  
% 11.73/2.00  fof(f17,axiom,(
% 11.73/2.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f41,plain,(
% 11.73/2.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 11.73/2.00    inference(ennf_transformation,[],[f17])).
% 11.73/2.00  
% 11.73/2.00  fof(f42,plain,(
% 11.73/2.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 11.73/2.00    inference(flattening,[],[f41])).
% 11.73/2.00  
% 11.73/2.00  fof(f88,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f42])).
% 11.73/2.00  
% 11.73/2.00  fof(f101,plain,(
% 11.73/2.00    ~v2_struct_0(sK1)),
% 11.73/2.00    inference(cnf_transformation,[],[f65])).
% 11.73/2.00  
% 11.73/2.00  fof(f104,plain,(
% 11.73/2.00    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 11.73/2.00    inference(cnf_transformation,[],[f65])).
% 11.73/2.00  
% 11.73/2.00  fof(f22,axiom,(
% 11.73/2.00    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f50,plain,(
% 11.73/2.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 11.73/2.00    inference(ennf_transformation,[],[f22])).
% 11.73/2.00  
% 11.73/2.00  fof(f51,plain,(
% 11.73/2.00    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 11.73/2.00    inference(flattening,[],[f50])).
% 11.73/2.00  
% 11.73/2.00  fof(f98,plain,(
% 11.73/2.00    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f51])).
% 11.73/2.00  
% 11.73/2.00  fof(f19,axiom,(
% 11.73/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f45,plain,(
% 11.73/2.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.73/2.00    inference(ennf_transformation,[],[f19])).
% 11.73/2.00  
% 11.73/2.00  fof(f46,plain,(
% 11.73/2.00    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.73/2.00    inference(flattening,[],[f45])).
% 11.73/2.00  
% 11.73/2.00  fof(f61,plain,(
% 11.73/2.00    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.73/2.00    inference(nnf_transformation,[],[f46])).
% 11.73/2.00  
% 11.73/2.00  fof(f92,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f61])).
% 11.73/2.00  
% 11.73/2.00  fof(f5,axiom,(
% 11.73/2.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f60,plain,(
% 11.73/2.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 11.73/2.00    inference(nnf_transformation,[],[f5])).
% 11.73/2.00  
% 11.73/2.00  fof(f74,plain,(
% 11.73/2.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 11.73/2.00    inference(cnf_transformation,[],[f60])).
% 11.73/2.00  
% 11.73/2.00  fof(f6,axiom,(
% 11.73/2.00    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f29,plain,(
% 11.73/2.00    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.73/2.00    inference(ennf_transformation,[],[f6])).
% 11.73/2.00  
% 11.73/2.00  fof(f76,plain,(
% 11.73/2.00    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f29])).
% 11.73/2.00  
% 11.73/2.00  fof(f75,plain,(
% 11.73/2.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f60])).
% 11.73/2.00  
% 11.73/2.00  fof(f11,axiom,(
% 11.73/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f26,plain,(
% 11.73/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 11.73/2.00    inference(pure_predicate_removal,[],[f11])).
% 11.73/2.00  
% 11.73/2.00  fof(f35,plain,(
% 11.73/2.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.73/2.00    inference(ennf_transformation,[],[f26])).
% 11.73/2.00  
% 11.73/2.00  fof(f81,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.73/2.00    inference(cnf_transformation,[],[f35])).
% 11.73/2.00  
% 11.73/2.00  fof(f7,axiom,(
% 11.73/2.00    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f77,plain,(
% 11.73/2.00    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.73/2.00    inference(cnf_transformation,[],[f7])).
% 11.73/2.00  
% 11.73/2.00  fof(f9,axiom,(
% 11.73/2.00    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f31,plain,(
% 11.73/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 11.73/2.00    inference(ennf_transformation,[],[f9])).
% 11.73/2.00  
% 11.73/2.00  fof(f32,plain,(
% 11.73/2.00    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.73/2.00    inference(flattening,[],[f31])).
% 11.73/2.00  
% 11.73/2.00  fof(f79,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f32])).
% 11.73/2.00  
% 11.73/2.00  fof(f8,axiom,(
% 11.73/2.00    ! [X0,X1] : (v1_relat_1(X1) => k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f30,plain,(
% 11.73/2.00    ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 11.73/2.00    inference(ennf_transformation,[],[f8])).
% 11.73/2.00  
% 11.73/2.00  fof(f78,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k2_relat_1(k7_relat_1(X1,X0)) = k9_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f30])).
% 11.73/2.00  
% 11.73/2.00  fof(f20,axiom,(
% 11.73/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f47,plain,(
% 11.73/2.00    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.73/2.00    inference(ennf_transformation,[],[f20])).
% 11.73/2.00  
% 11.73/2.00  fof(f48,plain,(
% 11.73/2.00    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.73/2.00    inference(flattening,[],[f47])).
% 11.73/2.00  
% 11.73/2.00  fof(f96,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f48])).
% 11.73/2.00  
% 11.73/2.00  fof(f107,plain,(
% 11.73/2.00    v2_funct_1(sK2)),
% 11.73/2.00    inference(cnf_transformation,[],[f65])).
% 11.73/2.00  
% 11.73/2.00  fof(f94,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (v1_funct_1(k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f48])).
% 11.73/2.00  
% 11.73/2.00  fof(f95,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (v1_funct_2(k2_funct_1(X2),X1,X0) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f48])).
% 11.73/2.00  
% 11.73/2.00  fof(f12,axiom,(
% 11.73/2.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_xboole_0(X2)))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f36,plain,(
% 11.73/2.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 11.73/2.00    inference(ennf_transformation,[],[f12])).
% 11.73/2.00  
% 11.73/2.00  fof(f82,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f36])).
% 11.73/2.00  
% 11.73/2.00  fof(f1,axiom,(
% 11.73/2.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f27,plain,(
% 11.73/2.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 11.73/2.00    inference(ennf_transformation,[],[f1])).
% 11.73/2.00  
% 11.73/2.00  fof(f66,plain,(
% 11.73/2.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f27])).
% 11.73/2.00  
% 11.73/2.00  fof(f15,axiom,(
% 11.73/2.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f39,plain,(
% 11.73/2.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.73/2.00    inference(ennf_transformation,[],[f15])).
% 11.73/2.00  
% 11.73/2.00  fof(f85,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.73/2.00    inference(cnf_transformation,[],[f39])).
% 11.73/2.00  
% 11.73/2.00  fof(f23,axiom,(
% 11.73/2.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f52,plain,(
% 11.73/2.00    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 11.73/2.00    inference(ennf_transformation,[],[f23])).
% 11.73/2.00  
% 11.73/2.00  fof(f53,plain,(
% 11.73/2.00    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 11.73/2.00    inference(flattening,[],[f52])).
% 11.73/2.00  
% 11.73/2.00  fof(f99,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f53])).
% 11.73/2.00  
% 11.73/2.00  fof(f108,plain,(
% 11.73/2.00    k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) | k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)),
% 11.73/2.00    inference(cnf_transformation,[],[f65])).
% 11.73/2.00  
% 11.73/2.00  fof(f18,axiom,(
% 11.73/2.00    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)))))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f43,plain,(
% 11.73/2.00    ! [X0,X1] : (! [X2] : (((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 11.73/2.00    inference(ennf_transformation,[],[f18])).
% 11.73/2.00  
% 11.73/2.00  fof(f44,plain,(
% 11.73/2.00    ! [X0,X1] : (! [X2] : ((v1_funct_2(X2,X0,X1) & ~v1_xboole_0(X2) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 11.73/2.00    inference(flattening,[],[f43])).
% 11.73/2.00  
% 11.73/2.00  fof(f90,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f44])).
% 11.73/2.00  
% 11.73/2.00  fof(f13,axiom,(
% 11.73/2.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f37,plain,(
% 11.73/2.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 11.73/2.00    inference(ennf_transformation,[],[f13])).
% 11.73/2.00  
% 11.73/2.00  fof(f83,plain,(
% 11.73/2.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 11.73/2.00    inference(cnf_transformation,[],[f37])).
% 11.73/2.00  
% 11.73/2.00  fof(f3,axiom,(
% 11.73/2.00    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 11.73/2.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.73/2.00  
% 11.73/2.00  fof(f58,plain,(
% 11.73/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.73/2.00    inference(nnf_transformation,[],[f3])).
% 11.73/2.00  
% 11.73/2.00  fof(f59,plain,(
% 11.73/2.00    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 11.73/2.00    inference(flattening,[],[f58])).
% 11.73/2.00  
% 11.73/2.00  fof(f72,plain,(
% 11.73/2.00    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 11.73/2.00    inference(cnf_transformation,[],[f59])).
% 11.73/2.00  
% 11.73/2.00  fof(f111,plain,(
% 11.73/2.00    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 11.73/2.00    inference(equality_resolution,[],[f72])).
% 11.73/2.00  
% 11.73/2.00  cnf(c_39,negated_conjecture,
% 11.73/2.00      ( v1_funct_1(sK2) ),
% 11.73/2.00      inference(cnf_transformation,[],[f103]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1485,plain,
% 11.73/2.00      ( v1_funct_1(sK2) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f110]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1511,plain,
% 11.73/2.00      ( r1_tarski(X0,X0) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_14,plain,
% 11.73/2.00      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 11.73/2.00      | ~ v1_funct_1(X1)
% 11.73/2.00      | ~ v2_funct_1(X1)
% 11.73/2.00      | ~ v1_relat_1(X1)
% 11.73/2.00      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
% 11.73/2.00      inference(cnf_transformation,[],[f80]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1505,plain,
% 11.73/2.00      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
% 11.73/2.00      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 11.73/2.00      | v1_funct_1(X0) != iProver_top
% 11.73/2.00      | v2_funct_1(X0) != iProver_top
% 11.73/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_7247,plain,
% 11.73/2.00      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,k1_relat_1(X0))) = k1_relat_1(X0)
% 11.73/2.00      | v1_funct_1(X0) != iProver_top
% 11.73/2.00      | v2_funct_1(X0) != iProver_top
% 11.73/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1511,c_1505]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_37130,plain,
% 11.73/2.00      ( k9_relat_1(k2_funct_1(sK2),k9_relat_1(sK2,k1_relat_1(sK2))) = k1_relat_1(sK2)
% 11.73/2.00      | v2_funct_1(sK2) != iProver_top
% 11.73/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1485,c_7247]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_40,negated_conjecture,
% 11.73/2.00      ( l1_struct_0(sK1) ),
% 11.73/2.00      inference(cnf_transformation,[],[f102]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1484,plain,
% 11.73/2.00      ( l1_struct_0(sK1) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_31,plain,
% 11.73/2.00      ( ~ l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f97]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1491,plain,
% 11.73/2.00      ( u1_struct_0(X0) = k2_struct_0(X0) | l1_struct_0(X0) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2295,plain,
% 11.73/2.00      ( u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1484,c_1491]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_37,negated_conjecture,
% 11.73/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
% 11.73/2.00      inference(cnf_transformation,[],[f105]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1487,plain,
% 11.73/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2302,plain,
% 11.73/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_2295,c_1487]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_42,negated_conjecture,
% 11.73/2.00      ( l1_struct_0(sK0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f100]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1482,plain,
% 11.73/2.00      ( l1_struct_0(sK0) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2296,plain,
% 11.73/2.00      ( u1_struct_0(sK0) = k2_struct_0(sK0) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1482,c_1491]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2850,plain,
% 11.73/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) = iProver_top ),
% 11.73/2.00      inference(light_normalisation,[status(thm)],[c_2302,c_2296]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_20,plain,
% 11.73/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f86]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1499,plain,
% 11.73/2.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.73/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3382,plain,
% 11.73/2.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_2850,c_1499]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_36,negated_conjecture,
% 11.73/2.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 11.73/2.00      inference(cnf_transformation,[],[f106]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2305,plain,
% 11.73/2.00      ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_2295,c_36]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2503,plain,
% 11.73/2.00      ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_2296,c_2305]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3658,plain,
% 11.73/2.00      ( k2_struct_0(sK1) = k2_relat_1(sK2) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_3382,c_2503]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3663,plain,
% 11.73/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) = iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_3658,c_2850]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_21,plain,
% 11.73/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.73/2.00      | v1_partfun1(X0,X1)
% 11.73/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | ~ v1_funct_1(X0)
% 11.73/2.00      | v1_xboole_0(X2) ),
% 11.73/2.00      inference(cnf_transformation,[],[f88]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1498,plain,
% 11.73/2.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 11.73/2.00      | v1_partfun1(X0,X1) = iProver_top
% 11.73/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.73/2.00      | v1_funct_1(X0) != iProver_top
% 11.73/2.00      | v1_xboole_0(X2) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_4468,plain,
% 11.73/2.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.73/2.00      | v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top
% 11.73/2.00      | v1_funct_1(sK2) != iProver_top
% 11.73/2.00      | v1_xboole_0(k2_relat_1(sK2)) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_3663,c_1498]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_41,negated_conjecture,
% 11.73/2.00      ( ~ v2_struct_0(sK1) ),
% 11.73/2.00      inference(cnf_transformation,[],[f101]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_44,plain,
% 11.73/2.00      ( v2_struct_0(sK1) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_45,plain,
% 11.73/2.00      ( l1_struct_0(sK1) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_46,plain,
% 11.73/2.00      ( v1_funct_1(sK2) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38,negated_conjecture,
% 11.73/2.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
% 11.73/2.00      inference(cnf_transformation,[],[f104]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1486,plain,
% 11.73/2.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2303,plain,
% 11.73/2.00      ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_2295,c_1486]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2771,plain,
% 11.73/2.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) = iProver_top ),
% 11.73/2.00      inference(light_normalisation,[status(thm)],[c_2303,c_2296]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3664,plain,
% 11.73/2.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) = iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_3658,c_2771]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_32,plain,
% 11.73/2.00      ( v2_struct_0(X0) | ~ l1_struct_0(X0) | ~ v1_xboole_0(k2_struct_0(X0)) ),
% 11.73/2.00      inference(cnf_transformation,[],[f98]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1490,plain,
% 11.73/2.00      ( v2_struct_0(X0) = iProver_top
% 11.73/2.00      | l1_struct_0(X0) != iProver_top
% 11.73/2.00      | v1_xboole_0(k2_struct_0(X0)) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3683,plain,
% 11.73/2.00      ( v2_struct_0(sK1) = iProver_top
% 11.73/2.00      | l1_struct_0(sK1) != iProver_top
% 11.73/2.00      | v1_xboole_0(k2_relat_1(sK2)) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_3658,c_1490]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_4969,plain,
% 11.73/2.00      ( v1_partfun1(sK2,k2_struct_0(sK0)) = iProver_top ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_4468,c_44,c_45,c_46,c_3664,c_3683]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_27,plain,
% 11.73/2.00      ( ~ v1_partfun1(X0,X1)
% 11.73/2.00      | ~ v4_relat_1(X0,X1)
% 11.73/2.00      | ~ v1_relat_1(X0)
% 11.73/2.00      | k1_relat_1(X0) = X1 ),
% 11.73/2.00      inference(cnf_transformation,[],[f92]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1495,plain,
% 11.73/2.00      ( k1_relat_1(X0) = X1
% 11.73/2.00      | v1_partfun1(X0,X1) != iProver_top
% 11.73/2.00      | v4_relat_1(X0,X1) != iProver_top
% 11.73/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_8679,plain,
% 11.73/2.00      ( k2_struct_0(sK0) = k1_relat_1(sK2)
% 11.73/2.00      | v4_relat_1(sK2,k2_struct_0(sK0)) != iProver_top
% 11.73/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_4969,c_1495]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_9,plain,
% 11.73/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 11.73/2.00      inference(cnf_transformation,[],[f74]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1955,plain,
% 11.73/2.00      ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 11.73/2.00      inference(resolution,[status(thm)],[c_9,c_37]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_660,plain,
% 11.73/2.00      ( X0 != X1 | k2_struct_0(X0) = k2_struct_0(X1) ),
% 11.73/2.00      theory(equality) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2056,plain,
% 11.73/2.00      ( k2_struct_0(sK0) = k2_struct_0(X0) | sK0 != X0 ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_660]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2439,plain,
% 11.73/2.00      ( k2_struct_0(sK0) = k2_struct_0(sK0) | sK0 != sK0 ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_2056]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_643,plain,( X0 = X0 ),theory(equality) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2440,plain,
% 11.73/2.00      ( sK0 = sK0 ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_643]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_10,plain,
% 11.73/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f76]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_8,plain,
% 11.73/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.73/2.00      inference(cnf_transformation,[],[f75]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_249,plain,
% 11.73/2.00      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 11.73/2.00      inference(prop_impl,[status(thm)],[c_8]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_250,plain,
% 11.73/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 11.73/2.00      inference(renaming,[status(thm)],[c_249]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_315,plain,
% 11.73/2.00      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 11.73/2.00      inference(bin_hyper_res,[status(thm)],[c_10,c_250]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1987,plain,
% 11.73/2.00      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 11.73/2.00      | v1_relat_1(X0)
% 11.73/2.00      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_315]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2802,plain,
% 11.73/2.00      ( ~ r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 11.73/2.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
% 11.73/2.00      | v1_relat_1(sK2) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_1987]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_15,plain,
% 11.73/2.00      ( v4_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 11.73/2.00      inference(cnf_transformation,[],[f81]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1504,plain,
% 11.73/2.00      ( v4_relat_1(X0,X1) = iProver_top
% 11.73/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3197,plain,
% 11.73/2.00      ( v4_relat_1(sK2,k2_struct_0(sK0)) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_2850,c_1504]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3215,plain,
% 11.73/2.00      ( v4_relat_1(sK2,k2_struct_0(sK0)) ),
% 11.73/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_3197]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_11,plain,
% 11.73/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.73/2.00      inference(cnf_transformation,[],[f77]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3365,plain,
% 11.73/2.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3682,plain,
% 11.73/2.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
% 11.73/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_3664]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3684,plain,
% 11.73/2.00      ( v2_struct_0(sK1)
% 11.73/2.00      | ~ l1_struct_0(sK1)
% 11.73/2.00      | ~ v1_xboole_0(k2_relat_1(sK2)) ),
% 11.73/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_3683]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_4491,plain,
% 11.73/2.00      ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
% 11.73/2.00      | v1_partfun1(sK2,k2_struct_0(sK0))
% 11.73/2.00      | ~ v1_funct_1(sK2)
% 11.73/2.00      | v1_xboole_0(k2_relat_1(sK2)) ),
% 11.73/2.00      inference(predicate_to_equality_rev,[status(thm)],[c_4468]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_5288,plain,
% 11.73/2.00      ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
% 11.73/2.00      | ~ v4_relat_1(sK2,k2_struct_0(sK0))
% 11.73/2.00      | ~ v1_relat_1(sK2)
% 11.73/2.00      | k1_relat_1(sK2) = k2_struct_0(sK0) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_27]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_644,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2054,plain,
% 11.73/2.00      ( X0 != X1 | k2_struct_0(sK0) != X1 | k2_struct_0(sK0) = X0 ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_644]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2464,plain,
% 11.73/2.00      ( X0 != k2_struct_0(sK0)
% 11.73/2.00      | k2_struct_0(sK0) = X0
% 11.73/2.00      | k2_struct_0(sK0) != k2_struct_0(sK0) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_2054]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_7784,plain,
% 11.73/2.00      ( k2_struct_0(sK0) != k2_struct_0(sK0)
% 11.73/2.00      | k2_struct_0(sK0) = k1_relat_1(sK2)
% 11.73/2.00      | k1_relat_1(sK2) != k2_struct_0(sK0) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_2464]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_9066,plain,
% 11.73/2.00      ( k2_struct_0(sK0) = k1_relat_1(sK2) ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_8679,c_41,c_40,c_39,c_1955,c_2439,c_2440,c_2802,c_3215,
% 11.73/2.00                 c_3365,c_3682,c_3684,c_4491,c_5288,c_7784]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_13,plain,
% 11.73/2.00      ( ~ v4_relat_1(X0,X1) | ~ v1_relat_1(X0) | k7_relat_1(X0,X1) = X0 ),
% 11.73/2.00      inference(cnf_transformation,[],[f79]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1506,plain,
% 11.73/2.00      ( k7_relat_1(X0,X1) = X0
% 11.73/2.00      | v4_relat_1(X0,X1) != iProver_top
% 11.73/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_5378,plain,
% 11.73/2.00      ( k7_relat_1(sK2,k2_struct_0(sK0)) = sK2
% 11.73/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_3197,c_1506]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_5290,plain,
% 11.73/2.00      ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
% 11.73/2.00      | ~ v1_relat_1(sK2)
% 11.73/2.00      | k7_relat_1(sK2,k2_struct_0(sK0)) = sK2 ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_13]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_5527,plain,
% 11.73/2.00      ( k7_relat_1(sK2,k2_struct_0(sK0)) = sK2 ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_5378,c_1955,c_2802,c_3215,c_3365,c_5290]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_9071,plain,
% 11.73/2.00      ( k7_relat_1(sK2,k1_relat_1(sK2)) = sK2 ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_9066,c_5527]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1509,plain,
% 11.73/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.73/2.00      | r1_tarski(X0,X1) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2853,plain,
% 11.73/2.00      ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_2850,c_1509]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3661,plain,
% 11.73/2.00      ( r1_tarski(sK2,k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))) = iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_3658,c_2853]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_9077,plain,
% 11.73/2.00      ( r1_tarski(sK2,k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) = iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_9066,c_3661]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1480,plain,
% 11.73/2.00      ( r1_tarski(X0,X1) != iProver_top
% 11.73/2.00      | v1_relat_1(X1) != iProver_top
% 11.73/2.00      | v1_relat_1(X0) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_315]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_17276,plain,
% 11.73/2.00      ( v1_relat_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))) != iProver_top
% 11.73/2.00      | v1_relat_1(sK2) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_9077,c_1480]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1956,plain,
% 11.73/2.00      ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_1955]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2804,plain,
% 11.73/2.00      ( r1_tarski(sK2,k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 11.73/2.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) != iProver_top
% 11.73/2.00      | v1_relat_1(sK2) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_2802]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3366,plain,
% 11.73/2.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_3365]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_17387,plain,
% 11.73/2.00      ( v1_relat_1(sK2) = iProver_top ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_17276,c_1956,c_2804,c_3366]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_12,plain,
% 11.73/2.00      ( ~ v1_relat_1(X0) | k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1) ),
% 11.73/2.00      inference(cnf_transformation,[],[f78]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1507,plain,
% 11.73/2.00      ( k2_relat_1(k7_relat_1(X0,X1)) = k9_relat_1(X0,X1)
% 11.73/2.00      | v1_relat_1(X0) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_17392,plain,
% 11.73/2.00      ( k2_relat_1(k7_relat_1(sK2,X0)) = k9_relat_1(sK2,X0) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_17387,c_1507]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_17395,plain,
% 11.73/2.00      ( k9_relat_1(sK2,k1_relat_1(sK2)) = k2_relat_1(sK2) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_9071,c_17392]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3660,plain,
% 11.73/2.00      ( k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_3658,c_3382]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_9078,plain,
% 11.73/2.00      ( k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relat_1(sK2) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_9066,c_3660]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_28,plain,
% 11.73/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.73/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | m1_subset_1(k2_funct_1(X0),k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
% 11.73/2.00      | ~ v1_funct_1(X0)
% 11.73/2.00      | ~ v2_funct_1(X0)
% 11.73/2.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 11.73/2.00      inference(cnf_transformation,[],[f96]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1494,plain,
% 11.73/2.00      ( k2_relset_1(X0,X1,X2) != X1
% 11.73/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.73/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.73/2.00      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) = iProver_top
% 11.73/2.00      | v1_funct_1(X2) != iProver_top
% 11.73/2.00      | v2_funct_1(X2) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_22885,plain,
% 11.73/2.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 11.73/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top
% 11.73/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 11.73/2.00      | v1_funct_1(sK2) != iProver_top
% 11.73/2.00      | v2_funct_1(sK2) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_9078,c_1494]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_35,negated_conjecture,
% 11.73/2.00      ( v2_funct_1(sK2) ),
% 11.73/2.00      inference(cnf_transformation,[],[f107]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_49,plain,
% 11.73/2.00      ( v2_funct_1(sK2) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_9076,plain,
% 11.73/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) = iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_9066,c_3663]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_9079,plain,
% 11.73/2.00      ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_9066,c_3664]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_23163,plain,
% 11.73/2.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) = iProver_top ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_22885,c_46,c_49,c_9076,c_9079]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_23175,plain,
% 11.73/2.00      ( v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_23163,c_1504]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_23449,plain,
% 11.73/2.00      ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2)
% 11.73/2.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_23175,c_1506]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_47,plain,
% 11.73/2.00      ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_48,plain,
% 11.73/2.00      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_57,plain,
% 11.73/2.00      ( ~ l1_struct_0(sK1) | u1_struct_0(sK1) = k2_struct_0(sK1) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_31]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1972,plain,
% 11.73/2.00      ( ~ v1_funct_2(sK2,X0,X1)
% 11.73/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 11.73/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.73/2.00      | ~ v1_funct_1(sK2)
% 11.73/2.00      | ~ v2_funct_1(sK2)
% 11.73/2.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_28]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2107,plain,
% 11.73/2.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.73/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 11.73/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.73/2.00      | ~ v1_funct_1(sK2)
% 11.73/2.00      | ~ v2_funct_1(sK2)
% 11.73/2.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_1972]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2108,plain,
% 11.73/2.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 11.73/2.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.73/2.00      | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) = iProver_top
% 11.73/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.73/2.00      | v1_funct_1(sK2) != iProver_top
% 11.73/2.00      | v2_funct_1(sK2) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_2107]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2286,plain,
% 11.73/2.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != X0
% 11.73/2.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 11.73/2.00      | u1_struct_0(sK1) != X0 ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_644]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2833,plain,
% 11.73/2.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = u1_struct_0(sK1)
% 11.73/2.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
% 11.73/2.00      | u1_struct_0(sK1) != k2_struct_0(sK1) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_2286]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2132,plain,
% 11.73/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_9]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3485,plain,
% 11.73/2.00      ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
% 11.73/2.00      | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_2132]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3498,plain,
% 11.73/2.00      ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) != iProver_top
% 11.73/2.00      | r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_3485]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_4829,plain,
% 11.73/2.00      ( ~ r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 11.73/2.00      | ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))
% 11.73/2.00      | v1_relat_1(k2_funct_1(sK2)) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_1987]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_4833,plain,
% 11.73/2.00      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 11.73/2.00      | v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) != iProver_top
% 11.73/2.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_4829]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_7076,plain,
% 11.73/2.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_11]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_7077,plain,
% 11.73/2.00      ( v1_relat_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_7076]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_25903,plain,
% 11.73/2.00      ( k7_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_funct_1(sK2) ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_23449,c_40,c_46,c_47,c_48,c_36,c_49,c_57,c_2108,c_2833,
% 11.73/2.00                 c_3498,c_4833,c_7077]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_23168,plain,
% 11.73/2.00      ( r1_tarski(k2_funct_1(sK2),k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_23163,c_1509]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_23454,plain,
% 11.73/2.00      ( v1_relat_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))) != iProver_top
% 11.73/2.00      | v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_23168,c_1480]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_26241,plain,
% 11.73/2.00      ( v1_relat_1(k2_funct_1(sK2)) = iProver_top ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_23454,c_40,c_46,c_47,c_48,c_36,c_49,c_57,c_2108,c_2833,
% 11.73/2.00                 c_3498,c_4833,c_7077]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_26247,plain,
% 11.73/2.00      ( k2_relat_1(k7_relat_1(k2_funct_1(sK2),X0)) = k9_relat_1(k2_funct_1(sK2),X0) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_26241,c_1507]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_29238,plain,
% 11.73/2.00      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_25903,c_26247]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_37141,plain,
% 11.73/2.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 11.73/2.00      | v2_funct_1(sK2) != iProver_top
% 11.73/2.00      | v1_relat_1(sK2) != iProver_top ),
% 11.73/2.00      inference(light_normalisation,[status(thm)],[c_37130,c_17395,c_29238]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38154,plain,
% 11.73/2.00      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2) ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_37141,c_49,c_1956,c_2804,c_3366]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38168,plain,
% 11.73/2.00      ( k9_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) = k1_relat_1(sK2) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_38154,c_29238]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_23174,plain,
% 11.73/2.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) != iProver_top
% 11.73/2.00      | v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) = iProver_top
% 11.73/2.00      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.73/2.00      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_23163,c_1498]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_30,plain,
% 11.73/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.73/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | ~ v1_funct_1(X0)
% 11.73/2.00      | v1_funct_1(k2_funct_1(X0))
% 11.73/2.00      | ~ v2_funct_1(X0)
% 11.73/2.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 11.73/2.00      inference(cnf_transformation,[],[f94]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1967,plain,
% 11.73/2.00      ( ~ v1_funct_2(sK2,X0,X1)
% 11.73/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.73/2.00      | v1_funct_1(k2_funct_1(sK2))
% 11.73/2.00      | ~ v1_funct_1(sK2)
% 11.73/2.00      | ~ v2_funct_1(sK2)
% 11.73/2.00      | k2_relset_1(X0,X1,sK2) != X1 ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_30]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2104,plain,
% 11.73/2.00      ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
% 11.73/2.00      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
% 11.73/2.00      | v1_funct_1(k2_funct_1(sK2))
% 11.73/2.00      | ~ v1_funct_1(sK2)
% 11.73/2.00      | ~ v2_funct_1(sK2)
% 11.73/2.00      | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1) ),
% 11.73/2.00      inference(instantiation,[status(thm)],[c_1967]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2105,plain,
% 11.73/2.00      ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != u1_struct_0(sK1)
% 11.73/2.00      | v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) != iProver_top
% 11.73/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) != iProver_top
% 11.73/2.00      | v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.73/2.00      | v1_funct_1(sK2) != iProver_top
% 11.73/2.00      | v2_funct_1(sK2) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_2104]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_29,plain,
% 11.73/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.73/2.00      | v1_funct_2(k2_funct_1(X0),X2,X1)
% 11.73/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | ~ v1_funct_1(X0)
% 11.73/2.00      | ~ v2_funct_1(X0)
% 11.73/2.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 11.73/2.00      inference(cnf_transformation,[],[f95]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1493,plain,
% 11.73/2.00      ( k2_relset_1(X0,X1,X2) != X1
% 11.73/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.73/2.00      | v1_funct_2(k2_funct_1(X2),X1,X0) = iProver_top
% 11.73/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.73/2.00      | v1_funct_1(X2) != iProver_top
% 11.73/2.00      | v2_funct_1(X2) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_16784,plain,
% 11.73/2.00      ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) = iProver_top
% 11.73/2.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 11.73/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 11.73/2.00      | v1_funct_1(sK2) != iProver_top
% 11.73/2.00      | v2_funct_1(sK2) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_9078,c_1493]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_25576,plain,
% 11.73/2.00      ( v1_partfun1(k2_funct_1(sK2),k2_relat_1(sK2)) = iProver_top
% 11.73/2.00      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_23174,c_40,c_46,c_47,c_48,c_36,c_49,c_57,c_2105,c_2833,
% 11.73/2.00                 c_9076,c_9079,c_16784]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_25582,plain,
% 11.73/2.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 11.73/2.00      | v4_relat_1(k2_funct_1(sK2),k2_relat_1(sK2)) != iProver_top
% 11.73/2.00      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 11.73/2.00      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_25576,c_1495]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_27717,plain,
% 11.73/2.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 11.73/2.00      | v1_xboole_0(k1_relat_1(sK2)) = iProver_top ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_25582,c_40,c_46,c_47,c_48,c_36,c_49,c_57,c_2108,c_2833,
% 11.73/2.00                 c_3498,c_4833,c_7077,c_23175]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_16,plain,
% 11.73/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | ~ v1_xboole_0(X1)
% 11.73/2.00      | v1_xboole_0(X0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f82]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1503,plain,
% 11.73/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.73/2.00      | v1_xboole_0(X1) != iProver_top
% 11.73/2.00      | v1_xboole_0(X0) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_6332,plain,
% 11.73/2.00      ( v1_xboole_0(k2_struct_0(sK0)) != iProver_top
% 11.73/2.00      | v1_xboole_0(sK2) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_3663,c_1503]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_9069,plain,
% 11.73/2.00      ( v1_xboole_0(k1_relat_1(sK2)) != iProver_top
% 11.73/2.00      | v1_xboole_0(sK2) = iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_9066,c_6332]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_27730,plain,
% 11.73/2.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 11.73/2.00      | v1_xboole_0(sK2) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_27717,c_9069]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_0,plain,
% 11.73/2.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 11.73/2.00      inference(cnf_transformation,[],[f66]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1513,plain,
% 11.73/2.00      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_27972,plain,
% 11.73/2.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) | sK2 = k1_xboole_0 ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_27730,c_1513]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_23170,plain,
% 11.73/2.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_23163,c_1499]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_19,plain,
% 11.73/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f85]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1500,plain,
% 11.73/2.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.73/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_23169,plain,
% 11.73/2.00      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_23163,c_1500]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_33,plain,
% 11.73/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.73/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | ~ v1_funct_1(X0)
% 11.73/2.00      | ~ v2_funct_1(X0)
% 11.73/2.00      | k2_tops_2(X1,X2,X0) = k2_funct_1(X0)
% 11.73/2.00      | k2_relset_1(X1,X2,X0) != X2 ),
% 11.73/2.00      inference(cnf_transformation,[],[f99]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1489,plain,
% 11.73/2.00      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
% 11.73/2.00      | k2_relset_1(X0,X1,X2) != X1
% 11.73/2.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 11.73/2.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.73/2.00      | v1_funct_1(X2) != iProver_top
% 11.73/2.00      | v2_funct_1(X2) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_16336,plain,
% 11.73/2.00      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
% 11.73/2.00      | v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) != iProver_top
% 11.73/2.00      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) != iProver_top
% 11.73/2.00      | v1_funct_1(sK2) != iProver_top
% 11.73/2.00      | v2_funct_1(sK2) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_9078,c_1489]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_16411,plain,
% 11.73/2.00      ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_16336,c_46,c_49,c_9076,c_9079]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_34,negated_conjecture,
% 11.73/2.00      ( k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 11.73/2.00      | k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f108]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2304,plain,
% 11.73/2.00      ( k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 11.73/2.00      | k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_2295,c_34]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2502,plain,
% 11.73/2.00      ( k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK1)
% 11.73/2.00      | k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) != k2_struct_0(sK0) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_2296,c_2304]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3662,plain,
% 11.73/2.00      ( k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2)
% 11.73/2.00      | k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) != k2_struct_0(sK0) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_3658,c_2502]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_9080,plain,
% 11.73/2.00      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k2_relat_1(sK2)
% 11.73/2.00      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) != k1_relat_1(sK2) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_9066,c_3662]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_16414,plain,
% 11.73/2.00      ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k2_relat_1(sK2)
% 11.73/2.00      | k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_16411,c_9080]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_23664,plain,
% 11.73/2.00      ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(sK2)
% 11.73/2.00      | k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_23169,c_16414]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_24209,plain,
% 11.73/2.00      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 11.73/2.00      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_23170,c_23664]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_28581,plain,
% 11.73/2.00      ( k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) | sK2 = k1_xboole_0 ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_27972,c_24209]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38170,plain,
% 11.73/2.00      ( k1_relat_1(sK2) != k1_relat_1(sK2) | sK2 = k1_xboole_0 ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_38154,c_28581]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38207,plain,
% 11.73/2.00      ( sK2 = k1_xboole_0 ),
% 11.73/2.00      inference(equality_resolution_simp,[status(thm)],[c_38170]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_24,plain,
% 11.73/2.00      ( ~ v1_funct_2(X0,X1,X2)
% 11.73/2.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | ~ v1_funct_1(X0)
% 11.73/2.00      | ~ v1_xboole_0(X0)
% 11.73/2.00      | v1_xboole_0(X1)
% 11.73/2.00      | v1_xboole_0(X2) ),
% 11.73/2.00      inference(cnf_transformation,[],[f90]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1497,plain,
% 11.73/2.00      ( v1_funct_2(X0,X1,X2) != iProver_top
% 11.73/2.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.73/2.00      | v1_funct_1(X0) != iProver_top
% 11.73/2.00      | v1_xboole_0(X0) != iProver_top
% 11.73/2.00      | v1_xboole_0(X1) = iProver_top
% 11.73/2.00      | v1_xboole_0(X2) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3140,plain,
% 11.73/2.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) != iProver_top
% 11.73/2.00      | v1_funct_1(sK2) != iProver_top
% 11.73/2.00      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
% 11.73/2.00      | v1_xboole_0(k2_struct_0(sK1)) = iProver_top
% 11.73/2.00      | v1_xboole_0(sK2) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_2850,c_1497]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_4470,plain,
% 11.73/2.00      ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) != iProver_top
% 11.73/2.00      | v1_funct_1(sK2) != iProver_top
% 11.73/2.00      | v1_xboole_0(k2_struct_0(sK0)) = iProver_top
% 11.73/2.00      | v1_xboole_0(k2_relat_1(sK2)) = iProver_top
% 11.73/2.00      | v1_xboole_0(sK2) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_3663,c_1497]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_4707,plain,
% 11.73/2.00      ( v1_xboole_0(k2_struct_0(sK0)) = iProver_top
% 11.73/2.00      | v1_xboole_0(sK2) != iProver_top ),
% 11.73/2.00      inference(global_propositional_subsumption,
% 11.73/2.00                [status(thm)],
% 11.73/2.00                [c_3140,c_44,c_45,c_46,c_3664,c_3683,c_4470]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_9075,plain,
% 11.73/2.00      ( v1_xboole_0(k1_relat_1(sK2)) = iProver_top
% 11.73/2.00      | v1_xboole_0(sK2) != iProver_top ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_9066,c_4707]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_17,plain,
% 11.73/2.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.73/2.00      | ~ v1_xboole_0(X2)
% 11.73/2.00      | v1_xboole_0(X0) ),
% 11.73/2.00      inference(cnf_transformation,[],[f83]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1502,plain,
% 11.73/2.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.73/2.00      | v1_xboole_0(X2) != iProver_top
% 11.73/2.00      | v1_xboole_0(X0) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_23173,plain,
% 11.73/2.00      ( v1_xboole_0(k1_relat_1(sK2)) != iProver_top
% 11.73/2.00      | v1_xboole_0(k2_funct_1(sK2)) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_23163,c_1502]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_24276,plain,
% 11.73/2.00      ( v1_xboole_0(k2_funct_1(sK2)) = iProver_top
% 11.73/2.00      | v1_xboole_0(sK2) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_9075,c_23173]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_24505,plain,
% 11.73/2.00      ( k2_funct_1(sK2) = k1_xboole_0 | v1_xboole_0(sK2) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_24276,c_1513]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_27975,plain,
% 11.73/2.00      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 11.73/2.00      | k2_funct_1(sK2) = k1_xboole_0 ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_27730,c_24505]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_28771,plain,
% 11.73/2.00      ( k2_funct_1(sK2) = k1_xboole_0
% 11.73/2.00      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_27975,c_24209]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38169,plain,
% 11.73/2.00      ( k1_relat_1(sK2) != k1_relat_1(sK2) | k2_funct_1(sK2) = k1_xboole_0 ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_38154,c_28771]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38239,plain,
% 11.73/2.00      ( k2_funct_1(sK2) = k1_xboole_0 ),
% 11.73/2.00      inference(equality_resolution_simp,[status(thm)],[c_38169]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38240,plain,
% 11.73/2.00      ( k2_funct_1(k1_xboole_0) = k1_xboole_0 ),
% 11.73/2.00      inference(light_normalisation,[status(thm)],[c_38239,c_38207]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38273,plain,
% 11.73/2.00      ( k9_relat_1(k1_xboole_0,k2_relat_1(k1_xboole_0)) = k1_relat_1(k1_xboole_0) ),
% 11.73/2.00      inference(light_normalisation,[status(thm)],[c_38168,c_38207,c_38240]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1510,plain,
% 11.73/2.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 11.73/2.00      | r1_tarski(X0,X1) != iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_4,plain,
% 11.73/2.00      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 11.73/2.00      inference(cnf_transformation,[],[f111]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3198,plain,
% 11.73/2.00      ( v4_relat_1(X0,X1) = iProver_top
% 11.73/2.00      | m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_4,c_1504]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_3374,plain,
% 11.73/2.00      ( v4_relat_1(X0,X1) = iProver_top
% 11.73/2.00      | r1_tarski(X0,k1_xboole_0) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1510,c_3198]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_5802,plain,
% 11.73/2.00      ( v4_relat_1(k1_xboole_0,X0) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_1511,c_3374]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_5930,plain,
% 11.73/2.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0
% 11.73/2.00      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_5802,c_1506]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_1508,plain,
% 11.73/2.00      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.73/2.00      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2063,plain,
% 11.73/2.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_4,c_1508]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_5945,plain,
% 11.73/2.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 11.73/2.00      inference(global_propositional_subsumption,[status(thm)],[c_5930,c_2063]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_2763,plain,
% 11.73/2.00      ( k2_relat_1(k7_relat_1(k1_xboole_0,X0)) = k9_relat_1(k1_xboole_0,X0) ),
% 11.73/2.00      inference(superposition,[status(thm)],[c_2063,c_1507]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_5949,plain,
% 11.73/2.00      ( k9_relat_1(k1_xboole_0,X0) = k2_relat_1(k1_xboole_0) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_5945,c_2763]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38275,plain,
% 11.73/2.00      ( k1_relat_1(k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_38273,c_5949]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38177,plain,
% 11.73/2.00      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2)
% 11.73/2.00      | k1_relat_1(sK2) != k1_relat_1(sK2) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_38154,c_24209]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38181,plain,
% 11.73/2.00      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(sK2) ),
% 11.73/2.00      inference(equality_resolution_simp,[status(thm)],[c_38177]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38214,plain,
% 11.73/2.00      ( k1_relat_1(k2_funct_1(k1_xboole_0)) != k2_relat_1(k1_xboole_0) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_38207,c_38181]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38246,plain,
% 11.73/2.00      ( k1_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_38240,c_38214]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38279,plain,
% 11.73/2.00      ( k2_relat_1(k1_xboole_0) != k2_relat_1(k1_xboole_0) ),
% 11.73/2.00      inference(demodulation,[status(thm)],[c_38275,c_38246]) ).
% 11.73/2.00  
% 11.73/2.00  cnf(c_38286,plain,
% 11.73/2.00      ( $false ),
% 11.73/2.00      inference(equality_resolution_simp,[status(thm)],[c_38279]) ).
% 11.73/2.00  
% 11.73/2.00  
% 11.73/2.00  % SZS output end CNFRefutation for theBenchmark.p
% 11.73/2.00  
% 11.73/2.00  ------                               Statistics
% 11.73/2.00  
% 11.73/2.00  ------ Selected
% 11.73/2.00  
% 11.73/2.00  total_time:                             1.077
% 11.73/2.00  
%------------------------------------------------------------------------------
