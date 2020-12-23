%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:01:38 EST 2020

% Result     : Theorem 25.97s
% Output     : CNFRefutation 25.97s
% Verified   : 
% Statistics : Number of formulae       :  221 (3111 expanded)
%              Number of clauses        :  140 (1000 expanded)
%              Number of leaves         :   22 ( 746 expanded)
%              Depth                    :   33
%              Number of atoms          :  671 (20476 expanded)
%              Number of equality atoms :  346 (6935 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f18,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( v2_funct_1(X4)
              & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
           => ( k2_relset_1(X0,X1,X3) = X1
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( v2_funct_1(X4)
                & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 )
             => ( k2_relset_1(X0,X1,X3) = X1
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f44,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f45,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f44])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( k2_relset_1(X0,X1,X3) != X1
          & k1_xboole_0 != X2
          & v2_funct_1(X4)
          & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
     => ( k2_relset_1(X0,X1,X3) != X1
        & k1_xboole_0 != X2
        & v2_funct_1(sK4)
        & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2
        & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(sK4,X1,X2)
        & v1_funct_1(sK4) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( k2_relset_1(X0,X1,X3) != X1
            & k1_xboole_0 != X2
            & v2_funct_1(X4)
            & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( k2_relset_1(sK0,sK1,sK3) != sK1
          & k1_xboole_0 != sK2
          & v2_funct_1(X4)
          & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
          & v1_funct_2(X4,sK1,sK2)
          & v1_funct_1(X4) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK3,sK0,sK1)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k2_relset_1(sK0,sK1,sK3) != sK1
    & k1_xboole_0 != sK2
    & v2_funct_1(sK4)
    & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    & v1_funct_2(sK4,sK1,sK2)
    & v1_funct_1(sK4)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK3,sK0,sK1)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f45,f51,f50])).

fof(f83,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f52])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f56,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f84,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f63,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f46])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f54])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( r1_tarski(X0,k2_relat_1(X1))
       => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = X0
      | ~ r1_tarski(X0,k2_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f62,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f67,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f52])).

fof(f86,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f52])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f66,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f43,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f42])).

fof(f80,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f81,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f52])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f41,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f40])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f87,plain,(
    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f52])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f59,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f58,plain,(
    ! [X0,X1] :
      ( r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f55,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f15,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f85,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f89,plain,(
    k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f52])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f90,plain,(
    k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_35,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1203,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_4,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v5_relat_1(X0,X2) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_393,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X3),X4)
    | ~ v1_relat_1(X3)
    | X0 != X3
    | X2 != X4 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_16])).

cnf(c_394,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_398,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_394,c_15])).

cnf(c_399,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_398])).

cnf(c_1201,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_399])).

cnf(c_1865,plain,
    ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_1201])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1204,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_10,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1217,plain,
    ( v1_funct_1(X0) != iProver_top
    | v1_funct_1(k2_funct_1(X0)) = iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1223,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_12,plain,
    ( ~ r1_tarski(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_1215,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3354,plain,
    ( k9_relat_1(X0,k10_relat_1(X0,k2_relat_1(X0))) = k2_relat_1(X0)
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1223,c_1215])).

cnf(c_8990,plain,
    ( k9_relat_1(k2_funct_1(X0),k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0)))) = k2_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1217,c_3354])).

cnf(c_11,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_93,plain,
    ( v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_87857,plain,
    ( v1_relat_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | k9_relat_1(k2_funct_1(X0),k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0)))) = k2_relat_1(k2_funct_1(X0)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_8990,c_93])).

cnf(c_87858,plain,
    ( k9_relat_1(k2_funct_1(X0),k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0)))) = k2_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_87857])).

cnf(c_87865,plain,
    ( k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),k2_relat_1(k2_funct_1(sK4)))) = k2_relat_1(k2_funct_1(sK4))
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_87858])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_1213,plain,
    ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3243,plain,
    ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0)
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_1213])).

cnf(c_30,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_44,plain,
    ( v2_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1205,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1212,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1578,plain,
    ( v1_relat_1(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1212])).

cnf(c_3512,plain,
    ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3243,c_44,c_1578])).

cnf(c_13,plain,
    ( ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1214,plain,
    ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_3339,plain,
    ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0)
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_1214])).

cnf(c_3580,plain,
    ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3339,c_44,c_1578])).

cnf(c_87883,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4)))) = k2_relat_1(k2_funct_1(sK4))
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_87865,c_3512,c_3580])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1207,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3946,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1207])).

cnf(c_41,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_4147,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3946,c_41])).

cnf(c_4148,plain,
    ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_4147])).

cnf(c_4155,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_4148])).

cnf(c_37,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_38,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4278,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4155,c_38])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1209,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4281,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
    | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4278,c_1209])).

cnf(c_40,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_43,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_7555,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4281,c_38,c_40,c_41,c_43])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1210,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_7562,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_7555,c_1210])).

cnf(c_31,negated_conjecture,
    ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_4280,plain,
    ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
    inference(demodulation,[status(thm)],[c_4278,c_31])).

cnf(c_7566,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    inference(light_normalisation,[status(thm)],[c_7562,c_4280])).

cnf(c_1579,plain,
    ( v1_relat_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1203,c_1212])).

cnf(c_6,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1221,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_2654,plain,
    ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1578,c_1221])).

cnf(c_3024,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    inference(superposition,[status(thm)],[c_1579,c_2654])).

cnf(c_5,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1222,plain,
    ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3076,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK4)),k2_relat_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3024,c_1222])).

cnf(c_4138,plain,
    ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK4)),k2_relat_1(sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3076,c_1578])).

cnf(c_7575,plain,
    ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_7566,c_4138])).

cnf(c_1864,plain,
    ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1205,c_1201])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1224,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2548,plain,
    ( k2_relat_1(sK4) = sK2
    | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1864,c_1224])).

cnf(c_7794,plain,
    ( k2_relat_1(sK4) = sK2 ),
    inference(superposition,[status(thm)],[c_7575,c_2548])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1211,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_1981,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1205,c_1211])).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_488,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X0
    | sK2 != X2
    | sK1 != X1
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_33])).

cnf(c_489,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_29,negated_conjecture,
    ( k1_xboole_0 != sK2 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_491,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_32,c_29])).

cnf(c_1983,plain,
    ( k1_relat_1(sK4) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_1981,c_491])).

cnf(c_8,plain,
    ( ~ v1_relat_1(X0)
    | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1219,plain,
    ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1583,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_1578,c_1219])).

cnf(c_2078,plain,
    ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
    inference(demodulation,[status(thm)],[c_1983,c_1583])).

cnf(c_16070,plain,
    ( k10_relat_1(sK4,sK2) = sK1 ),
    inference(demodulation,[status(thm)],[c_7794,c_2078])).

cnf(c_8992,plain,
    ( k9_relat_1(sK4,k10_relat_1(sK4,k2_relat_1(sK4))) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_3354])).

cnf(c_9002,plain,
    ( k9_relat_1(sK4,sK1) = sK2
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8992,c_2078,c_7794])).

cnf(c_9109,plain,
    ( k9_relat_1(sK4,sK1) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9002,c_1578])).

cnf(c_7,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1220,plain,
    ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3583,plain,
    ( r1_tarski(k9_relat_1(sK4,X0),k1_relat_1(k2_funct_1(sK4))) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3580,c_1220])).

cnf(c_3788,plain,
    ( k9_relat_1(sK4,X0) = k1_relat_1(k2_funct_1(sK4))
    | r1_tarski(k1_relat_1(k2_funct_1(sK4)),k9_relat_1(sK4,X0)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3583,c_1224])).

cnf(c_8286,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_8287,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8286])).

cnf(c_13129,plain,
    ( r1_tarski(k1_relat_1(k2_funct_1(sK4)),k9_relat_1(sK4,X0)) != iProver_top
    | k9_relat_1(sK4,X0) = k1_relat_1(k2_funct_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3788,c_41,c_44,c_1578,c_8287])).

cnf(c_13130,plain,
    ( k9_relat_1(sK4,X0) = k1_relat_1(k2_funct_1(sK4))
    | r1_tarski(k1_relat_1(k2_funct_1(sK4)),k9_relat_1(sK4,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_13129])).

cnf(c_13139,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k9_relat_1(sK4,sK1)
    | r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_9109,c_13130])).

cnf(c_13142,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK2
    | r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_13139,c_9109])).

cnf(c_7576,plain,
    ( k9_relat_1(sK4,k2_relat_1(sK3)) = sK2 ),
    inference(demodulation,[status(thm)],[c_7566,c_3024])).

cnf(c_7797,plain,
    ( r1_tarski(sK2,k1_relat_1(k2_funct_1(sK4))) = iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7576,c_3583])).

cnf(c_1216,plain,
    ( v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_2664,plain,
    ( k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0))) = k1_relat_1(k2_funct_1(X0))
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1216,c_1219])).

cnf(c_5403,plain,
    ( k10_relat_1(k2_funct_1(sK4),k2_relat_1(k2_funct_1(sK4))) = k1_relat_1(k2_funct_1(sK4))
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1204,c_2664])).

cnf(c_5407,plain,
    ( k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4))) = k1_relat_1(k2_funct_1(sK4))
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5403,c_3580])).

cnf(c_5700,plain,
    ( k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4))) = k1_relat_1(k2_funct_1(sK4)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5407,c_44,c_1578])).

cnf(c_2545,plain,
    ( k9_relat_1(X0,X1) = k2_relat_1(X0)
    | r1_tarski(k2_relat_1(X0),k9_relat_1(X0,X1)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1224])).

cnf(c_9601,plain,
    ( k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4))) = k2_relat_1(sK4)
    | r1_tarski(k2_relat_1(sK4),k1_relat_1(k2_funct_1(sK4))) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5700,c_2545])).

cnf(c_9616,plain,
    ( k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4))) = sK2
    | r1_tarski(sK2,k1_relat_1(k2_funct_1(sK4))) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_9601,c_5700,c_7794])).

cnf(c_9617,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK2
    | r1_tarski(sK2,k1_relat_1(k2_funct_1(sK4))) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9616,c_5700])).

cnf(c_56088,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_13142,c_41,c_44,c_1578,c_7797,c_8287,c_9617])).

cnf(c_56102,plain,
    ( k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4))) = sK2 ),
    inference(demodulation,[status(thm)],[c_56088,c_5700])).

cnf(c_87884,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = sK1
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_87883,c_16070,c_56102])).

cnf(c_91458,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_87884,c_44,c_1578])).

cnf(c_91499,plain,
    ( k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_91458,c_1215])).

cnf(c_91502,plain,
    ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_91499,c_3580])).

cnf(c_91503,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_91502,c_3512])).

cnf(c_4121,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v2_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4122,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v2_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4121])).

cnf(c_95351,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
    | r1_tarski(X0,sK1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_91503,c_41,c_44,c_1578,c_4122,c_8287])).

cnf(c_95358,plain,
    ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_1865,c_95351])).

cnf(c_95369,plain,
    ( k2_relat_1(sK3) = sK1 ),
    inference(light_normalisation,[status(thm)],[c_95358,c_7576,c_16070])).

cnf(c_721,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1296,plain,
    ( X0 != X1
    | sK1 != X1
    | sK1 = X0 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1363,plain,
    ( X0 != sK1
    | sK1 = X0
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1296])).

cnf(c_1837,plain,
    ( k2_relat_1(sK3) != sK1
    | sK1 = k2_relat_1(sK3)
    | sK1 != sK1 ),
    inference(instantiation,[status(thm)],[c_1363])).

cnf(c_1830,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1265,plain,
    ( k2_relset_1(sK0,sK1,sK3) != X0
    | k2_relset_1(sK0,sK1,sK3) = sK1
    | sK1 != X0 ),
    inference(instantiation,[status(thm)],[c_721])).

cnf(c_1732,plain,
    ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
    | k2_relset_1(sK0,sK1,sK3) = sK1
    | sK1 != k2_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_1265])).

cnf(c_720,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1386,plain,
    ( sK1 = sK1 ),
    inference(instantiation,[status(thm)],[c_720])).

cnf(c_28,negated_conjecture,
    ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
    inference(cnf_transformation,[],[f90])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_95369,c_1837,c_1830,c_1732,c_1386,c_28,c_35])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:35:46 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 25.97/3.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 25.97/3.98  
% 25.97/3.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 25.97/3.98  
% 25.97/3.98  ------  iProver source info
% 25.97/3.98  
% 25.97/3.98  git: date: 2020-06-30 10:37:57 +0100
% 25.97/3.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 25.97/3.98  git: non_committed_changes: false
% 25.97/3.98  git: last_make_outside_of_git: false
% 25.97/3.98  
% 25.97/3.98  ------ 
% 25.97/3.98  
% 25.97/3.98  ------ Input Options
% 25.97/3.98  
% 25.97/3.98  --out_options                           all
% 25.97/3.98  --tptp_safe_out                         true
% 25.97/3.98  --problem_path                          ""
% 25.97/3.98  --include_path                          ""
% 25.97/3.98  --clausifier                            res/vclausify_rel
% 25.97/3.98  --clausifier_options                    ""
% 25.97/3.98  --stdin                                 false
% 25.97/3.98  --stats_out                             all
% 25.97/3.98  
% 25.97/3.98  ------ General Options
% 25.97/3.98  
% 25.97/3.98  --fof                                   false
% 25.97/3.98  --time_out_real                         305.
% 25.97/3.98  --time_out_virtual                      -1.
% 25.97/3.98  --symbol_type_check                     false
% 25.97/3.98  --clausify_out                          false
% 25.97/3.98  --sig_cnt_out                           false
% 25.97/3.98  --trig_cnt_out                          false
% 25.97/3.98  --trig_cnt_out_tolerance                1.
% 25.97/3.98  --trig_cnt_out_sk_spl                   false
% 25.97/3.98  --abstr_cl_out                          false
% 25.97/3.98  
% 25.97/3.98  ------ Global Options
% 25.97/3.98  
% 25.97/3.98  --schedule                              default
% 25.97/3.98  --add_important_lit                     false
% 25.97/3.98  --prop_solver_per_cl                    1000
% 25.97/3.98  --min_unsat_core                        false
% 25.97/3.98  --soft_assumptions                      false
% 25.97/3.98  --soft_lemma_size                       3
% 25.97/3.98  --prop_impl_unit_size                   0
% 25.97/3.98  --prop_impl_unit                        []
% 25.97/3.98  --share_sel_clauses                     true
% 25.97/3.98  --reset_solvers                         false
% 25.97/3.98  --bc_imp_inh                            [conj_cone]
% 25.97/3.98  --conj_cone_tolerance                   3.
% 25.97/3.98  --extra_neg_conj                        none
% 25.97/3.98  --large_theory_mode                     true
% 25.97/3.98  --prolific_symb_bound                   200
% 25.97/3.98  --lt_threshold                          2000
% 25.97/3.98  --clause_weak_htbl                      true
% 25.97/3.98  --gc_record_bc_elim                     false
% 25.97/3.98  
% 25.97/3.98  ------ Preprocessing Options
% 25.97/3.98  
% 25.97/3.98  --preprocessing_flag                    true
% 25.97/3.98  --time_out_prep_mult                    0.1
% 25.97/3.98  --splitting_mode                        input
% 25.97/3.98  --splitting_grd                         true
% 25.97/3.98  --splitting_cvd                         false
% 25.97/3.98  --splitting_cvd_svl                     false
% 25.97/3.98  --splitting_nvd                         32
% 25.97/3.98  --sub_typing                            true
% 25.97/3.98  --prep_gs_sim                           true
% 25.97/3.98  --prep_unflatten                        true
% 25.97/3.98  --prep_res_sim                          true
% 25.97/3.98  --prep_upred                            true
% 25.97/3.98  --prep_sem_filter                       exhaustive
% 25.97/3.98  --prep_sem_filter_out                   false
% 25.97/3.98  --pred_elim                             true
% 25.97/3.98  --res_sim_input                         true
% 25.97/3.98  --eq_ax_congr_red                       true
% 25.97/3.98  --pure_diseq_elim                       true
% 25.97/3.98  --brand_transform                       false
% 25.97/3.98  --non_eq_to_eq                          false
% 25.97/3.98  --prep_def_merge                        true
% 25.97/3.98  --prep_def_merge_prop_impl              false
% 25.97/3.98  --prep_def_merge_mbd                    true
% 25.97/3.98  --prep_def_merge_tr_red                 false
% 25.97/3.98  --prep_def_merge_tr_cl                  false
% 25.97/3.98  --smt_preprocessing                     true
% 25.97/3.98  --smt_ac_axioms                         fast
% 25.97/3.98  --preprocessed_out                      false
% 25.97/3.98  --preprocessed_stats                    false
% 25.97/3.98  
% 25.97/3.98  ------ Abstraction refinement Options
% 25.97/3.98  
% 25.97/3.98  --abstr_ref                             []
% 25.97/3.98  --abstr_ref_prep                        false
% 25.97/3.98  --abstr_ref_until_sat                   false
% 25.97/3.98  --abstr_ref_sig_restrict                funpre
% 25.97/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 25.97/3.98  --abstr_ref_under                       []
% 25.97/3.98  
% 25.97/3.98  ------ SAT Options
% 25.97/3.98  
% 25.97/3.98  --sat_mode                              false
% 25.97/3.98  --sat_fm_restart_options                ""
% 25.97/3.98  --sat_gr_def                            false
% 25.97/3.98  --sat_epr_types                         true
% 25.97/3.98  --sat_non_cyclic_types                  false
% 25.97/3.98  --sat_finite_models                     false
% 25.97/3.98  --sat_fm_lemmas                         false
% 25.97/3.98  --sat_fm_prep                           false
% 25.97/3.98  --sat_fm_uc_incr                        true
% 25.97/3.98  --sat_out_model                         small
% 25.97/3.98  --sat_out_clauses                       false
% 25.97/3.98  
% 25.97/3.98  ------ QBF Options
% 25.97/3.98  
% 25.97/3.98  --qbf_mode                              false
% 25.97/3.98  --qbf_elim_univ                         false
% 25.97/3.98  --qbf_dom_inst                          none
% 25.97/3.98  --qbf_dom_pre_inst                      false
% 25.97/3.98  --qbf_sk_in                             false
% 25.97/3.98  --qbf_pred_elim                         true
% 25.97/3.98  --qbf_split                             512
% 25.97/3.98  
% 25.97/3.98  ------ BMC1 Options
% 25.97/3.98  
% 25.97/3.98  --bmc1_incremental                      false
% 25.97/3.98  --bmc1_axioms                           reachable_all
% 25.97/3.98  --bmc1_min_bound                        0
% 25.97/3.98  --bmc1_max_bound                        -1
% 25.97/3.98  --bmc1_max_bound_default                -1
% 25.97/3.98  --bmc1_symbol_reachability              true
% 25.97/3.98  --bmc1_property_lemmas                  false
% 25.97/3.98  --bmc1_k_induction                      false
% 25.97/3.98  --bmc1_non_equiv_states                 false
% 25.97/3.98  --bmc1_deadlock                         false
% 25.97/3.98  --bmc1_ucm                              false
% 25.97/3.98  --bmc1_add_unsat_core                   none
% 25.97/3.98  --bmc1_unsat_core_children              false
% 25.97/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 25.97/3.98  --bmc1_out_stat                         full
% 25.97/3.98  --bmc1_ground_init                      false
% 25.97/3.98  --bmc1_pre_inst_next_state              false
% 25.97/3.98  --bmc1_pre_inst_state                   false
% 25.97/3.98  --bmc1_pre_inst_reach_state             false
% 25.97/3.98  --bmc1_out_unsat_core                   false
% 25.97/3.98  --bmc1_aig_witness_out                  false
% 25.97/3.98  --bmc1_verbose                          false
% 25.97/3.98  --bmc1_dump_clauses_tptp                false
% 25.97/3.98  --bmc1_dump_unsat_core_tptp             false
% 25.97/3.98  --bmc1_dump_file                        -
% 25.97/3.98  --bmc1_ucm_expand_uc_limit              128
% 25.97/3.98  --bmc1_ucm_n_expand_iterations          6
% 25.97/3.98  --bmc1_ucm_extend_mode                  1
% 25.97/3.98  --bmc1_ucm_init_mode                    2
% 25.97/3.98  --bmc1_ucm_cone_mode                    none
% 25.97/3.98  --bmc1_ucm_reduced_relation_type        0
% 25.97/3.98  --bmc1_ucm_relax_model                  4
% 25.97/3.98  --bmc1_ucm_full_tr_after_sat            true
% 25.97/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 25.97/3.98  --bmc1_ucm_layered_model                none
% 25.97/3.98  --bmc1_ucm_max_lemma_size               10
% 25.97/3.98  
% 25.97/3.98  ------ AIG Options
% 25.97/3.98  
% 25.97/3.98  --aig_mode                              false
% 25.97/3.98  
% 25.97/3.98  ------ Instantiation Options
% 25.97/3.98  
% 25.97/3.98  --instantiation_flag                    true
% 25.97/3.98  --inst_sos_flag                         true
% 25.97/3.98  --inst_sos_phase                        true
% 25.97/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 25.97/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 25.97/3.98  --inst_lit_sel_side                     num_symb
% 25.97/3.98  --inst_solver_per_active                1400
% 25.97/3.98  --inst_solver_calls_frac                1.
% 25.97/3.98  --inst_passive_queue_type               priority_queues
% 25.97/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 25.97/3.98  --inst_passive_queues_freq              [25;2]
% 25.97/3.98  --inst_dismatching                      true
% 25.97/3.98  --inst_eager_unprocessed_to_passive     true
% 25.97/3.98  --inst_prop_sim_given                   true
% 25.97/3.98  --inst_prop_sim_new                     false
% 25.97/3.98  --inst_subs_new                         false
% 25.97/3.98  --inst_eq_res_simp                      false
% 25.97/3.98  --inst_subs_given                       false
% 25.97/3.98  --inst_orphan_elimination               true
% 25.97/3.98  --inst_learning_loop_flag               true
% 25.97/3.98  --inst_learning_start                   3000
% 25.97/3.98  --inst_learning_factor                  2
% 25.97/3.98  --inst_start_prop_sim_after_learn       3
% 25.97/3.98  --inst_sel_renew                        solver
% 25.97/3.98  --inst_lit_activity_flag                true
% 25.97/3.98  --inst_restr_to_given                   false
% 25.97/3.98  --inst_activity_threshold               500
% 25.97/3.98  --inst_out_proof                        true
% 25.97/3.98  
% 25.97/3.98  ------ Resolution Options
% 25.97/3.98  
% 25.97/3.98  --resolution_flag                       true
% 25.97/3.98  --res_lit_sel                           adaptive
% 25.97/3.98  --res_lit_sel_side                      none
% 25.97/3.98  --res_ordering                          kbo
% 25.97/3.98  --res_to_prop_solver                    active
% 25.97/3.98  --res_prop_simpl_new                    false
% 25.97/3.98  --res_prop_simpl_given                  true
% 25.97/3.98  --res_passive_queue_type                priority_queues
% 25.97/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 25.97/3.98  --res_passive_queues_freq               [15;5]
% 25.97/3.98  --res_forward_subs                      full
% 25.97/3.98  --res_backward_subs                     full
% 25.97/3.98  --res_forward_subs_resolution           true
% 25.97/3.98  --res_backward_subs_resolution          true
% 25.97/3.98  --res_orphan_elimination                true
% 25.97/3.98  --res_time_limit                        2.
% 25.97/3.98  --res_out_proof                         true
% 25.97/3.98  
% 25.97/3.98  ------ Superposition Options
% 25.97/3.98  
% 25.97/3.98  --superposition_flag                    true
% 25.97/3.98  --sup_passive_queue_type                priority_queues
% 25.97/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 25.97/3.98  --sup_passive_queues_freq               [8;1;4]
% 25.97/3.98  --demod_completeness_check              fast
% 25.97/3.98  --demod_use_ground                      true
% 25.97/3.98  --sup_to_prop_solver                    passive
% 25.97/3.98  --sup_prop_simpl_new                    true
% 25.97/3.98  --sup_prop_simpl_given                  true
% 25.97/3.98  --sup_fun_splitting                     true
% 25.97/3.98  --sup_smt_interval                      50000
% 25.97/3.98  
% 25.97/3.98  ------ Superposition Simplification Setup
% 25.97/3.98  
% 25.97/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 25.97/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 25.97/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 25.97/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 25.97/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 25.97/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 25.97/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 25.97/3.98  --sup_immed_triv                        [TrivRules]
% 25.97/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 25.97/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 25.97/3.98  --sup_immed_bw_main                     []
% 25.97/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 25.97/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 25.97/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 25.97/3.98  --sup_input_bw                          []
% 25.97/3.98  
% 25.97/3.98  ------ Combination Options
% 25.97/3.98  
% 25.97/3.98  --comb_res_mult                         3
% 25.97/3.98  --comb_sup_mult                         2
% 25.97/3.98  --comb_inst_mult                        10
% 25.97/3.98  
% 25.97/3.98  ------ Debug Options
% 25.97/3.98  
% 25.97/3.98  --dbg_backtrace                         false
% 25.97/3.98  --dbg_dump_prop_clauses                 false
% 25.97/3.98  --dbg_dump_prop_clauses_file            -
% 25.97/3.98  --dbg_out_stat                          false
% 25.97/3.98  ------ Parsing...
% 25.97/3.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 25.97/3.98  
% 25.97/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 25.97/3.98  
% 25.97/3.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 25.97/3.98  
% 25.97/3.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 25.97/3.98  ------ Proving...
% 25.97/3.98  ------ Problem Properties 
% 25.97/3.98  
% 25.97/3.98  
% 25.97/3.98  clauses                                 33
% 25.97/3.98  conjectures                             8
% 25.97/3.98  EPR                                     6
% 25.97/3.98  Horn                                    30
% 25.97/3.98  unary                                   10
% 25.97/3.98  binary                                  8
% 25.97/3.98  lits                                    85
% 25.97/3.98  lits eq                                 25
% 25.97/3.98  fd_pure                                 0
% 25.97/3.98  fd_pseudo                               0
% 25.97/3.98  fd_cond                                 0
% 25.97/3.98  fd_pseudo_cond                          1
% 25.97/3.98  AC symbols                              0
% 25.97/3.98  
% 25.97/3.98  ------ Schedule dynamic 5 is on 
% 25.97/3.98  
% 25.97/3.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 25.97/3.98  
% 25.97/3.98  
% 25.97/3.98  ------ 
% 25.97/3.98  Current options:
% 25.97/3.98  ------ 
% 25.97/3.98  
% 25.97/3.98  ------ Input Options
% 25.97/3.98  
% 25.97/3.98  --out_options                           all
% 25.97/3.98  --tptp_safe_out                         true
% 25.97/3.98  --problem_path                          ""
% 25.97/3.98  --include_path                          ""
% 25.97/3.98  --clausifier                            res/vclausify_rel
% 25.97/3.98  --clausifier_options                    ""
% 25.97/3.98  --stdin                                 false
% 25.97/3.98  --stats_out                             all
% 25.97/3.98  
% 25.97/3.98  ------ General Options
% 25.97/3.98  
% 25.97/3.98  --fof                                   false
% 25.97/3.98  --time_out_real                         305.
% 25.97/3.98  --time_out_virtual                      -1.
% 25.97/3.98  --symbol_type_check                     false
% 25.97/3.98  --clausify_out                          false
% 25.97/3.98  --sig_cnt_out                           false
% 25.97/3.98  --trig_cnt_out                          false
% 25.97/3.98  --trig_cnt_out_tolerance                1.
% 25.97/3.98  --trig_cnt_out_sk_spl                   false
% 25.97/3.98  --abstr_cl_out                          false
% 25.97/3.98  
% 25.97/3.98  ------ Global Options
% 25.97/3.98  
% 25.97/3.98  --schedule                              default
% 25.97/3.98  --add_important_lit                     false
% 25.97/3.98  --prop_solver_per_cl                    1000
% 25.97/3.98  --min_unsat_core                        false
% 25.97/3.98  --soft_assumptions                      false
% 25.97/3.98  --soft_lemma_size                       3
% 25.97/3.98  --prop_impl_unit_size                   0
% 25.97/3.98  --prop_impl_unit                        []
% 25.97/3.98  --share_sel_clauses                     true
% 25.97/3.98  --reset_solvers                         false
% 25.97/3.98  --bc_imp_inh                            [conj_cone]
% 25.97/3.98  --conj_cone_tolerance                   3.
% 25.97/3.98  --extra_neg_conj                        none
% 25.97/3.98  --large_theory_mode                     true
% 25.97/3.98  --prolific_symb_bound                   200
% 25.97/3.98  --lt_threshold                          2000
% 25.97/3.98  --clause_weak_htbl                      true
% 25.97/3.98  --gc_record_bc_elim                     false
% 25.97/3.98  
% 25.97/3.98  ------ Preprocessing Options
% 25.97/3.98  
% 25.97/3.98  --preprocessing_flag                    true
% 25.97/3.98  --time_out_prep_mult                    0.1
% 25.97/3.98  --splitting_mode                        input
% 25.97/3.98  --splitting_grd                         true
% 25.97/3.98  --splitting_cvd                         false
% 25.97/3.98  --splitting_cvd_svl                     false
% 25.97/3.98  --splitting_nvd                         32
% 25.97/3.98  --sub_typing                            true
% 25.97/3.98  --prep_gs_sim                           true
% 25.97/3.98  --prep_unflatten                        true
% 25.97/3.98  --prep_res_sim                          true
% 25.97/3.98  --prep_upred                            true
% 25.97/3.98  --prep_sem_filter                       exhaustive
% 25.97/3.98  --prep_sem_filter_out                   false
% 25.97/3.98  --pred_elim                             true
% 25.97/3.98  --res_sim_input                         true
% 25.97/3.98  --eq_ax_congr_red                       true
% 25.97/3.98  --pure_diseq_elim                       true
% 25.97/3.98  --brand_transform                       false
% 25.97/3.98  --non_eq_to_eq                          false
% 25.97/3.98  --prep_def_merge                        true
% 25.97/3.98  --prep_def_merge_prop_impl              false
% 25.97/3.98  --prep_def_merge_mbd                    true
% 25.97/3.98  --prep_def_merge_tr_red                 false
% 25.97/3.98  --prep_def_merge_tr_cl                  false
% 25.97/3.98  --smt_preprocessing                     true
% 25.97/3.98  --smt_ac_axioms                         fast
% 25.97/3.98  --preprocessed_out                      false
% 25.97/3.98  --preprocessed_stats                    false
% 25.97/3.98  
% 25.97/3.98  ------ Abstraction refinement Options
% 25.97/3.98  
% 25.97/3.98  --abstr_ref                             []
% 25.97/3.98  --abstr_ref_prep                        false
% 25.97/3.98  --abstr_ref_until_sat                   false
% 25.97/3.98  --abstr_ref_sig_restrict                funpre
% 25.97/3.98  --abstr_ref_af_restrict_to_split_sk     false
% 25.97/3.98  --abstr_ref_under                       []
% 25.97/3.98  
% 25.97/3.98  ------ SAT Options
% 25.97/3.98  
% 25.97/3.98  --sat_mode                              false
% 25.97/3.98  --sat_fm_restart_options                ""
% 25.97/3.98  --sat_gr_def                            false
% 25.97/3.98  --sat_epr_types                         true
% 25.97/3.98  --sat_non_cyclic_types                  false
% 25.97/3.98  --sat_finite_models                     false
% 25.97/3.98  --sat_fm_lemmas                         false
% 25.97/3.98  --sat_fm_prep                           false
% 25.97/3.98  --sat_fm_uc_incr                        true
% 25.97/3.98  --sat_out_model                         small
% 25.97/3.98  --sat_out_clauses                       false
% 25.97/3.98  
% 25.97/3.98  ------ QBF Options
% 25.97/3.98  
% 25.97/3.98  --qbf_mode                              false
% 25.97/3.98  --qbf_elim_univ                         false
% 25.97/3.98  --qbf_dom_inst                          none
% 25.97/3.98  --qbf_dom_pre_inst                      false
% 25.97/3.98  --qbf_sk_in                             false
% 25.97/3.98  --qbf_pred_elim                         true
% 25.97/3.98  --qbf_split                             512
% 25.97/3.98  
% 25.97/3.98  ------ BMC1 Options
% 25.97/3.98  
% 25.97/3.98  --bmc1_incremental                      false
% 25.97/3.98  --bmc1_axioms                           reachable_all
% 25.97/3.98  --bmc1_min_bound                        0
% 25.97/3.98  --bmc1_max_bound                        -1
% 25.97/3.98  --bmc1_max_bound_default                -1
% 25.97/3.98  --bmc1_symbol_reachability              true
% 25.97/3.98  --bmc1_property_lemmas                  false
% 25.97/3.98  --bmc1_k_induction                      false
% 25.97/3.98  --bmc1_non_equiv_states                 false
% 25.97/3.98  --bmc1_deadlock                         false
% 25.97/3.98  --bmc1_ucm                              false
% 25.97/3.98  --bmc1_add_unsat_core                   none
% 25.97/3.98  --bmc1_unsat_core_children              false
% 25.97/3.98  --bmc1_unsat_core_extrapolate_axioms    false
% 25.97/3.98  --bmc1_out_stat                         full
% 25.97/3.98  --bmc1_ground_init                      false
% 25.97/3.98  --bmc1_pre_inst_next_state              false
% 25.97/3.98  --bmc1_pre_inst_state                   false
% 25.97/3.98  --bmc1_pre_inst_reach_state             false
% 25.97/3.98  --bmc1_out_unsat_core                   false
% 25.97/3.98  --bmc1_aig_witness_out                  false
% 25.97/3.98  --bmc1_verbose                          false
% 25.97/3.98  --bmc1_dump_clauses_tptp                false
% 25.97/3.98  --bmc1_dump_unsat_core_tptp             false
% 25.97/3.98  --bmc1_dump_file                        -
% 25.97/3.98  --bmc1_ucm_expand_uc_limit              128
% 25.97/3.98  --bmc1_ucm_n_expand_iterations          6
% 25.97/3.98  --bmc1_ucm_extend_mode                  1
% 25.97/3.98  --bmc1_ucm_init_mode                    2
% 25.97/3.98  --bmc1_ucm_cone_mode                    none
% 25.97/3.98  --bmc1_ucm_reduced_relation_type        0
% 25.97/3.98  --bmc1_ucm_relax_model                  4
% 25.97/3.98  --bmc1_ucm_full_tr_after_sat            true
% 25.97/3.98  --bmc1_ucm_expand_neg_assumptions       false
% 25.97/3.98  --bmc1_ucm_layered_model                none
% 25.97/3.98  --bmc1_ucm_max_lemma_size               10
% 25.97/3.98  
% 25.97/3.98  ------ AIG Options
% 25.97/3.98  
% 25.97/3.98  --aig_mode                              false
% 25.97/3.98  
% 25.97/3.98  ------ Instantiation Options
% 25.97/3.98  
% 25.97/3.98  --instantiation_flag                    true
% 25.97/3.98  --inst_sos_flag                         true
% 25.97/3.98  --inst_sos_phase                        true
% 25.97/3.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 25.97/3.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 25.97/3.98  --inst_lit_sel_side                     none
% 25.97/3.98  --inst_solver_per_active                1400
% 25.97/3.98  --inst_solver_calls_frac                1.
% 25.97/3.98  --inst_passive_queue_type               priority_queues
% 25.97/3.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 25.97/3.98  --inst_passive_queues_freq              [25;2]
% 25.97/3.98  --inst_dismatching                      true
% 25.97/3.98  --inst_eager_unprocessed_to_passive     true
% 25.97/3.98  --inst_prop_sim_given                   true
% 25.97/3.98  --inst_prop_sim_new                     false
% 25.97/3.98  --inst_subs_new                         false
% 25.97/3.98  --inst_eq_res_simp                      false
% 25.97/3.98  --inst_subs_given                       false
% 25.97/3.98  --inst_orphan_elimination               true
% 25.97/3.98  --inst_learning_loop_flag               true
% 25.97/3.98  --inst_learning_start                   3000
% 25.97/3.98  --inst_learning_factor                  2
% 25.97/3.98  --inst_start_prop_sim_after_learn       3
% 25.97/3.98  --inst_sel_renew                        solver
% 25.97/3.98  --inst_lit_activity_flag                true
% 25.97/3.98  --inst_restr_to_given                   false
% 25.97/3.98  --inst_activity_threshold               500
% 25.97/3.98  --inst_out_proof                        true
% 25.97/3.98  
% 25.97/3.98  ------ Resolution Options
% 25.97/3.98  
% 25.97/3.98  --resolution_flag                       false
% 25.97/3.98  --res_lit_sel                           adaptive
% 25.97/3.98  --res_lit_sel_side                      none
% 25.97/3.98  --res_ordering                          kbo
% 25.97/3.98  --res_to_prop_solver                    active
% 25.97/3.98  --res_prop_simpl_new                    false
% 25.97/3.98  --res_prop_simpl_given                  true
% 25.97/3.98  --res_passive_queue_type                priority_queues
% 25.97/3.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 25.97/3.98  --res_passive_queues_freq               [15;5]
% 25.97/3.98  --res_forward_subs                      full
% 25.97/3.98  --res_backward_subs                     full
% 25.97/3.98  --res_forward_subs_resolution           true
% 25.97/3.98  --res_backward_subs_resolution          true
% 25.97/3.98  --res_orphan_elimination                true
% 25.97/3.98  --res_time_limit                        2.
% 25.97/3.98  --res_out_proof                         true
% 25.97/3.98  
% 25.97/3.98  ------ Superposition Options
% 25.97/3.98  
% 25.97/3.98  --superposition_flag                    true
% 25.97/3.98  --sup_passive_queue_type                priority_queues
% 25.97/3.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 25.97/3.98  --sup_passive_queues_freq               [8;1;4]
% 25.97/3.98  --demod_completeness_check              fast
% 25.97/3.98  --demod_use_ground                      true
% 25.97/3.98  --sup_to_prop_solver                    passive
% 25.97/3.98  --sup_prop_simpl_new                    true
% 25.97/3.98  --sup_prop_simpl_given                  true
% 25.97/3.98  --sup_fun_splitting                     true
% 25.97/3.98  --sup_smt_interval                      50000
% 25.97/3.98  
% 25.97/3.98  ------ Superposition Simplification Setup
% 25.97/3.98  
% 25.97/3.98  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 25.97/3.98  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 25.97/3.98  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 25.97/3.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 25.97/3.98  --sup_full_triv                         [TrivRules;PropSubs]
% 25.97/3.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 25.97/3.98  --sup_full_bw                           [BwDemod;BwSubsumption]
% 25.97/3.98  --sup_immed_triv                        [TrivRules]
% 25.97/3.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 25.97/3.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 25.97/3.98  --sup_immed_bw_main                     []
% 25.97/3.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 25.97/3.98  --sup_input_triv                        [Unflattening;TrivRules]
% 25.97/3.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 25.97/3.98  --sup_input_bw                          []
% 25.97/3.98  
% 25.97/3.98  ------ Combination Options
% 25.97/3.98  
% 25.97/3.98  --comb_res_mult                         3
% 25.97/3.98  --comb_sup_mult                         2
% 25.97/3.98  --comb_inst_mult                        10
% 25.97/3.98  
% 25.97/3.98  ------ Debug Options
% 25.97/3.98  
% 25.97/3.98  --dbg_backtrace                         false
% 25.97/3.98  --dbg_dump_prop_clauses                 false
% 25.97/3.98  --dbg_dump_prop_clauses_file            -
% 25.97/3.98  --dbg_out_stat                          false
% 25.97/3.98  
% 25.97/3.98  
% 25.97/3.98  
% 25.97/3.98  
% 25.97/3.98  ------ Proving...
% 25.97/3.98  
% 25.97/3.98  
% 25.97/3.98  % SZS status Theorem for theBenchmark.p
% 25.97/3.98  
% 25.97/3.98  % SZS output start CNFRefutation for theBenchmark.p
% 25.97/3.98  
% 25.97/3.98  fof(f18,conjecture,(
% 25.97/3.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f19,negated_conjecture,(
% 25.97/3.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2) => (k2_relset_1(X0,X1,X3) = X1 | k1_xboole_0 = X2))))),
% 25.97/3.98    inference(negated_conjecture,[],[f18])).
% 25.97/3.98  
% 25.97/3.98  fof(f44,plain,(
% 25.97/3.98    ? [X0,X1,X2,X3] : (? [X4] : (((k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2) & (v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 25.97/3.98    inference(ennf_transformation,[],[f19])).
% 25.97/3.98  
% 25.97/3.98  fof(f45,plain,(
% 25.97/3.98    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 25.97/3.98    inference(flattening,[],[f44])).
% 25.97/3.98  
% 25.97/3.98  fof(f51,plain,(
% 25.97/3.98    ( ! [X2,X0,X3,X1] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(sK4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,sK4)) = X2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(sK4,X1,X2) & v1_funct_1(sK4))) )),
% 25.97/3.98    introduced(choice_axiom,[])).
% 25.97/3.98  
% 25.97/3.98  fof(f50,plain,(
% 25.97/3.98    ? [X0,X1,X2,X3] : (? [X4] : (k2_relset_1(X0,X1,X3) != X1 & k1_xboole_0 != X2 & v2_funct_1(X4) & k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(X4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,X4)) = sK2 & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(X4,sK1,sK2) & v1_funct_1(X4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3))),
% 25.97/3.98    introduced(choice_axiom,[])).
% 25.97/3.98  
% 25.97/3.98  fof(f52,plain,(
% 25.97/3.98    (k2_relset_1(sK0,sK1,sK3) != sK1 & k1_xboole_0 != sK2 & v2_funct_1(sK4) & k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) & v1_funct_2(sK4,sK1,sK2) & v1_funct_1(sK4)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK3,sK0,sK1) & v1_funct_1(sK3)),
% 25.97/3.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f45,f51,f50])).
% 25.97/3.98  
% 25.97/3.98  fof(f83,plain,(
% 25.97/3.98    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 25.97/3.98    inference(cnf_transformation,[],[f52])).
% 25.97/3.98  
% 25.97/3.98  fof(f2,axiom,(
% 25.97/3.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f21,plain,(
% 25.97/3.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 25.97/3.98    inference(ennf_transformation,[],[f2])).
% 25.97/3.98  
% 25.97/3.98  fof(f48,plain,(
% 25.97/3.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 25.97/3.98    inference(nnf_transformation,[],[f21])).
% 25.97/3.98  
% 25.97/3.98  fof(f56,plain,(
% 25.97/3.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f48])).
% 25.97/3.98  
% 25.97/3.98  fof(f12,axiom,(
% 25.97/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f20,plain,(
% 25.97/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 25.97/3.98    inference(pure_predicate_removal,[],[f12])).
% 25.97/3.98  
% 25.97/3.98  fof(f35,plain,(
% 25.97/3.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 25.97/3.98    inference(ennf_transformation,[],[f20])).
% 25.97/3.98  
% 25.97/3.98  fof(f69,plain,(
% 25.97/3.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 25.97/3.98    inference(cnf_transformation,[],[f35])).
% 25.97/3.98  
% 25.97/3.98  fof(f11,axiom,(
% 25.97/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f34,plain,(
% 25.97/3.98    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 25.97/3.98    inference(ennf_transformation,[],[f11])).
% 25.97/3.98  
% 25.97/3.98  fof(f68,plain,(
% 25.97/3.98    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 25.97/3.98    inference(cnf_transformation,[],[f34])).
% 25.97/3.98  
% 25.97/3.98  fof(f84,plain,(
% 25.97/3.98    v1_funct_1(sK4)),
% 25.97/3.98    inference(cnf_transformation,[],[f52])).
% 25.97/3.98  
% 25.97/3.98  fof(f7,axiom,(
% 25.97/3.98    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f26,plain,(
% 25.97/3.98    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 25.97/3.98    inference(ennf_transformation,[],[f7])).
% 25.97/3.98  
% 25.97/3.98  fof(f27,plain,(
% 25.97/3.98    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 25.97/3.98    inference(flattening,[],[f26])).
% 25.97/3.98  
% 25.97/3.98  fof(f63,plain,(
% 25.97/3.98    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f27])).
% 25.97/3.98  
% 25.97/3.98  fof(f1,axiom,(
% 25.97/3.98    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f46,plain,(
% 25.97/3.98    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 25.97/3.98    inference(nnf_transformation,[],[f1])).
% 25.97/3.98  
% 25.97/3.98  fof(f47,plain,(
% 25.97/3.98    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 25.97/3.98    inference(flattening,[],[f46])).
% 25.97/3.98  
% 25.97/3.98  fof(f54,plain,(
% 25.97/3.98    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 25.97/3.98    inference(cnf_transformation,[],[f47])).
% 25.97/3.98  
% 25.97/3.98  fof(f91,plain,(
% 25.97/3.98    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 25.97/3.98    inference(equality_resolution,[],[f54])).
% 25.97/3.98  
% 25.97/3.98  fof(f8,axiom,(
% 25.97/3.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (r1_tarski(X0,k2_relat_1(X1)) => k9_relat_1(X1,k10_relat_1(X1,X0)) = X0))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f28,plain,(
% 25.97/3.98    ! [X0,X1] : ((k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 25.97/3.98    inference(ennf_transformation,[],[f8])).
% 25.97/3.98  
% 25.97/3.98  fof(f29,plain,(
% 25.97/3.98    ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 25.97/3.98    inference(flattening,[],[f28])).
% 25.97/3.98  
% 25.97/3.98  fof(f65,plain,(
% 25.97/3.98    ( ! [X0,X1] : (k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 | ~r1_tarski(X0,k2_relat_1(X1)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f29])).
% 25.97/3.98  
% 25.97/3.98  fof(f62,plain,(
% 25.97/3.98    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f27])).
% 25.97/3.98  
% 25.97/3.98  fof(f10,axiom,(
% 25.97/3.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0)))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f32,plain,(
% 25.97/3.98    ! [X0,X1] : ((k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 25.97/3.98    inference(ennf_transformation,[],[f10])).
% 25.97/3.98  
% 25.97/3.98  fof(f33,plain,(
% 25.97/3.98    ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 25.97/3.98    inference(flattening,[],[f32])).
% 25.97/3.98  
% 25.97/3.98  fof(f67,plain,(
% 25.97/3.98    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X1),X0) = k10_relat_1(X1,X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f33])).
% 25.97/3.98  
% 25.97/3.98  fof(f88,plain,(
% 25.97/3.98    v2_funct_1(sK4)),
% 25.97/3.98    inference(cnf_transformation,[],[f52])).
% 25.97/3.98  
% 25.97/3.98  fof(f86,plain,(
% 25.97/3.98    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 25.97/3.98    inference(cnf_transformation,[],[f52])).
% 25.97/3.98  
% 25.97/3.98  fof(f9,axiom,(
% 25.97/3.98    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0)))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f30,plain,(
% 25.97/3.98    ! [X0,X1] : ((k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 25.97/3.98    inference(ennf_transformation,[],[f9])).
% 25.97/3.98  
% 25.97/3.98  fof(f31,plain,(
% 25.97/3.98    ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 25.97/3.98    inference(flattening,[],[f30])).
% 25.97/3.98  
% 25.97/3.98  fof(f66,plain,(
% 25.97/3.98    ( ! [X0,X1] : (k9_relat_1(X1,X0) = k10_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f31])).
% 25.97/3.98  
% 25.97/3.98  fof(f17,axiom,(
% 25.97/3.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f42,plain,(
% 25.97/3.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 25.97/3.98    inference(ennf_transformation,[],[f17])).
% 25.97/3.98  
% 25.97/3.98  fof(f43,plain,(
% 25.97/3.98    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 25.97/3.98    inference(flattening,[],[f42])).
% 25.97/3.98  
% 25.97/3.98  fof(f80,plain,(
% 25.97/3.98    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f43])).
% 25.97/3.98  
% 25.97/3.98  fof(f81,plain,(
% 25.97/3.98    v1_funct_1(sK3)),
% 25.97/3.98    inference(cnf_transformation,[],[f52])).
% 25.97/3.98  
% 25.97/3.98  fof(f16,axiom,(
% 25.97/3.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f40,plain,(
% 25.97/3.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 25.97/3.98    inference(ennf_transformation,[],[f16])).
% 25.97/3.98  
% 25.97/3.98  fof(f41,plain,(
% 25.97/3.98    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 25.97/3.98    inference(flattening,[],[f40])).
% 25.97/3.98  
% 25.97/3.98  fof(f79,plain,(
% 25.97/3.98    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f41])).
% 25.97/3.98  
% 25.97/3.98  fof(f14,axiom,(
% 25.97/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f37,plain,(
% 25.97/3.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 25.97/3.98    inference(ennf_transformation,[],[f14])).
% 25.97/3.98  
% 25.97/3.98  fof(f71,plain,(
% 25.97/3.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 25.97/3.98    inference(cnf_transformation,[],[f37])).
% 25.97/3.98  
% 25.97/3.98  fof(f87,plain,(
% 25.97/3.98    k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2),
% 25.97/3.98    inference(cnf_transformation,[],[f52])).
% 25.97/3.98  
% 25.97/3.98  fof(f4,axiom,(
% 25.97/3.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f23,plain,(
% 25.97/3.98    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 25.97/3.98    inference(ennf_transformation,[],[f4])).
% 25.97/3.98  
% 25.97/3.98  fof(f59,plain,(
% 25.97/3.98    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f23])).
% 25.97/3.98  
% 25.97/3.98  fof(f3,axiom,(
% 25.97/3.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f22,plain,(
% 25.97/3.98    ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1))),
% 25.97/3.98    inference(ennf_transformation,[],[f3])).
% 25.97/3.98  
% 25.97/3.98  fof(f58,plain,(
% 25.97/3.98    ( ! [X0,X1] : (r1_tarski(k9_relat_1(X1,X0),k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f22])).
% 25.97/3.98  
% 25.97/3.98  fof(f55,plain,(
% 25.97/3.98    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f47])).
% 25.97/3.98  
% 25.97/3.98  fof(f13,axiom,(
% 25.97/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f36,plain,(
% 25.97/3.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 25.97/3.98    inference(ennf_transformation,[],[f13])).
% 25.97/3.98  
% 25.97/3.98  fof(f70,plain,(
% 25.97/3.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 25.97/3.98    inference(cnf_transformation,[],[f36])).
% 25.97/3.98  
% 25.97/3.98  fof(f15,axiom,(
% 25.97/3.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f38,plain,(
% 25.97/3.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 25.97/3.98    inference(ennf_transformation,[],[f15])).
% 25.97/3.98  
% 25.97/3.98  fof(f39,plain,(
% 25.97/3.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 25.97/3.98    inference(flattening,[],[f38])).
% 25.97/3.98  
% 25.97/3.98  fof(f49,plain,(
% 25.97/3.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 25.97/3.98    inference(nnf_transformation,[],[f39])).
% 25.97/3.98  
% 25.97/3.98  fof(f72,plain,(
% 25.97/3.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 25.97/3.98    inference(cnf_transformation,[],[f49])).
% 25.97/3.98  
% 25.97/3.98  fof(f85,plain,(
% 25.97/3.98    v1_funct_2(sK4,sK1,sK2)),
% 25.97/3.98    inference(cnf_transformation,[],[f52])).
% 25.97/3.98  
% 25.97/3.98  fof(f89,plain,(
% 25.97/3.98    k1_xboole_0 != sK2),
% 25.97/3.98    inference(cnf_transformation,[],[f52])).
% 25.97/3.98  
% 25.97/3.98  fof(f6,axiom,(
% 25.97/3.98    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f25,plain,(
% 25.97/3.98    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 25.97/3.98    inference(ennf_transformation,[],[f6])).
% 25.97/3.98  
% 25.97/3.98  fof(f61,plain,(
% 25.97/3.98    ( ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f25])).
% 25.97/3.98  
% 25.97/3.98  fof(f5,axiom,(
% 25.97/3.98    ! [X0,X1] : (v1_relat_1(X1) => r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)))),
% 25.97/3.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 25.97/3.98  
% 25.97/3.98  fof(f24,plain,(
% 25.97/3.98    ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1))),
% 25.97/3.98    inference(ennf_transformation,[],[f5])).
% 25.97/3.98  
% 25.97/3.98  fof(f60,plain,(
% 25.97/3.98    ( ! [X0,X1] : (r1_tarski(k10_relat_1(X1,X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 25.97/3.98    inference(cnf_transformation,[],[f24])).
% 25.97/3.98  
% 25.97/3.98  fof(f90,plain,(
% 25.97/3.98    k2_relset_1(sK0,sK1,sK3) != sK1),
% 25.97/3.98    inference(cnf_transformation,[],[f52])).
% 25.97/3.98  
% 25.97/3.98  cnf(c_35,negated_conjecture,
% 25.97/3.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
% 25.97/3.98      inference(cnf_transformation,[],[f83]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1203,plain,
% 25.97/3.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_4,plain,
% 25.97/3.98      ( ~ v5_relat_1(X0,X1)
% 25.97/3.98      | r1_tarski(k2_relat_1(X0),X1)
% 25.97/3.98      | ~ v1_relat_1(X0) ),
% 25.97/3.98      inference(cnf_transformation,[],[f56]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_16,plain,
% 25.97/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 25.97/3.98      | v5_relat_1(X0,X2) ),
% 25.97/3.98      inference(cnf_transformation,[],[f69]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_393,plain,
% 25.97/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 25.97/3.98      | r1_tarski(k2_relat_1(X3),X4)
% 25.97/3.98      | ~ v1_relat_1(X3)
% 25.97/3.98      | X0 != X3
% 25.97/3.98      | X2 != X4 ),
% 25.97/3.98      inference(resolution_lifted,[status(thm)],[c_4,c_16]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_394,plain,
% 25.97/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 25.97/3.98      | r1_tarski(k2_relat_1(X0),X2)
% 25.97/3.98      | ~ v1_relat_1(X0) ),
% 25.97/3.98      inference(unflattening,[status(thm)],[c_393]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_15,plain,
% 25.97/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 25.97/3.98      | v1_relat_1(X0) ),
% 25.97/3.98      inference(cnf_transformation,[],[f68]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_398,plain,
% 25.97/3.98      ( r1_tarski(k2_relat_1(X0),X2)
% 25.97/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_394,c_15]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_399,plain,
% 25.97/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 25.97/3.98      | r1_tarski(k2_relat_1(X0),X2) ),
% 25.97/3.98      inference(renaming,[status(thm)],[c_398]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1201,plain,
% 25.97/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 25.97/3.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_399]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1865,plain,
% 25.97/3.98      ( r1_tarski(k2_relat_1(sK3),sK1) = iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1203,c_1201]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_34,negated_conjecture,
% 25.97/3.98      ( v1_funct_1(sK4) ),
% 25.97/3.98      inference(cnf_transformation,[],[f84]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1204,plain,
% 25.97/3.98      ( v1_funct_1(sK4) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_10,plain,
% 25.97/3.98      ( ~ v1_funct_1(X0)
% 25.97/3.98      | v1_funct_1(k2_funct_1(X0))
% 25.97/3.98      | ~ v2_funct_1(X0)
% 25.97/3.98      | ~ v1_relat_1(X0) ),
% 25.97/3.98      inference(cnf_transformation,[],[f63]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1217,plain,
% 25.97/3.98      ( v1_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_funct_1(k2_funct_1(X0)) = iProver_top
% 25.97/3.98      | v2_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1,plain,
% 25.97/3.98      ( r1_tarski(X0,X0) ),
% 25.97/3.98      inference(cnf_transformation,[],[f91]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1223,plain,
% 25.97/3.98      ( r1_tarski(X0,X0) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_12,plain,
% 25.97/3.98      ( ~ r1_tarski(X0,k2_relat_1(X1))
% 25.97/3.98      | ~ v1_funct_1(X1)
% 25.97/3.98      | ~ v1_relat_1(X1)
% 25.97/3.98      | k9_relat_1(X1,k10_relat_1(X1,X0)) = X0 ),
% 25.97/3.98      inference(cnf_transformation,[],[f65]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1215,plain,
% 25.97/3.98      ( k9_relat_1(X0,k10_relat_1(X0,X1)) = X1
% 25.97/3.98      | r1_tarski(X1,k2_relat_1(X0)) != iProver_top
% 25.97/3.98      | v1_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_3354,plain,
% 25.97/3.98      ( k9_relat_1(X0,k10_relat_1(X0,k2_relat_1(X0))) = k2_relat_1(X0)
% 25.97/3.98      | v1_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1223,c_1215]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_8990,plain,
% 25.97/3.98      ( k9_relat_1(k2_funct_1(X0),k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0)))) = k2_relat_1(k2_funct_1(X0))
% 25.97/3.98      | v1_funct_1(X0) != iProver_top
% 25.97/3.98      | v2_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(k2_funct_1(X0)) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1217,c_3354]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_11,plain,
% 25.97/3.98      ( ~ v1_funct_1(X0)
% 25.97/3.98      | ~ v2_funct_1(X0)
% 25.97/3.98      | ~ v1_relat_1(X0)
% 25.97/3.98      | v1_relat_1(k2_funct_1(X0)) ),
% 25.97/3.98      inference(cnf_transformation,[],[f62]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_93,plain,
% 25.97/3.98      ( v1_funct_1(X0) != iProver_top
% 25.97/3.98      | v2_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_87857,plain,
% 25.97/3.98      ( v1_relat_1(X0) != iProver_top
% 25.97/3.98      | v2_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_funct_1(X0) != iProver_top
% 25.97/3.98      | k9_relat_1(k2_funct_1(X0),k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0)))) = k2_relat_1(k2_funct_1(X0)) ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_8990,c_93]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_87858,plain,
% 25.97/3.98      ( k9_relat_1(k2_funct_1(X0),k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0)))) = k2_relat_1(k2_funct_1(X0))
% 25.97/3.98      | v1_funct_1(X0) != iProver_top
% 25.97/3.98      | v2_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top ),
% 25.97/3.98      inference(renaming,[status(thm)],[c_87857]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_87865,plain,
% 25.97/3.98      ( k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),k2_relat_1(k2_funct_1(sK4)))) = k2_relat_1(k2_funct_1(sK4))
% 25.97/3.98      | v2_funct_1(sK4) != iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1204,c_87858]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_14,plain,
% 25.97/3.98      ( ~ v1_funct_1(X0)
% 25.97/3.98      | ~ v2_funct_1(X0)
% 25.97/3.98      | ~ v1_relat_1(X0)
% 25.97/3.98      | k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1) ),
% 25.97/3.98      inference(cnf_transformation,[],[f67]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1213,plain,
% 25.97/3.98      ( k9_relat_1(k2_funct_1(X0),X1) = k10_relat_1(X0,X1)
% 25.97/3.98      | v1_funct_1(X0) != iProver_top
% 25.97/3.98      | v2_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_3243,plain,
% 25.97/3.98      ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0)
% 25.97/3.98      | v2_funct_1(sK4) != iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1204,c_1213]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_30,negated_conjecture,
% 25.97/3.98      ( v2_funct_1(sK4) ),
% 25.97/3.98      inference(cnf_transformation,[],[f88]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_44,plain,
% 25.97/3.98      ( v2_funct_1(sK4) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_32,negated_conjecture,
% 25.97/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
% 25.97/3.98      inference(cnf_transformation,[],[f86]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1205,plain,
% 25.97/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1212,plain,
% 25.97/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 25.97/3.98      | v1_relat_1(X0) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1578,plain,
% 25.97/3.98      ( v1_relat_1(sK4) = iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1205,c_1212]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_3512,plain,
% 25.97/3.98      ( k9_relat_1(k2_funct_1(sK4),X0) = k10_relat_1(sK4,X0) ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_3243,c_44,c_1578]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_13,plain,
% 25.97/3.98      ( ~ v1_funct_1(X0)
% 25.97/3.98      | ~ v2_funct_1(X0)
% 25.97/3.98      | ~ v1_relat_1(X0)
% 25.97/3.98      | k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1) ),
% 25.97/3.98      inference(cnf_transformation,[],[f66]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1214,plain,
% 25.97/3.98      ( k10_relat_1(k2_funct_1(X0),X1) = k9_relat_1(X0,X1)
% 25.97/3.98      | v1_funct_1(X0) != iProver_top
% 25.97/3.98      | v2_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_3339,plain,
% 25.97/3.98      ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0)
% 25.97/3.98      | v2_funct_1(sK4) != iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1204,c_1214]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_3580,plain,
% 25.97/3.98      ( k10_relat_1(k2_funct_1(sK4),X0) = k9_relat_1(sK4,X0) ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_3339,c_44,c_1578]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_87883,plain,
% 25.97/3.98      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4)))) = k2_relat_1(k2_funct_1(sK4))
% 25.97/3.98      | v2_funct_1(sK4) != iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(demodulation,[status(thm)],[c_87865,c_3512,c_3580]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_27,plain,
% 25.97/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 25.97/3.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 25.97/3.98      | ~ v1_funct_1(X0)
% 25.97/3.98      | ~ v1_funct_1(X3)
% 25.97/3.98      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 25.97/3.98      inference(cnf_transformation,[],[f80]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1207,plain,
% 25.97/3.98      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 25.97/3.98      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 25.97/3.98      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 25.97/3.98      | v1_funct_1(X5) != iProver_top
% 25.97/3.98      | v1_funct_1(X4) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_3946,plain,
% 25.97/3.98      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 25.97/3.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 25.97/3.98      | v1_funct_1(X2) != iProver_top
% 25.97/3.98      | v1_funct_1(sK4) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1205,c_1207]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_41,plain,
% 25.97/3.98      ( v1_funct_1(sK4) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_4147,plain,
% 25.97/3.98      ( v1_funct_1(X2) != iProver_top
% 25.97/3.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 25.97/3.98      | k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4) ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_3946,c_41]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_4148,plain,
% 25.97/3.98      ( k1_partfun1(X0,X1,sK1,sK2,X2,sK4) = k5_relat_1(X2,sK4)
% 25.97/3.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 25.97/3.98      | v1_funct_1(X2) != iProver_top ),
% 25.97/3.98      inference(renaming,[status(thm)],[c_4147]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_4155,plain,
% 25.97/3.98      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
% 25.97/3.98      | v1_funct_1(sK3) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1203,c_4148]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_37,negated_conjecture,
% 25.97/3.98      ( v1_funct_1(sK3) ),
% 25.97/3.98      inference(cnf_transformation,[],[f81]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_38,plain,
% 25.97/3.98      ( v1_funct_1(sK3) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_4278,plain,
% 25.97/3.98      ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_4155,c_38]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_25,plain,
% 25.97/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 25.97/3.98      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 25.97/3.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 25.97/3.98      | ~ v1_funct_1(X0)
% 25.97/3.98      | ~ v1_funct_1(X3) ),
% 25.97/3.98      inference(cnf_transformation,[],[f79]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1209,plain,
% 25.97/3.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 25.97/3.98      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) != iProver_top
% 25.97/3.98      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2))) = iProver_top
% 25.97/3.98      | v1_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_funct_1(X3) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_4281,plain,
% 25.97/3.98      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top
% 25.97/3.98      | m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) != iProver_top
% 25.97/3.98      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) != iProver_top
% 25.97/3.98      | v1_funct_1(sK4) != iProver_top
% 25.97/3.98      | v1_funct_1(sK3) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_4278,c_1209]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_40,plain,
% 25.97/3.98      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_43,plain,
% 25.97/3.98      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_7555,plain,
% 25.97/3.98      ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) = iProver_top ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_4281,c_38,c_40,c_41,c_43]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_18,plain,
% 25.97/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 25.97/3.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 25.97/3.98      inference(cnf_transformation,[],[f71]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1210,plain,
% 25.97/3.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 25.97/3.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_7562,plain,
% 25.97/3.98      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_7555,c_1210]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_31,negated_conjecture,
% 25.97/3.98      ( k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) = sK2 ),
% 25.97/3.98      inference(cnf_transformation,[],[f87]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_4280,plain,
% 25.97/3.98      ( k2_relset_1(sK0,sK2,k5_relat_1(sK3,sK4)) = sK2 ),
% 25.97/3.98      inference(demodulation,[status(thm)],[c_4278,c_31]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_7566,plain,
% 25.97/3.98      ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
% 25.97/3.98      inference(light_normalisation,[status(thm)],[c_7562,c_4280]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1579,plain,
% 25.97/3.98      ( v1_relat_1(sK3) = iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1203,c_1212]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_6,plain,
% 25.97/3.98      ( ~ v1_relat_1(X0)
% 25.97/3.98      | ~ v1_relat_1(X1)
% 25.97/3.98      | k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0)) ),
% 25.97/3.98      inference(cnf_transformation,[],[f59]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1221,plain,
% 25.97/3.98      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 25.97/3.98      | v1_relat_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(X1) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_2654,plain,
% 25.97/3.98      ( k9_relat_1(sK4,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK4))
% 25.97/3.98      | v1_relat_1(X0) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1578,c_1221]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_3024,plain,
% 25.97/3.98      ( k9_relat_1(sK4,k2_relat_1(sK3)) = k2_relat_1(k5_relat_1(sK3,sK4)) ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1579,c_2654]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_5,plain,
% 25.97/3.98      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 25.97/3.98      inference(cnf_transformation,[],[f58]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1222,plain,
% 25.97/3.98      ( r1_tarski(k9_relat_1(X0,X1),k2_relat_1(X0)) = iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_3076,plain,
% 25.97/3.98      ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK4)),k2_relat_1(sK4)) = iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_3024,c_1222]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_4138,plain,
% 25.97/3.98      ( r1_tarski(k2_relat_1(k5_relat_1(sK3,sK4)),k2_relat_1(sK4)) = iProver_top ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_3076,c_1578]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_7575,plain,
% 25.97/3.98      ( r1_tarski(sK2,k2_relat_1(sK4)) = iProver_top ),
% 25.97/3.98      inference(demodulation,[status(thm)],[c_7566,c_4138]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1864,plain,
% 25.97/3.98      ( r1_tarski(k2_relat_1(sK4),sK2) = iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1205,c_1201]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_0,plain,
% 25.97/3.98      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 25.97/3.98      inference(cnf_transformation,[],[f55]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1224,plain,
% 25.97/3.98      ( X0 = X1
% 25.97/3.98      | r1_tarski(X0,X1) != iProver_top
% 25.97/3.98      | r1_tarski(X1,X0) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_2548,plain,
% 25.97/3.98      ( k2_relat_1(sK4) = sK2
% 25.97/3.98      | r1_tarski(sK2,k2_relat_1(sK4)) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1864,c_1224]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_7794,plain,
% 25.97/3.98      ( k2_relat_1(sK4) = sK2 ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_7575,c_2548]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_17,plain,
% 25.97/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 25.97/3.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 25.97/3.98      inference(cnf_transformation,[],[f70]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1211,plain,
% 25.97/3.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 25.97/3.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1981,plain,
% 25.97/3.98      ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1205,c_1211]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_24,plain,
% 25.97/3.98      ( ~ v1_funct_2(X0,X1,X2)
% 25.97/3.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 25.97/3.98      | k1_relset_1(X1,X2,X0) = X1
% 25.97/3.98      | k1_xboole_0 = X2 ),
% 25.97/3.98      inference(cnf_transformation,[],[f72]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_33,negated_conjecture,
% 25.97/3.98      ( v1_funct_2(sK4,sK1,sK2) ),
% 25.97/3.98      inference(cnf_transformation,[],[f85]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_488,plain,
% 25.97/3.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 25.97/3.98      | k1_relset_1(X1,X2,X0) = X1
% 25.97/3.98      | sK4 != X0
% 25.97/3.98      | sK2 != X2
% 25.97/3.98      | sK1 != X1
% 25.97/3.98      | k1_xboole_0 = X2 ),
% 25.97/3.98      inference(resolution_lifted,[status(thm)],[c_24,c_33]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_489,plain,
% 25.97/3.98      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
% 25.97/3.98      | k1_relset_1(sK1,sK2,sK4) = sK1
% 25.97/3.98      | k1_xboole_0 = sK2 ),
% 25.97/3.98      inference(unflattening,[status(thm)],[c_488]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_29,negated_conjecture,
% 25.97/3.98      ( k1_xboole_0 != sK2 ),
% 25.97/3.98      inference(cnf_transformation,[],[f89]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_491,plain,
% 25.97/3.98      ( k1_relset_1(sK1,sK2,sK4) = sK1 ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_489,c_32,c_29]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1983,plain,
% 25.97/3.98      ( k1_relat_1(sK4) = sK1 ),
% 25.97/3.98      inference(light_normalisation,[status(thm)],[c_1981,c_491]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_8,plain,
% 25.97/3.98      ( ~ v1_relat_1(X0)
% 25.97/3.98      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ),
% 25.97/3.98      inference(cnf_transformation,[],[f61]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1219,plain,
% 25.97/3.98      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
% 25.97/3.98      | v1_relat_1(X0) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1583,plain,
% 25.97/3.98      ( k10_relat_1(sK4,k2_relat_1(sK4)) = k1_relat_1(sK4) ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1578,c_1219]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_2078,plain,
% 25.97/3.98      ( k10_relat_1(sK4,k2_relat_1(sK4)) = sK1 ),
% 25.97/3.98      inference(demodulation,[status(thm)],[c_1983,c_1583]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_16070,plain,
% 25.97/3.98      ( k10_relat_1(sK4,sK2) = sK1 ),
% 25.97/3.98      inference(demodulation,[status(thm)],[c_7794,c_2078]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_8992,plain,
% 25.97/3.98      ( k9_relat_1(sK4,k10_relat_1(sK4,k2_relat_1(sK4))) = k2_relat_1(sK4)
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1204,c_3354]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_9002,plain,
% 25.97/3.98      ( k9_relat_1(sK4,sK1) = sK2 | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(light_normalisation,[status(thm)],[c_8992,c_2078,c_7794]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_9109,plain,
% 25.97/3.98      ( k9_relat_1(sK4,sK1) = sK2 ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_9002,c_1578]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_7,plain,
% 25.97/3.98      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) | ~ v1_relat_1(X0) ),
% 25.97/3.98      inference(cnf_transformation,[],[f60]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1220,plain,
% 25.97/3.98      ( r1_tarski(k10_relat_1(X0,X1),k1_relat_1(X0)) = iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_3583,plain,
% 25.97/3.98      ( r1_tarski(k9_relat_1(sK4,X0),k1_relat_1(k2_funct_1(sK4))) = iProver_top
% 25.97/3.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_3580,c_1220]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_3788,plain,
% 25.97/3.98      ( k9_relat_1(sK4,X0) = k1_relat_1(k2_funct_1(sK4))
% 25.97/3.98      | r1_tarski(k1_relat_1(k2_funct_1(sK4)),k9_relat_1(sK4,X0)) != iProver_top
% 25.97/3.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_3583,c_1224]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_8286,plain,
% 25.97/3.98      ( ~ v1_funct_1(sK4)
% 25.97/3.98      | ~ v2_funct_1(sK4)
% 25.97/3.98      | v1_relat_1(k2_funct_1(sK4))
% 25.97/3.98      | ~ v1_relat_1(sK4) ),
% 25.97/3.98      inference(instantiation,[status(thm)],[c_11]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_8287,plain,
% 25.97/3.98      ( v1_funct_1(sK4) != iProver_top
% 25.97/3.98      | v2_funct_1(sK4) != iProver_top
% 25.97/3.98      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_8286]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_13129,plain,
% 25.97/3.98      ( r1_tarski(k1_relat_1(k2_funct_1(sK4)),k9_relat_1(sK4,X0)) != iProver_top
% 25.97/3.98      | k9_relat_1(sK4,X0) = k1_relat_1(k2_funct_1(sK4)) ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_3788,c_41,c_44,c_1578,c_8287]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_13130,plain,
% 25.97/3.98      ( k9_relat_1(sK4,X0) = k1_relat_1(k2_funct_1(sK4))
% 25.97/3.98      | r1_tarski(k1_relat_1(k2_funct_1(sK4)),k9_relat_1(sK4,X0)) != iProver_top ),
% 25.97/3.98      inference(renaming,[status(thm)],[c_13129]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_13139,plain,
% 25.97/3.98      ( k1_relat_1(k2_funct_1(sK4)) = k9_relat_1(sK4,sK1)
% 25.97/3.98      | r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK2) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_9109,c_13130]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_13142,plain,
% 25.97/3.98      ( k1_relat_1(k2_funct_1(sK4)) = sK2
% 25.97/3.98      | r1_tarski(k1_relat_1(k2_funct_1(sK4)),sK2) != iProver_top ),
% 25.97/3.98      inference(light_normalisation,[status(thm)],[c_13139,c_9109]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_7576,plain,
% 25.97/3.98      ( k9_relat_1(sK4,k2_relat_1(sK3)) = sK2 ),
% 25.97/3.98      inference(demodulation,[status(thm)],[c_7566,c_3024]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_7797,plain,
% 25.97/3.98      ( r1_tarski(sK2,k1_relat_1(k2_funct_1(sK4))) = iProver_top
% 25.97/3.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_7576,c_3583]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1216,plain,
% 25.97/3.98      ( v1_funct_1(X0) != iProver_top
% 25.97/3.98      | v2_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(k2_funct_1(X0)) = iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_2664,plain,
% 25.97/3.98      ( k10_relat_1(k2_funct_1(X0),k2_relat_1(k2_funct_1(X0))) = k1_relat_1(k2_funct_1(X0))
% 25.97/3.98      | v1_funct_1(X0) != iProver_top
% 25.97/3.98      | v2_funct_1(X0) != iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1216,c_1219]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_5403,plain,
% 25.97/3.98      ( k10_relat_1(k2_funct_1(sK4),k2_relat_1(k2_funct_1(sK4))) = k1_relat_1(k2_funct_1(sK4))
% 25.97/3.98      | v2_funct_1(sK4) != iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1204,c_2664]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_5407,plain,
% 25.97/3.98      ( k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4))) = k1_relat_1(k2_funct_1(sK4))
% 25.97/3.98      | v2_funct_1(sK4) != iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(demodulation,[status(thm)],[c_5403,c_3580]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_5700,plain,
% 25.97/3.98      ( k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4))) = k1_relat_1(k2_funct_1(sK4)) ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_5407,c_44,c_1578]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_2545,plain,
% 25.97/3.98      ( k9_relat_1(X0,X1) = k2_relat_1(X0)
% 25.97/3.98      | r1_tarski(k2_relat_1(X0),k9_relat_1(X0,X1)) != iProver_top
% 25.97/3.98      | v1_relat_1(X0) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1222,c_1224]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_9601,plain,
% 25.97/3.98      ( k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4))) = k2_relat_1(sK4)
% 25.97/3.98      | r1_tarski(k2_relat_1(sK4),k1_relat_1(k2_funct_1(sK4))) != iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_5700,c_2545]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_9616,plain,
% 25.97/3.98      ( k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4))) = sK2
% 25.97/3.98      | r1_tarski(sK2,k1_relat_1(k2_funct_1(sK4))) != iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(light_normalisation,[status(thm)],[c_9601,c_5700,c_7794]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_9617,plain,
% 25.97/3.98      ( k1_relat_1(k2_funct_1(sK4)) = sK2
% 25.97/3.98      | r1_tarski(sK2,k1_relat_1(k2_funct_1(sK4))) != iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(demodulation,[status(thm)],[c_9616,c_5700]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_56088,plain,
% 25.97/3.98      ( k1_relat_1(k2_funct_1(sK4)) = sK2 ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_13142,c_41,c_44,c_1578,c_7797,c_8287,c_9617]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_56102,plain,
% 25.97/3.98      ( k9_relat_1(sK4,k2_relat_1(k2_funct_1(sK4))) = sK2 ),
% 25.97/3.98      inference(demodulation,[status(thm)],[c_56088,c_5700]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_87884,plain,
% 25.97/3.98      ( k2_relat_1(k2_funct_1(sK4)) = sK1
% 25.97/3.98      | v2_funct_1(sK4) != iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(light_normalisation,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_87883,c_16070,c_56102]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_91458,plain,
% 25.97/3.98      ( k2_relat_1(k2_funct_1(sK4)) = sK1 ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_87884,c_44,c_1578]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_91499,plain,
% 25.97/3.98      ( k9_relat_1(k2_funct_1(sK4),k10_relat_1(k2_funct_1(sK4),X0)) = X0
% 25.97/3.98      | r1_tarski(X0,sK1) != iProver_top
% 25.97/3.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 25.97/3.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_91458,c_1215]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_91502,plain,
% 25.97/3.98      ( k9_relat_1(k2_funct_1(sK4),k9_relat_1(sK4,X0)) = X0
% 25.97/3.98      | r1_tarski(X0,sK1) != iProver_top
% 25.97/3.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 25.97/3.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 25.97/3.98      inference(light_normalisation,[status(thm)],[c_91499,c_3580]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_91503,plain,
% 25.97/3.98      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 25.97/3.98      | r1_tarski(X0,sK1) != iProver_top
% 25.97/3.98      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 25.97/3.98      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 25.97/3.98      inference(demodulation,[status(thm)],[c_91502,c_3512]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_4121,plain,
% 25.97/3.98      ( v1_funct_1(k2_funct_1(sK4))
% 25.97/3.98      | ~ v1_funct_1(sK4)
% 25.97/3.98      | ~ v2_funct_1(sK4)
% 25.97/3.98      | ~ v1_relat_1(sK4) ),
% 25.97/3.98      inference(instantiation,[status(thm)],[c_10]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_4122,plain,
% 25.97/3.98      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 25.97/3.98      | v1_funct_1(sK4) != iProver_top
% 25.97/3.98      | v2_funct_1(sK4) != iProver_top
% 25.97/3.98      | v1_relat_1(sK4) != iProver_top ),
% 25.97/3.98      inference(predicate_to_equality,[status(thm)],[c_4121]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_95351,plain,
% 25.97/3.98      ( k10_relat_1(sK4,k9_relat_1(sK4,X0)) = X0
% 25.97/3.98      | r1_tarski(X0,sK1) != iProver_top ),
% 25.97/3.98      inference(global_propositional_subsumption,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_91503,c_41,c_44,c_1578,c_4122,c_8287]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_95358,plain,
% 25.97/3.98      ( k10_relat_1(sK4,k9_relat_1(sK4,k2_relat_1(sK3))) = k2_relat_1(sK3) ),
% 25.97/3.98      inference(superposition,[status(thm)],[c_1865,c_95351]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_95369,plain,
% 25.97/3.98      ( k2_relat_1(sK3) = sK1 ),
% 25.97/3.98      inference(light_normalisation,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_95358,c_7576,c_16070]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_721,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1296,plain,
% 25.97/3.98      ( X0 != X1 | sK1 != X1 | sK1 = X0 ),
% 25.97/3.98      inference(instantiation,[status(thm)],[c_721]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1363,plain,
% 25.97/3.98      ( X0 != sK1 | sK1 = X0 | sK1 != sK1 ),
% 25.97/3.98      inference(instantiation,[status(thm)],[c_1296]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1837,plain,
% 25.97/3.98      ( k2_relat_1(sK3) != sK1 | sK1 = k2_relat_1(sK3) | sK1 != sK1 ),
% 25.97/3.98      inference(instantiation,[status(thm)],[c_1363]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1830,plain,
% 25.97/3.98      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
% 25.97/3.98      | k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
% 25.97/3.98      inference(instantiation,[status(thm)],[c_18]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1265,plain,
% 25.97/3.98      ( k2_relset_1(sK0,sK1,sK3) != X0
% 25.97/3.98      | k2_relset_1(sK0,sK1,sK3) = sK1
% 25.97/3.98      | sK1 != X0 ),
% 25.97/3.98      inference(instantiation,[status(thm)],[c_721]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1732,plain,
% 25.97/3.98      ( k2_relset_1(sK0,sK1,sK3) != k2_relat_1(sK3)
% 25.97/3.98      | k2_relset_1(sK0,sK1,sK3) = sK1
% 25.97/3.98      | sK1 != k2_relat_1(sK3) ),
% 25.97/3.98      inference(instantiation,[status(thm)],[c_1265]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_720,plain,( X0 = X0 ),theory(equality) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_1386,plain,
% 25.97/3.98      ( sK1 = sK1 ),
% 25.97/3.98      inference(instantiation,[status(thm)],[c_720]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(c_28,negated_conjecture,
% 25.97/3.98      ( k2_relset_1(sK0,sK1,sK3) != sK1 ),
% 25.97/3.98      inference(cnf_transformation,[],[f90]) ).
% 25.97/3.98  
% 25.97/3.98  cnf(contradiction,plain,
% 25.97/3.98      ( $false ),
% 25.97/3.98      inference(minisat,
% 25.97/3.98                [status(thm)],
% 25.97/3.98                [c_95369,c_1837,c_1830,c_1732,c_1386,c_28,c_35]) ).
% 25.97/3.98  
% 25.97/3.98  
% 25.97/3.98  % SZS output end CNFRefutation for theBenchmark.p
% 25.97/3.98  
% 25.97/3.98  ------                               Statistics
% 25.97/3.98  
% 25.97/3.98  ------ General
% 25.97/3.98  
% 25.97/3.98  abstr_ref_over_cycles:                  0
% 25.97/3.98  abstr_ref_under_cycles:                 0
% 25.97/3.98  gc_basic_clause_elim:                   0
% 25.97/3.98  forced_gc_time:                         0
% 25.97/3.98  parsing_time:                           0.011
% 25.97/3.98  unif_index_cands_time:                  0.
% 25.97/3.98  unif_index_add_time:                    0.
% 25.97/3.98  orderings_time:                         0.
% 25.97/3.98  out_proof_time:                         0.033
% 25.97/3.98  total_time:                             3.069
% 25.97/3.98  num_of_symbols:                         55
% 25.97/3.98  num_of_terms:                           68241
% 25.97/3.98  
% 25.97/3.98  ------ Preprocessing
% 25.97/3.98  
% 25.97/3.98  num_of_splits:                          0
% 25.97/3.98  num_of_split_atoms:                     0
% 25.97/3.98  num_of_reused_defs:                     0
% 25.97/3.98  num_eq_ax_congr_red:                    16
% 25.97/3.98  num_of_sem_filtered_clauses:            1
% 25.97/3.98  num_of_subtypes:                        0
% 25.97/3.98  monotx_restored_types:                  0
% 25.97/3.98  sat_num_of_epr_types:                   0
% 25.97/3.98  sat_num_of_non_cyclic_types:            0
% 25.97/3.98  sat_guarded_non_collapsed_types:        0
% 25.97/3.98  num_pure_diseq_elim:                    0
% 25.97/3.98  simp_replaced_by:                       0
% 25.97/3.98  res_preprocessed:                       167
% 25.97/3.98  prep_upred:                             0
% 25.97/3.98  prep_unflattend:                        36
% 25.97/3.98  smt_new_axioms:                         0
% 25.97/3.98  pred_elim_cands:                        5
% 25.97/3.98  pred_elim:                              2
% 25.97/3.98  pred_elim_cl:                           4
% 25.97/3.98  pred_elim_cycles:                       4
% 25.97/3.98  merged_defs:                            0
% 25.97/3.98  merged_defs_ncl:                        0
% 25.97/3.98  bin_hyper_res:                          0
% 25.97/3.98  prep_cycles:                            4
% 25.97/3.98  pred_elim_time:                         0.005
% 25.97/3.98  splitting_time:                         0.
% 25.97/3.98  sem_filter_time:                        0.
% 25.97/3.98  monotx_time:                            0.001
% 25.97/3.98  subtype_inf_time:                       0.
% 25.97/3.98  
% 25.97/3.98  ------ Problem properties
% 25.97/3.98  
% 25.97/3.98  clauses:                                33
% 25.97/3.98  conjectures:                            8
% 25.97/3.98  epr:                                    6
% 25.97/3.98  horn:                                   30
% 25.97/3.98  ground:                                 14
% 25.97/3.98  unary:                                  10
% 25.97/3.98  binary:                                 8
% 25.97/3.98  lits:                                   85
% 25.97/3.98  lits_eq:                                25
% 25.97/3.98  fd_pure:                                0
% 25.97/3.98  fd_pseudo:                              0
% 25.97/3.98  fd_cond:                                0
% 25.97/3.98  fd_pseudo_cond:                         1
% 25.97/3.98  ac_symbols:                             0
% 25.97/3.98  
% 25.97/3.98  ------ Propositional Solver
% 25.97/3.98  
% 25.97/3.98  prop_solver_calls:                      49
% 25.97/3.98  prop_fast_solver_calls:                 5179
% 25.97/3.98  smt_solver_calls:                       0
% 25.97/3.98  smt_fast_solver_calls:                  0
% 25.97/3.98  prop_num_of_clauses:                    37487
% 25.97/3.98  prop_preprocess_simplified:             55676
% 25.97/3.98  prop_fo_subsumed:                       1246
% 25.97/3.98  prop_solver_time:                       0.
% 25.97/3.98  smt_solver_time:                        0.
% 25.97/3.98  smt_fast_solver_time:                   0.
% 25.97/3.98  prop_fast_solver_time:                  0.
% 25.97/3.98  prop_unsat_core_time:                   0.005
% 25.97/3.98  
% 25.97/3.98  ------ QBF
% 25.97/3.98  
% 25.97/3.98  qbf_q_res:                              0
% 25.97/3.98  qbf_num_tautologies:                    0
% 25.97/3.98  qbf_prep_cycles:                        0
% 25.97/3.98  
% 25.97/3.98  ------ BMC1
% 25.97/3.98  
% 25.97/3.98  bmc1_current_bound:                     -1
% 25.97/3.98  bmc1_last_solved_bound:                 -1
% 25.97/3.98  bmc1_unsat_core_size:                   -1
% 25.97/3.98  bmc1_unsat_core_parents_size:           -1
% 25.97/3.98  bmc1_merge_next_fun:                    0
% 25.97/3.98  bmc1_unsat_core_clauses_time:           0.
% 25.97/3.98  
% 25.97/3.98  ------ Instantiation
% 25.97/3.98  
% 25.97/3.98  inst_num_of_clauses:                    6213
% 25.97/3.98  inst_num_in_passive:                    2054
% 25.97/3.98  inst_num_in_active:                     4766
% 25.97/3.98  inst_num_in_unprocessed:                1857
% 25.97/3.98  inst_num_of_loops:                      5379
% 25.97/3.98  inst_num_of_learning_restarts:          1
% 25.97/3.98  inst_num_moves_active_passive:          597
% 25.97/3.98  inst_lit_activity:                      0
% 25.97/3.98  inst_lit_activity_moves:                1
% 25.97/3.98  inst_num_tautologies:                   0
% 25.97/3.98  inst_num_prop_implied:                  0
% 25.97/3.98  inst_num_existing_simplified:           0
% 25.97/3.98  inst_num_eq_res_simplified:             0
% 25.97/3.98  inst_num_child_elim:                    0
% 25.97/3.98  inst_num_of_dismatching_blockings:      9754
% 25.97/3.98  inst_num_of_non_proper_insts:           17352
% 25.97/3.98  inst_num_of_duplicates:                 0
% 25.97/3.98  inst_inst_num_from_inst_to_res:         0
% 25.97/3.98  inst_dismatching_checking_time:         0.
% 25.97/3.98  
% 25.97/3.98  ------ Resolution
% 25.97/3.98  
% 25.97/3.98  res_num_of_clauses:                     48
% 25.97/3.98  res_num_in_passive:                     48
% 25.97/3.98  res_num_in_active:                      0
% 25.97/3.98  res_num_of_loops:                       171
% 25.97/3.98  res_forward_subset_subsumed:            780
% 25.97/3.98  res_backward_subset_subsumed:           2
% 25.97/3.98  res_forward_subsumed:                   0
% 25.97/3.98  res_backward_subsumed:                  0
% 25.97/3.98  res_forward_subsumption_resolution:     0
% 25.97/3.98  res_backward_subsumption_resolution:    0
% 25.97/3.98  res_clause_to_clause_subsumption:       9504
% 25.97/3.98  res_orphan_elimination:                 0
% 25.97/3.98  res_tautology_del:                      1806
% 25.97/3.98  res_num_eq_res_simplified:              0
% 25.97/3.98  res_num_sel_changes:                    0
% 25.97/3.98  res_moves_from_active_to_pass:          0
% 25.97/3.98  
% 25.97/3.98  ------ Superposition
% 25.97/3.98  
% 25.97/3.98  sup_time_total:                         0.
% 25.97/3.98  sup_time_generating:                    0.
% 25.97/3.98  sup_time_sim_full:                      0.
% 25.97/3.98  sup_time_sim_immed:                     0.
% 25.97/3.98  
% 25.97/3.98  sup_num_of_clauses:                     3212
% 25.97/3.98  sup_num_in_active:                      914
% 25.97/3.98  sup_num_in_passive:                     2298
% 25.97/3.98  sup_num_of_loops:                       1075
% 25.97/3.98  sup_fw_superposition:                   2039
% 25.97/3.98  sup_bw_superposition:                   1970
% 25.97/3.98  sup_immediate_simplified:               1559
% 25.97/3.98  sup_given_eliminated:                   5
% 25.97/3.98  comparisons_done:                       0
% 25.97/3.98  comparisons_avoided:                    9
% 25.97/3.98  
% 25.97/3.98  ------ Simplifications
% 25.97/3.98  
% 25.97/3.98  
% 25.97/3.98  sim_fw_subset_subsumed:                 107
% 25.97/3.98  sim_bw_subset_subsumed:                 204
% 25.97/3.98  sim_fw_subsumed:                        128
% 25.97/3.98  sim_bw_subsumed:                        6
% 25.97/3.98  sim_fw_subsumption_res:                 0
% 25.97/3.98  sim_bw_subsumption_res:                 0
% 25.97/3.98  sim_tautology_del:                      0
% 25.97/3.98  sim_eq_tautology_del:                   74
% 25.97/3.98  sim_eq_res_simp:                        0
% 25.97/3.98  sim_fw_demodulated:                     255
% 25.97/3.98  sim_bw_demodulated:                     145
% 25.97/3.98  sim_light_normalised:                   1387
% 25.97/3.98  sim_joinable_taut:                      0
% 25.97/3.98  sim_joinable_simp:                      0
% 25.97/3.98  sim_ac_normalised:                      0
% 25.97/3.98  sim_smt_subsumption:                    0
% 25.97/3.98  
%------------------------------------------------------------------------------
