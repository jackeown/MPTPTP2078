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
% DateTime   : Thu Dec  3 12:06:49 EST 2020

% Result     : Theorem 11.65s
% Output     : CNFRefutation 11.65s
% Verified   : 
% Statistics : Number of formulae       :  308 (3006 expanded)
%              Number of clauses        :  191 ( 974 expanded)
%              Number of leaves         :   34 ( 724 expanded)
%              Depth                    :   20
%              Number of atoms          : 1025 (18072 expanded)
%              Number of equality atoms :  467 (1813 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal clause size      :   18 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f35,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ! [X2] :
          ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
         => ( ( v2_funct_1(X1)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
           => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ! [X2] :
            ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
              & v1_funct_2(X2,X0,X0)
              & v1_funct_1(X2) )
           => ( ( v2_funct_1(X1)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) )
             => r2_relset_1(X0,X0,X2,k6_partfun1(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f35])).

fof(f77,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f78,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f77])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ? [X2] :
          ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
          & v2_funct_1(X1)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
     => ( ~ r2_relset_1(X0,X0,sK2,k6_partfun1(X0))
        & v2_funct_1(X1)
        & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,sK2,X1),X1)
        & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(sK2,X0,X0)
        & v1_funct_1(sK2) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,
    ( ? [X0,X1] :
        ( ? [X2] :
            ( ~ r2_relset_1(X0,X0,X2,k6_partfun1(X0))
            & v2_funct_1(X1)
            & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
            & v1_funct_2(X2,X0,X0)
            & v1_funct_1(X2) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ? [X2] :
          ( ~ r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0))
          & v2_funct_1(sK1)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
          & v1_funct_2(X2,sK0,sK0)
          & v1_funct_1(X2) )
      & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
      & v1_funct_2(sK1,sK0,sK0)
      & v1_funct_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))
    & v2_funct_1(sK1)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK2,sK0,sK0)
    & v1_funct_1(sK2)
    & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    & v1_funct_2(sK1,sK0,sK0)
    & v1_funct_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f78,f84,f83])).

fof(f143,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f85])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f40])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f81])).

fof(f140,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f85])).

fof(f34,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f76,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f75])).

fof(f137,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f138,plain,(
    v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f85])).

fof(f139,plain,(
    v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f14,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( r1_tarski(X1,k1_relat_1(X0))
            & v2_funct_1(X0) )
         => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f48,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
          | ~ r1_tarski(X1,k1_relat_1(X0))
          | ~ v2_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f47])).

fof(f106,plain,(
    ! [X0,X1] :
      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
      | ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f145,plain,(
    v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f85])).

fof(f6,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f94,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f91,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f29,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f67,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f68,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f67])).

fof(f127,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f68])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f62])).

fof(f82,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f63])).

fof(f120,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f144,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f85])).

fof(f141,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f85])).

fof(f27,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f65,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f66,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f65])).

fof(f125,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f66])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f96,plain,(
    ! [X0,X1] :
      ( k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f52,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f51])).

fof(f109,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f33,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f73,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f74,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f73])).

fof(f136,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f108,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f46,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f45])).

fof(f101,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f100,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f26,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f64,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f24,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f119,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f23,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f60,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f31,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f70,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f69])).

fof(f129,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( v2_funct_1(X3)
      | k1_xboole_0 = X2
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f142,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f85])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f79,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f79])).

fof(f87,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f80])).

fof(f158,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f87])).

fof(f89,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f80])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f21,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f28,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f28])).

fof(f126,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f37])).

fof(f121,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_relset_1(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f159,plain,(
    ! [X0,X3,X1] :
      ( r2_relset_1(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(equality_resolution,[],[f121])).

fof(f146,plain,(
    ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f85])).

fof(f3,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( v2_funct_1(X1)
              & v2_funct_1(X0) )
           => k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f55,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
          | ~ v2_funct_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f55])).

fof(f112,plain,(
    ! [X0,X1] :
      ( k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1))
      | ~ v2_funct_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = X0
              & k2_relat_1(X0) = k1_relat_1(X1) )
           => k6_relat_1(k1_relat_1(X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f50,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k6_relat_1(k1_relat_1(X1)) = X1
          | k5_relat_1(X0,X1) != X0
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f49])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k6_relat_1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f30,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f128,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f30])).

fof(f153,plain,(
    ! [X0,X1] :
      ( k6_partfun1(k1_relat_1(X1)) = X1
      | k5_relat_1(X0,X1) != X0
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f107,f128])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f54,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f53])).

fof(f111,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f154,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f111,f128])).

cnf(c_54,negated_conjecture,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_1784,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_28,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_637,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_28,c_7])).

cnf(c_1777,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_637])).

cnf(c_2719,plain,
    ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1777])).

cnf(c_57,negated_conjecture,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_1781,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_50,plain,
    ( ~ v1_funct_2(X0,X1,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
    | ~ v1_funct_1(X0)
    | k1_relset_1(X1,X1,X0) = X1 ),
    inference(cnf_transformation,[],[f137])).

cnf(c_1786,plain,
    ( k1_relset_1(X0,X0,X1) = X0
    | v1_funct_2(X1,X0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_50])).

cnf(c_3974,plain,
    ( k1_relset_1(sK0,sK0,sK1) = sK0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_1786])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1802,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3316,plain,
    ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
    inference(superposition,[status(thm)],[c_1781,c_1802])).

cnf(c_3975,plain,
    ( k1_relat_1(sK1) = sK0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3974,c_3316])).

cnf(c_59,negated_conjecture,
    ( v1_funct_1(sK1) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_60,plain,
    ( v1_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_59])).

cnf(c_58,negated_conjecture,
    ( v1_funct_2(sK1,sK0,sK0) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_61,plain,
    ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_58])).

cnf(c_7071,plain,
    ( k1_relat_1(sK1) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3975,c_60,c_61])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,k1_relat_1(X1))
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1810,plain,
    ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
    | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_7077,plain,
    ( k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top
    | v2_funct_1(sK1) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_7071,c_1810])).

cnf(c_52,negated_conjecture,
    ( v2_funct_1(sK1) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_67,plain,
    ( v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_8,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_183,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_185,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_183])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1819,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_3982,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_1819])).

cnf(c_38398,plain,
    ( r1_tarski(X0,sK0) != iProver_top
    | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7077,c_60,c_67,c_185,c_3982])).

cnf(c_38399,plain,
    ( k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0
    | r1_tarski(X0,sK0) != iProver_top ),
    inference(renaming,[status(thm)],[c_38398])).

cnf(c_38405,plain,
    ( k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k2_relat_1(sK2))) = k2_relat_1(sK2)
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2719,c_38399])).

cnf(c_41,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
    inference(cnf_transformation,[],[f127])).

cnf(c_1794,plain,
    ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
    | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X5) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_7462,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1781,c_1794])).

cnf(c_7744,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7462,c_60])).

cnf(c_7745,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7744])).

cnf(c_7752,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_7745])).

cnf(c_35,plain,
    ( ~ r2_relset_1(X0,X1,X2,X3)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | X3 = X2 ),
    inference(cnf_transformation,[],[f120])).

cnf(c_53,negated_conjecture,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_666,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | X3 = X0
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X0
    | sK1 != X3
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_53])).

cnf(c_667,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(unflattening,[status(thm)],[c_666])).

cnf(c_669,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_667,c_57])).

cnf(c_1776,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_669])).

cnf(c_56,negated_conjecture,
    ( v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f141])).

cnf(c_38,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3) ),
    inference(cnf_transformation,[],[f125])).

cnf(c_1888,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2) ),
    inference(instantiation,[status(thm)],[c_38])).

cnf(c_2449,plain,
    ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1776,c_59,c_57,c_56,c_54,c_667,c_1888])).

cnf(c_7754,plain,
    ( k5_relat_1(sK2,sK1) = sK1
    | v1_funct_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7752,c_2449])).

cnf(c_63,plain,
    ( v1_funct_1(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_56])).

cnf(c_7957,plain,
    ( k5_relat_1(sK2,sK1) = sK1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7754,c_63])).

cnf(c_3981,plain,
    ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
    | v1_relat_1(sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1819])).

cnf(c_4324,plain,
    ( v1_relat_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3981,c_185])).

cnf(c_4499,plain,
    ( v1_relat_1(sK1) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3982,c_185])).

cnf(c_10,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1816,plain,
    ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5016,plain,
    ( k9_relat_1(sK1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK1))
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4499,c_1816])).

cnf(c_6552,plain,
    ( k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
    inference(superposition,[status(thm)],[c_4324,c_5016])).

cnf(c_7959,plain,
    ( k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(sK1) ),
    inference(demodulation,[status(thm)],[c_7957,c_6552])).

cnf(c_1785,plain,
    ( v2_funct_1(sK1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_22,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_1808,plain,
    ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_5952,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1)
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_1808])).

cnf(c_6207,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5952,c_60,c_185,c_3982])).

cnf(c_7074,plain,
    ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_7071,c_6207])).

cnf(c_47,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f136])).

cnf(c_1788,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_47])).

cnf(c_7085,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),sK0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7074,c_1788])).

cnf(c_23,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_1807,plain,
    ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5947,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1)
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_1807])).

cnf(c_6200,plain,
    ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_5947,c_60,c_185,c_3982])).

cnf(c_7088,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK1),sK0))) = iProver_top
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_7085,c_6200])).

cnf(c_14,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f101])).

cnf(c_6059,plain,
    ( v1_funct_1(k2_funct_1(sK1))
    | ~ v1_funct_1(sK1)
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_6060,plain,
    ( v1_funct_1(k2_funct_1(sK1)) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6059])).

cnf(c_15,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_6073,plain,
    ( ~ v1_funct_1(sK1)
    | v1_relat_1(k2_funct_1(sK1))
    | ~ v1_relat_1(sK1) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_6074,plain,
    ( v1_funct_1(sK1) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) = iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6073])).

cnf(c_9273,plain,
    ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK1),sK0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7088,c_60,c_185,c_3982,c_6060,c_6074])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1798,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_9281,plain,
    ( k7_relset_1(k2_relat_1(sK1),sK0,k2_funct_1(sK1),k2_relat_1(sK1)) = k2_relset_1(k2_relat_1(sK1),sK0,k2_funct_1(sK1)) ),
    inference(superposition,[status(thm)],[c_9273,c_1798])).

cnf(c_33,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_1800,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_9282,plain,
    ( k7_relset_1(k2_relat_1(sK1),sK0,k2_funct_1(sK1),X0) = k9_relat_1(k2_funct_1(sK1),X0) ),
    inference(superposition,[status(thm)],[c_9273,c_1800])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1801,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_9284,plain,
    ( k2_relset_1(k2_relat_1(sK1),sK0,k2_funct_1(sK1)) = k2_relat_1(k2_funct_1(sK1)) ),
    inference(superposition,[status(thm)],[c_9273,c_1801])).

cnf(c_9290,plain,
    ( k2_relset_1(k2_relat_1(sK1),sK0,k2_funct_1(sK1)) = sK0 ),
    inference(light_normalisation,[status(thm)],[c_9284,c_7074])).

cnf(c_9292,plain,
    ( k9_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = sK0 ),
    inference(demodulation,[status(thm)],[c_9281,c_9282,c_9290])).

cnf(c_38414,plain,
    ( k2_relat_1(sK2) = sK0
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38405,c_7959,c_9292])).

cnf(c_7461,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1794])).

cnf(c_7648,plain,
    ( v1_funct_1(X2) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7461,c_63])).

cnf(c_7649,plain,
    ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(renaming,[status(thm)],[c_7648])).

cnf(c_7656,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_7649])).

cnf(c_7667,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_7656,c_63])).

cnf(c_43,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(X3,X4,X1)
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v2_funct_1(X3)
    | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f129])).

cnf(c_1792,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(X1,X2,X0) != iProver_top
    | v1_funct_2(X3,X4,X2) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
    | v2_funct_1(X3) = iProver_top
    | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_8055,plain,
    ( sK0 = k1_xboole_0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(k5_relat_1(sK2,sK2)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_7667,c_1792])).

cnf(c_62,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_57])).

cnf(c_55,negated_conjecture,
    ( v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_64,plain,
    ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_55])).

cnf(c_65,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_54])).

cnf(c_3,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f158])).

cnf(c_197,plain,
    ( r1_tarski(sK0,sK0) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_201,plain,
    ( ~ r1_tarski(sK0,sK0)
    | sK0 = sK0 ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_203,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1012,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_2030,plain,
    ( v1_xboole_0(X0)
    | ~ v1_xboole_0(k1_xboole_0)
    | X0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1012])).

cnf(c_2031,plain,
    ( X0 != k1_xboole_0
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2030])).

cnf(c_2033,plain,
    ( sK0 != k1_xboole_0
    | v1_xboole_0(sK0) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2031])).

cnf(c_1011,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2217,plain,
    ( X0 != X1
    | X0 = k1_xboole_0
    | k1_xboole_0 != X1 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_2218,plain,
    ( sK0 != sK0
    | sK0 = k1_xboole_0
    | k1_xboole_0 != sK0 ),
    inference(instantiation,[status(thm)],[c_2217])).

cnf(c_2146,plain,
    ( ~ r1_tarski(X0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1))
    | ~ r1_tarski(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),X0)
    | X0 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_2292,plain,
    ( ~ r1_tarski(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1))
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_2146])).

cnf(c_2701,plain,
    ( r1_tarski(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_2392,plain,
    ( X0 != X1
    | X0 = sK1
    | sK1 != X1 ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_3170,plain,
    ( X0 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | X0 = sK1
    | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_2392])).

cnf(c_3856,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = sK1
    | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
    inference(instantiation,[status(thm)],[c_3170])).

cnf(c_30,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_1803,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_4922,plain,
    ( v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1803])).

cnf(c_40,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f126])).

cnf(c_98,plain,
    ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(instantiation,[status(thm)],[c_40])).

cnf(c_34,plain,
    ( r2_relset_1(X0,X1,X2,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_51,negated_conjecture,
    ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_658,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK0 != X2
    | sK0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_51])).

cnf(c_659,plain,
    ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK2 != k6_partfun1(sK0) ),
    inference(unflattening,[status(thm)],[c_658])).

cnf(c_4,plain,
    ( ~ v1_xboole_0(X0)
    | ~ v1_xboole_0(X1)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1881,plain,
    ( ~ v1_xboole_0(k6_partfun1(sK0))
    | ~ v1_xboole_0(sK2)
    | sK2 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1882,plain,
    ( sK2 = k6_partfun1(sK0)
    | v1_xboole_0(k6_partfun1(sK0)) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1881])).

cnf(c_1916,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(sK2) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_1917,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(sK2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1916])).

cnf(c_1919,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v1_xboole_0(sK2) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1917])).

cnf(c_1795,plain,
    ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_4920,plain,
    ( v1_xboole_0(X0) != iProver_top
    | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1795,c_1803])).

cnf(c_4925,plain,
    ( v1_xboole_0(k6_partfun1(sK0)) = iProver_top
    | v1_xboole_0(sK0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4920])).

cnf(c_5176,plain,
    ( v1_xboole_0(sK0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4922,c_65,c_98,c_659,c_1882,c_1919,c_4925])).

cnf(c_4773,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK1,X2,X3)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | v2_funct_1(X0)
    | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X3,X0,sK1))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1)
    | k1_xboole_0 = X3 ),
    inference(instantiation,[status(thm)],[c_43])).

cnf(c_5913,plain,
    ( ~ v1_funct_2(sK1,X0,X1)
    | ~ v1_funct_2(sK2,X2,X0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
    | ~ v2_funct_1(k1_partfun1(X2,X0,X0,X1,sK2,sK1))
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK1)
    | ~ v1_funct_1(sK2)
    | k1_xboole_0 = X1 ),
    inference(instantiation,[status(thm)],[c_4773])).

cnf(c_5914,plain,
    ( k1_xboole_0 = X0
    | v1_funct_2(sK1,X1,X0) != iProver_top
    | v1_funct_2(sK2,X2,X1) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
    | v2_funct_1(k1_partfun1(X2,X1,X1,X0,sK2,sK1)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5913])).

cnf(c_5916,plain,
    ( k1_xboole_0 = sK0
    | v1_funct_2(sK1,sK0,sK0) != iProver_top
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
    | v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) != iProver_top
    | v2_funct_1(sK2) = iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5914])).

cnf(c_1025,plain,
    ( ~ v2_funct_1(X0)
    | v2_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_4025,plain,
    ( v2_funct_1(X0)
    | ~ v2_funct_1(sK1)
    | X0 != sK1 ),
    inference(instantiation,[status(thm)],[c_1025])).

cnf(c_6264,plain,
    ( v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1))
    | ~ v2_funct_1(sK1)
    | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != sK1 ),
    inference(instantiation,[status(thm)],[c_4025])).

cnf(c_6279,plain,
    ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != sK1
    | v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) = iProver_top
    | v2_funct_1(sK1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6264])).

cnf(c_17105,plain,
    ( v2_funct_1(sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8055,c_59,c_60,c_61,c_57,c_62,c_56,c_63,c_64,c_54,c_65,c_67,c_98,c_197,c_201,c_203,c_659,c_667,c_1882,c_1888,c_1919,c_2033,c_2218,c_2292,c_2701,c_3856,c_4925,c_5916,c_6279])).

cnf(c_26,plain,
    ( ~ v2_funct_1(X0)
    | ~ v2_funct_1(X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f112])).

cnf(c_1804,plain,
    ( k5_relat_1(k2_funct_1(X0),k2_funct_1(X1)) = k2_funct_1(k5_relat_1(X1,X0))
    | v2_funct_1(X1) != iProver_top
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_8248,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK1))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(sK1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1785,c_1804])).

cnf(c_8450,plain,
    ( v1_relat_1(X0) != iProver_top
    | k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK1))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8248,c_60,c_185,c_3982])).

cnf(c_8451,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK1))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_8450])).

cnf(c_17109,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) = k2_funct_1(k5_relat_1(sK2,sK1))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17105,c_8451])).

cnf(c_17117,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK1)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17109,c_7957])).

cnf(c_27813,plain,
    ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17117,c_63,c_185,c_3981])).

cnf(c_21,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X0)
    | ~ v1_relat_1(X1)
    | k5_relat_1(X0,X1) != X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k6_partfun1(k1_relat_1(X1)) = X1 ),
    inference(cnf_transformation,[],[f153])).

cnf(c_1809,plain,
    ( k5_relat_1(X0,X1) != X0
    | k1_relat_1(X1) != k2_relat_1(X0)
    | k6_partfun1(k1_relat_1(X1)) = X1
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X0) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_27817,plain,
    ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1))
    | k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k2_funct_1(sK2)
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_27813,c_1809])).

cnf(c_17114,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17105,c_1807])).

cnf(c_24780,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17114,c_63,c_185,c_3981])).

cnf(c_27818,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k2_funct_1(sK2)
    | k2_relat_1(sK2) != sK0
    | v1_funct_1(k2_funct_1(sK1)) != iProver_top
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(k2_funct_1(sK1)) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27817,c_7074,c_24780])).

cnf(c_24,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
    inference(cnf_transformation,[],[f154])).

cnf(c_1806,plain,
    ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
    | v2_funct_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_17111,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17105,c_1806])).

cnf(c_27645,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_17111,c_63,c_185,c_3981])).

cnf(c_27647,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = sK2
    | k6_partfun1(k2_relat_1(sK2)) != k2_funct_1(sK2)
    | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_27645,c_1809])).

cnf(c_3973,plain,
    ( k1_relset_1(sK0,sK0,sK2) = sK0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1784,c_1786])).

cnf(c_3315,plain,
    ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
    inference(superposition,[status(thm)],[c_1784,c_1802])).

cnf(c_3976,plain,
    ( k1_relat_1(sK2) = sK0
    | v1_funct_2(sK2,sK0,sK0) != iProver_top
    | v1_funct_1(sK2) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3973,c_3315])).

cnf(c_7274,plain,
    ( k1_relat_1(sK2) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3976,c_63,c_64])).

cnf(c_17113,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_17105,c_1808])).

cnf(c_17115,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_17113,c_7274])).

cnf(c_23852,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17115,c_63,c_185,c_3981])).

cnf(c_27648,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k2_funct_1(sK2)
    | k6_partfun1(sK0) = sK2
    | sK0 != sK0
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_27647,c_7274,c_23852])).

cnf(c_27649,plain,
    ( k6_partfun1(k2_relat_1(sK2)) != k2_funct_1(sK2)
    | k6_partfun1(sK0) = sK2
    | v1_funct_1(k2_funct_1(sK2)) != iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_27648])).

cnf(c_6070,plain,
    ( ~ v1_funct_1(sK2)
    | v1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_6071,plain,
    ( v1_funct_1(sK2) != iProver_top
    | v1_relat_1(k2_funct_1(sK2)) = iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6070])).

cnf(c_6056,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_6057,plain,
    ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
    | v1_funct_1(sK2) != iProver_top
    | v1_relat_1(sK2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6056])).

cnf(c_1010,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2042,plain,
    ( sK2 = sK2 ),
    inference(instantiation,[status(thm)],[c_1010])).

cnf(c_1886,plain,
    ( k6_partfun1(sK0) != X0
    | sK2 != X0
    | sK2 = k6_partfun1(sK0) ),
    inference(instantiation,[status(thm)],[c_1011])).

cnf(c_1950,plain,
    ( k6_partfun1(sK0) != sK2
    | sK2 = k6_partfun1(sK0)
    | sK2 != sK2 ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_38414,c_27818,c_27649,c_6074,c_6071,c_6060,c_6057,c_3982,c_3981,c_2042,c_1950,c_659,c_185,c_98,c_63,c_60])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:20:22 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  % Running in FOF mode
% 11.65/2.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.65/2.03  
% 11.65/2.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.65/2.03  
% 11.65/2.03  ------  iProver source info
% 11.65/2.03  
% 11.65/2.03  git: date: 2020-06-30 10:37:57 +0100
% 11.65/2.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.65/2.03  git: non_committed_changes: false
% 11.65/2.03  git: last_make_outside_of_git: false
% 11.65/2.03  
% 11.65/2.03  ------ 
% 11.65/2.03  
% 11.65/2.03  ------ Input Options
% 11.65/2.03  
% 11.65/2.03  --out_options                           all
% 11.65/2.03  --tptp_safe_out                         true
% 11.65/2.03  --problem_path                          ""
% 11.65/2.03  --include_path                          ""
% 11.65/2.03  --clausifier                            res/vclausify_rel
% 11.65/2.03  --clausifier_options                    ""
% 11.65/2.03  --stdin                                 false
% 11.65/2.03  --stats_out                             all
% 11.65/2.03  
% 11.65/2.03  ------ General Options
% 11.65/2.03  
% 11.65/2.03  --fof                                   false
% 11.65/2.03  --time_out_real                         305.
% 11.65/2.03  --time_out_virtual                      -1.
% 11.65/2.03  --symbol_type_check                     false
% 11.65/2.03  --clausify_out                          false
% 11.65/2.03  --sig_cnt_out                           false
% 11.65/2.03  --trig_cnt_out                          false
% 11.65/2.03  --trig_cnt_out_tolerance                1.
% 11.65/2.03  --trig_cnt_out_sk_spl                   false
% 11.65/2.03  --abstr_cl_out                          false
% 11.65/2.03  
% 11.65/2.03  ------ Global Options
% 11.65/2.03  
% 11.65/2.03  --schedule                              default
% 11.65/2.03  --add_important_lit                     false
% 11.65/2.03  --prop_solver_per_cl                    1000
% 11.65/2.03  --min_unsat_core                        false
% 11.65/2.03  --soft_assumptions                      false
% 11.65/2.03  --soft_lemma_size                       3
% 11.65/2.03  --prop_impl_unit_size                   0
% 11.65/2.03  --prop_impl_unit                        []
% 11.65/2.03  --share_sel_clauses                     true
% 11.65/2.03  --reset_solvers                         false
% 11.65/2.03  --bc_imp_inh                            [conj_cone]
% 11.65/2.03  --conj_cone_tolerance                   3.
% 11.65/2.03  --extra_neg_conj                        none
% 11.65/2.03  --large_theory_mode                     true
% 11.65/2.03  --prolific_symb_bound                   200
% 11.65/2.03  --lt_threshold                          2000
% 11.65/2.03  --clause_weak_htbl                      true
% 11.65/2.03  --gc_record_bc_elim                     false
% 11.65/2.03  
% 11.65/2.03  ------ Preprocessing Options
% 11.65/2.03  
% 11.65/2.03  --preprocessing_flag                    true
% 11.65/2.03  --time_out_prep_mult                    0.1
% 11.65/2.03  --splitting_mode                        input
% 11.65/2.03  --splitting_grd                         true
% 11.65/2.03  --splitting_cvd                         false
% 11.65/2.03  --splitting_cvd_svl                     false
% 11.65/2.03  --splitting_nvd                         32
% 11.65/2.03  --sub_typing                            true
% 11.65/2.03  --prep_gs_sim                           true
% 11.65/2.03  --prep_unflatten                        true
% 11.65/2.03  --prep_res_sim                          true
% 11.65/2.03  --prep_upred                            true
% 11.65/2.03  --prep_sem_filter                       exhaustive
% 11.65/2.03  --prep_sem_filter_out                   false
% 11.65/2.03  --pred_elim                             true
% 11.65/2.03  --res_sim_input                         true
% 11.65/2.03  --eq_ax_congr_red                       true
% 11.65/2.03  --pure_diseq_elim                       true
% 11.65/2.03  --brand_transform                       false
% 11.65/2.03  --non_eq_to_eq                          false
% 11.65/2.03  --prep_def_merge                        true
% 11.65/2.03  --prep_def_merge_prop_impl              false
% 11.65/2.03  --prep_def_merge_mbd                    true
% 11.65/2.03  --prep_def_merge_tr_red                 false
% 11.65/2.03  --prep_def_merge_tr_cl                  false
% 11.65/2.03  --smt_preprocessing                     true
% 11.65/2.03  --smt_ac_axioms                         fast
% 11.65/2.03  --preprocessed_out                      false
% 11.65/2.03  --preprocessed_stats                    false
% 11.65/2.03  
% 11.65/2.03  ------ Abstraction refinement Options
% 11.65/2.03  
% 11.65/2.03  --abstr_ref                             []
% 11.65/2.03  --abstr_ref_prep                        false
% 11.65/2.03  --abstr_ref_until_sat                   false
% 11.65/2.03  --abstr_ref_sig_restrict                funpre
% 11.65/2.03  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/2.03  --abstr_ref_under                       []
% 11.65/2.03  
% 11.65/2.03  ------ SAT Options
% 11.65/2.03  
% 11.65/2.03  --sat_mode                              false
% 11.65/2.03  --sat_fm_restart_options                ""
% 11.65/2.03  --sat_gr_def                            false
% 11.65/2.03  --sat_epr_types                         true
% 11.65/2.03  --sat_non_cyclic_types                  false
% 11.65/2.03  --sat_finite_models                     false
% 11.65/2.03  --sat_fm_lemmas                         false
% 11.65/2.03  --sat_fm_prep                           false
% 11.65/2.03  --sat_fm_uc_incr                        true
% 11.65/2.03  --sat_out_model                         small
% 11.65/2.03  --sat_out_clauses                       false
% 11.65/2.03  
% 11.65/2.03  ------ QBF Options
% 11.65/2.03  
% 11.65/2.03  --qbf_mode                              false
% 11.65/2.03  --qbf_elim_univ                         false
% 11.65/2.03  --qbf_dom_inst                          none
% 11.65/2.03  --qbf_dom_pre_inst                      false
% 11.65/2.03  --qbf_sk_in                             false
% 11.65/2.03  --qbf_pred_elim                         true
% 11.65/2.03  --qbf_split                             512
% 11.65/2.03  
% 11.65/2.03  ------ BMC1 Options
% 11.65/2.03  
% 11.65/2.03  --bmc1_incremental                      false
% 11.65/2.03  --bmc1_axioms                           reachable_all
% 11.65/2.03  --bmc1_min_bound                        0
% 11.65/2.03  --bmc1_max_bound                        -1
% 11.65/2.03  --bmc1_max_bound_default                -1
% 11.65/2.03  --bmc1_symbol_reachability              true
% 11.65/2.03  --bmc1_property_lemmas                  false
% 11.65/2.03  --bmc1_k_induction                      false
% 11.65/2.03  --bmc1_non_equiv_states                 false
% 11.65/2.03  --bmc1_deadlock                         false
% 11.65/2.03  --bmc1_ucm                              false
% 11.65/2.03  --bmc1_add_unsat_core                   none
% 11.65/2.03  --bmc1_unsat_core_children              false
% 11.65/2.03  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/2.03  --bmc1_out_stat                         full
% 11.65/2.03  --bmc1_ground_init                      false
% 11.65/2.03  --bmc1_pre_inst_next_state              false
% 11.65/2.03  --bmc1_pre_inst_state                   false
% 11.65/2.03  --bmc1_pre_inst_reach_state             false
% 11.65/2.03  --bmc1_out_unsat_core                   false
% 11.65/2.03  --bmc1_aig_witness_out                  false
% 11.65/2.03  --bmc1_verbose                          false
% 11.65/2.03  --bmc1_dump_clauses_tptp                false
% 11.65/2.03  --bmc1_dump_unsat_core_tptp             false
% 11.65/2.03  --bmc1_dump_file                        -
% 11.65/2.03  --bmc1_ucm_expand_uc_limit              128
% 11.65/2.03  --bmc1_ucm_n_expand_iterations          6
% 11.65/2.03  --bmc1_ucm_extend_mode                  1
% 11.65/2.03  --bmc1_ucm_init_mode                    2
% 11.65/2.03  --bmc1_ucm_cone_mode                    none
% 11.65/2.03  --bmc1_ucm_reduced_relation_type        0
% 11.65/2.03  --bmc1_ucm_relax_model                  4
% 11.65/2.03  --bmc1_ucm_full_tr_after_sat            true
% 11.65/2.03  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/2.03  --bmc1_ucm_layered_model                none
% 11.65/2.03  --bmc1_ucm_max_lemma_size               10
% 11.65/2.03  
% 11.65/2.03  ------ AIG Options
% 11.65/2.03  
% 11.65/2.03  --aig_mode                              false
% 11.65/2.03  
% 11.65/2.03  ------ Instantiation Options
% 11.65/2.03  
% 11.65/2.03  --instantiation_flag                    true
% 11.65/2.03  --inst_sos_flag                         true
% 11.65/2.03  --inst_sos_phase                        true
% 11.65/2.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/2.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/2.03  --inst_lit_sel_side                     num_symb
% 11.65/2.03  --inst_solver_per_active                1400
% 11.65/2.03  --inst_solver_calls_frac                1.
% 11.65/2.03  --inst_passive_queue_type               priority_queues
% 11.65/2.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/2.03  --inst_passive_queues_freq              [25;2]
% 11.65/2.03  --inst_dismatching                      true
% 11.65/2.03  --inst_eager_unprocessed_to_passive     true
% 11.65/2.03  --inst_prop_sim_given                   true
% 11.65/2.03  --inst_prop_sim_new                     false
% 11.65/2.03  --inst_subs_new                         false
% 11.65/2.03  --inst_eq_res_simp                      false
% 11.65/2.03  --inst_subs_given                       false
% 11.65/2.03  --inst_orphan_elimination               true
% 11.65/2.03  --inst_learning_loop_flag               true
% 11.65/2.03  --inst_learning_start                   3000
% 11.65/2.03  --inst_learning_factor                  2
% 11.65/2.03  --inst_start_prop_sim_after_learn       3
% 11.65/2.03  --inst_sel_renew                        solver
% 11.65/2.03  --inst_lit_activity_flag                true
% 11.65/2.03  --inst_restr_to_given                   false
% 11.65/2.03  --inst_activity_threshold               500
% 11.65/2.03  --inst_out_proof                        true
% 11.65/2.03  
% 11.65/2.03  ------ Resolution Options
% 11.65/2.03  
% 11.65/2.03  --resolution_flag                       true
% 11.65/2.03  --res_lit_sel                           adaptive
% 11.65/2.03  --res_lit_sel_side                      none
% 11.65/2.03  --res_ordering                          kbo
% 11.65/2.03  --res_to_prop_solver                    active
% 11.65/2.03  --res_prop_simpl_new                    false
% 11.65/2.03  --res_prop_simpl_given                  true
% 11.65/2.03  --res_passive_queue_type                priority_queues
% 11.65/2.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/2.03  --res_passive_queues_freq               [15;5]
% 11.65/2.03  --res_forward_subs                      full
% 11.65/2.03  --res_backward_subs                     full
% 11.65/2.03  --res_forward_subs_resolution           true
% 11.65/2.03  --res_backward_subs_resolution          true
% 11.65/2.03  --res_orphan_elimination                true
% 11.65/2.03  --res_time_limit                        2.
% 11.65/2.03  --res_out_proof                         true
% 11.65/2.03  
% 11.65/2.03  ------ Superposition Options
% 11.65/2.03  
% 11.65/2.03  --superposition_flag                    true
% 11.65/2.03  --sup_passive_queue_type                priority_queues
% 11.65/2.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/2.03  --sup_passive_queues_freq               [8;1;4]
% 11.65/2.03  --demod_completeness_check              fast
% 11.65/2.03  --demod_use_ground                      true
% 11.65/2.03  --sup_to_prop_solver                    passive
% 11.65/2.03  --sup_prop_simpl_new                    true
% 11.65/2.03  --sup_prop_simpl_given                  true
% 11.65/2.03  --sup_fun_splitting                     true
% 11.65/2.03  --sup_smt_interval                      50000
% 11.65/2.03  
% 11.65/2.03  ------ Superposition Simplification Setup
% 11.65/2.03  
% 11.65/2.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.65/2.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.65/2.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.65/2.03  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/2.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.65/2.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.65/2.03  --sup_immed_triv                        [TrivRules]
% 11.65/2.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.03  --sup_immed_bw_main                     []
% 11.65/2.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.65/2.03  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/2.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.03  --sup_input_bw                          []
% 11.65/2.03  
% 11.65/2.03  ------ Combination Options
% 11.65/2.03  
% 11.65/2.03  --comb_res_mult                         3
% 11.65/2.03  --comb_sup_mult                         2
% 11.65/2.03  --comb_inst_mult                        10
% 11.65/2.03  
% 11.65/2.03  ------ Debug Options
% 11.65/2.03  
% 11.65/2.03  --dbg_backtrace                         false
% 11.65/2.03  --dbg_dump_prop_clauses                 false
% 11.65/2.03  --dbg_dump_prop_clauses_file            -
% 11.65/2.03  --dbg_out_stat                          false
% 11.65/2.03  ------ Parsing...
% 11.65/2.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.65/2.03  
% 11.65/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.65/2.03  
% 11.65/2.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.65/2.03  
% 11.65/2.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.65/2.03  ------ Proving...
% 11.65/2.03  ------ Problem Properties 
% 11.65/2.03  
% 11.65/2.03  
% 11.65/2.03  clauses                                 53
% 11.65/2.03  conjectures                             7
% 11.65/2.03  EPR                                     9
% 11.65/2.03  Horn                                    52
% 11.65/2.03  unary                                   18
% 11.65/2.03  binary                                  8
% 11.65/2.03  lits                                    156
% 11.65/2.03  lits eq                                 32
% 11.65/2.03  fd_pure                                 0
% 11.65/2.03  fd_pseudo                               0
% 11.65/2.03  fd_cond                                 1
% 11.65/2.03  fd_pseudo_cond                          2
% 11.65/2.03  AC symbols                              0
% 11.65/2.03  
% 11.65/2.03  ------ Schedule dynamic 5 is on 
% 11.65/2.03  
% 11.65/2.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.65/2.03  
% 11.65/2.03  
% 11.65/2.03  ------ 
% 11.65/2.03  Current options:
% 11.65/2.03  ------ 
% 11.65/2.03  
% 11.65/2.03  ------ Input Options
% 11.65/2.03  
% 11.65/2.03  --out_options                           all
% 11.65/2.03  --tptp_safe_out                         true
% 11.65/2.03  --problem_path                          ""
% 11.65/2.03  --include_path                          ""
% 11.65/2.03  --clausifier                            res/vclausify_rel
% 11.65/2.03  --clausifier_options                    ""
% 11.65/2.03  --stdin                                 false
% 11.65/2.03  --stats_out                             all
% 11.65/2.03  
% 11.65/2.03  ------ General Options
% 11.65/2.03  
% 11.65/2.03  --fof                                   false
% 11.65/2.03  --time_out_real                         305.
% 11.65/2.03  --time_out_virtual                      -1.
% 11.65/2.03  --symbol_type_check                     false
% 11.65/2.03  --clausify_out                          false
% 11.65/2.03  --sig_cnt_out                           false
% 11.65/2.03  --trig_cnt_out                          false
% 11.65/2.03  --trig_cnt_out_tolerance                1.
% 11.65/2.03  --trig_cnt_out_sk_spl                   false
% 11.65/2.03  --abstr_cl_out                          false
% 11.65/2.03  
% 11.65/2.03  ------ Global Options
% 11.65/2.03  
% 11.65/2.03  --schedule                              default
% 11.65/2.03  --add_important_lit                     false
% 11.65/2.03  --prop_solver_per_cl                    1000
% 11.65/2.03  --min_unsat_core                        false
% 11.65/2.03  --soft_assumptions                      false
% 11.65/2.03  --soft_lemma_size                       3
% 11.65/2.03  --prop_impl_unit_size                   0
% 11.65/2.03  --prop_impl_unit                        []
% 11.65/2.03  --share_sel_clauses                     true
% 11.65/2.03  --reset_solvers                         false
% 11.65/2.03  --bc_imp_inh                            [conj_cone]
% 11.65/2.03  --conj_cone_tolerance                   3.
% 11.65/2.03  --extra_neg_conj                        none
% 11.65/2.03  --large_theory_mode                     true
% 11.65/2.03  --prolific_symb_bound                   200
% 11.65/2.03  --lt_threshold                          2000
% 11.65/2.03  --clause_weak_htbl                      true
% 11.65/2.03  --gc_record_bc_elim                     false
% 11.65/2.03  
% 11.65/2.03  ------ Preprocessing Options
% 11.65/2.03  
% 11.65/2.03  --preprocessing_flag                    true
% 11.65/2.03  --time_out_prep_mult                    0.1
% 11.65/2.03  --splitting_mode                        input
% 11.65/2.03  --splitting_grd                         true
% 11.65/2.03  --splitting_cvd                         false
% 11.65/2.03  --splitting_cvd_svl                     false
% 11.65/2.03  --splitting_nvd                         32
% 11.65/2.03  --sub_typing                            true
% 11.65/2.03  --prep_gs_sim                           true
% 11.65/2.03  --prep_unflatten                        true
% 11.65/2.03  --prep_res_sim                          true
% 11.65/2.03  --prep_upred                            true
% 11.65/2.03  --prep_sem_filter                       exhaustive
% 11.65/2.03  --prep_sem_filter_out                   false
% 11.65/2.03  --pred_elim                             true
% 11.65/2.03  --res_sim_input                         true
% 11.65/2.03  --eq_ax_congr_red                       true
% 11.65/2.03  --pure_diseq_elim                       true
% 11.65/2.03  --brand_transform                       false
% 11.65/2.03  --non_eq_to_eq                          false
% 11.65/2.03  --prep_def_merge                        true
% 11.65/2.03  --prep_def_merge_prop_impl              false
% 11.65/2.03  --prep_def_merge_mbd                    true
% 11.65/2.03  --prep_def_merge_tr_red                 false
% 11.65/2.03  --prep_def_merge_tr_cl                  false
% 11.65/2.03  --smt_preprocessing                     true
% 11.65/2.03  --smt_ac_axioms                         fast
% 11.65/2.03  --preprocessed_out                      false
% 11.65/2.03  --preprocessed_stats                    false
% 11.65/2.03  
% 11.65/2.03  ------ Abstraction refinement Options
% 11.65/2.03  
% 11.65/2.03  --abstr_ref                             []
% 11.65/2.03  --abstr_ref_prep                        false
% 11.65/2.03  --abstr_ref_until_sat                   false
% 11.65/2.03  --abstr_ref_sig_restrict                funpre
% 11.65/2.03  --abstr_ref_af_restrict_to_split_sk     false
% 11.65/2.03  --abstr_ref_under                       []
% 11.65/2.03  
% 11.65/2.03  ------ SAT Options
% 11.65/2.03  
% 11.65/2.03  --sat_mode                              false
% 11.65/2.03  --sat_fm_restart_options                ""
% 11.65/2.03  --sat_gr_def                            false
% 11.65/2.03  --sat_epr_types                         true
% 11.65/2.03  --sat_non_cyclic_types                  false
% 11.65/2.03  --sat_finite_models                     false
% 11.65/2.03  --sat_fm_lemmas                         false
% 11.65/2.03  --sat_fm_prep                           false
% 11.65/2.03  --sat_fm_uc_incr                        true
% 11.65/2.03  --sat_out_model                         small
% 11.65/2.03  --sat_out_clauses                       false
% 11.65/2.03  
% 11.65/2.03  ------ QBF Options
% 11.65/2.03  
% 11.65/2.03  --qbf_mode                              false
% 11.65/2.03  --qbf_elim_univ                         false
% 11.65/2.03  --qbf_dom_inst                          none
% 11.65/2.03  --qbf_dom_pre_inst                      false
% 11.65/2.03  --qbf_sk_in                             false
% 11.65/2.03  --qbf_pred_elim                         true
% 11.65/2.03  --qbf_split                             512
% 11.65/2.03  
% 11.65/2.03  ------ BMC1 Options
% 11.65/2.03  
% 11.65/2.03  --bmc1_incremental                      false
% 11.65/2.03  --bmc1_axioms                           reachable_all
% 11.65/2.03  --bmc1_min_bound                        0
% 11.65/2.03  --bmc1_max_bound                        -1
% 11.65/2.03  --bmc1_max_bound_default                -1
% 11.65/2.03  --bmc1_symbol_reachability              true
% 11.65/2.03  --bmc1_property_lemmas                  false
% 11.65/2.03  --bmc1_k_induction                      false
% 11.65/2.03  --bmc1_non_equiv_states                 false
% 11.65/2.03  --bmc1_deadlock                         false
% 11.65/2.03  --bmc1_ucm                              false
% 11.65/2.03  --bmc1_add_unsat_core                   none
% 11.65/2.03  --bmc1_unsat_core_children              false
% 11.65/2.03  --bmc1_unsat_core_extrapolate_axioms    false
% 11.65/2.03  --bmc1_out_stat                         full
% 11.65/2.03  --bmc1_ground_init                      false
% 11.65/2.03  --bmc1_pre_inst_next_state              false
% 11.65/2.03  --bmc1_pre_inst_state                   false
% 11.65/2.03  --bmc1_pre_inst_reach_state             false
% 11.65/2.03  --bmc1_out_unsat_core                   false
% 11.65/2.03  --bmc1_aig_witness_out                  false
% 11.65/2.03  --bmc1_verbose                          false
% 11.65/2.03  --bmc1_dump_clauses_tptp                false
% 11.65/2.03  --bmc1_dump_unsat_core_tptp             false
% 11.65/2.03  --bmc1_dump_file                        -
% 11.65/2.03  --bmc1_ucm_expand_uc_limit              128
% 11.65/2.03  --bmc1_ucm_n_expand_iterations          6
% 11.65/2.03  --bmc1_ucm_extend_mode                  1
% 11.65/2.03  --bmc1_ucm_init_mode                    2
% 11.65/2.03  --bmc1_ucm_cone_mode                    none
% 11.65/2.03  --bmc1_ucm_reduced_relation_type        0
% 11.65/2.03  --bmc1_ucm_relax_model                  4
% 11.65/2.03  --bmc1_ucm_full_tr_after_sat            true
% 11.65/2.03  --bmc1_ucm_expand_neg_assumptions       false
% 11.65/2.03  --bmc1_ucm_layered_model                none
% 11.65/2.03  --bmc1_ucm_max_lemma_size               10
% 11.65/2.03  
% 11.65/2.03  ------ AIG Options
% 11.65/2.03  
% 11.65/2.03  --aig_mode                              false
% 11.65/2.03  
% 11.65/2.03  ------ Instantiation Options
% 11.65/2.03  
% 11.65/2.03  --instantiation_flag                    true
% 11.65/2.03  --inst_sos_flag                         true
% 11.65/2.03  --inst_sos_phase                        true
% 11.65/2.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.65/2.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.65/2.03  --inst_lit_sel_side                     none
% 11.65/2.03  --inst_solver_per_active                1400
% 11.65/2.03  --inst_solver_calls_frac                1.
% 11.65/2.03  --inst_passive_queue_type               priority_queues
% 11.65/2.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.65/2.03  --inst_passive_queues_freq              [25;2]
% 11.65/2.03  --inst_dismatching                      true
% 11.65/2.03  --inst_eager_unprocessed_to_passive     true
% 11.65/2.03  --inst_prop_sim_given                   true
% 11.65/2.03  --inst_prop_sim_new                     false
% 11.65/2.03  --inst_subs_new                         false
% 11.65/2.03  --inst_eq_res_simp                      false
% 11.65/2.03  --inst_subs_given                       false
% 11.65/2.03  --inst_orphan_elimination               true
% 11.65/2.03  --inst_learning_loop_flag               true
% 11.65/2.03  --inst_learning_start                   3000
% 11.65/2.03  --inst_learning_factor                  2
% 11.65/2.03  --inst_start_prop_sim_after_learn       3
% 11.65/2.03  --inst_sel_renew                        solver
% 11.65/2.03  --inst_lit_activity_flag                true
% 11.65/2.03  --inst_restr_to_given                   false
% 11.65/2.03  --inst_activity_threshold               500
% 11.65/2.03  --inst_out_proof                        true
% 11.65/2.03  
% 11.65/2.03  ------ Resolution Options
% 11.65/2.03  
% 11.65/2.03  --resolution_flag                       false
% 11.65/2.03  --res_lit_sel                           adaptive
% 11.65/2.03  --res_lit_sel_side                      none
% 11.65/2.03  --res_ordering                          kbo
% 11.65/2.03  --res_to_prop_solver                    active
% 11.65/2.03  --res_prop_simpl_new                    false
% 11.65/2.03  --res_prop_simpl_given                  true
% 11.65/2.03  --res_passive_queue_type                priority_queues
% 11.65/2.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.65/2.03  --res_passive_queues_freq               [15;5]
% 11.65/2.03  --res_forward_subs                      full
% 11.65/2.03  --res_backward_subs                     full
% 11.65/2.03  --res_forward_subs_resolution           true
% 11.65/2.03  --res_backward_subs_resolution          true
% 11.65/2.03  --res_orphan_elimination                true
% 11.65/2.03  --res_time_limit                        2.
% 11.65/2.03  --res_out_proof                         true
% 11.65/2.03  
% 11.65/2.03  ------ Superposition Options
% 11.65/2.03  
% 11.65/2.03  --superposition_flag                    true
% 11.65/2.03  --sup_passive_queue_type                priority_queues
% 11.65/2.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.65/2.03  --sup_passive_queues_freq               [8;1;4]
% 11.65/2.03  --demod_completeness_check              fast
% 11.65/2.03  --demod_use_ground                      true
% 11.65/2.03  --sup_to_prop_solver                    passive
% 11.65/2.03  --sup_prop_simpl_new                    true
% 11.65/2.03  --sup_prop_simpl_given                  true
% 11.65/2.03  --sup_fun_splitting                     true
% 11.65/2.03  --sup_smt_interval                      50000
% 11.65/2.03  
% 11.65/2.03  ------ Superposition Simplification Setup
% 11.65/2.03  
% 11.65/2.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 11.65/2.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 11.65/2.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 11.65/2.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 11.65/2.03  --sup_full_triv                         [TrivRules;PropSubs]
% 11.65/2.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 11.65/2.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 11.65/2.03  --sup_immed_triv                        [TrivRules]
% 11.65/2.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.03  --sup_immed_bw_main                     []
% 11.65/2.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 11.65/2.03  --sup_input_triv                        [Unflattening;TrivRules]
% 11.65/2.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 11.65/2.03  --sup_input_bw                          []
% 11.65/2.03  
% 11.65/2.03  ------ Combination Options
% 11.65/2.03  
% 11.65/2.03  --comb_res_mult                         3
% 11.65/2.03  --comb_sup_mult                         2
% 11.65/2.03  --comb_inst_mult                        10
% 11.65/2.03  
% 11.65/2.03  ------ Debug Options
% 11.65/2.03  
% 11.65/2.03  --dbg_backtrace                         false
% 11.65/2.03  --dbg_dump_prop_clauses                 false
% 11.65/2.03  --dbg_dump_prop_clauses_file            -
% 11.65/2.03  --dbg_out_stat                          false
% 11.65/2.03  
% 11.65/2.03  
% 11.65/2.03  
% 11.65/2.03  
% 11.65/2.03  ------ Proving...
% 11.65/2.03  
% 11.65/2.03  
% 11.65/2.03  % SZS status Theorem for theBenchmark.p
% 11.65/2.03  
% 11.65/2.03  % SZS output start CNFRefutation for theBenchmark.p
% 11.65/2.03  
% 11.65/2.03  fof(f35,conjecture,(
% 11.65/2.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f36,negated_conjecture,(
% 11.65/2.03    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => ((v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1)) => r2_relset_1(X0,X0,X2,k6_partfun1(X0)))))),
% 11.65/2.03    inference(negated_conjecture,[],[f35])).
% 11.65/2.03  
% 11.65/2.03  fof(f77,plain,(
% 11.65/2.03    ? [X0,X1] : (? [X2] : ((~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & (v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 11.65/2.03    inference(ennf_transformation,[],[f36])).
% 11.65/2.03  
% 11.65/2.03  fof(f78,plain,(
% 11.65/2.03    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 11.65/2.03    inference(flattening,[],[f77])).
% 11.65/2.03  
% 11.65/2.03  fof(f84,plain,(
% 11.65/2.03    ( ! [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) => (~r2_relset_1(X0,X0,sK2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,sK2,X1),X1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(sK2,X0,X0) & v1_funct_1(sK2))) )),
% 11.65/2.03    introduced(choice_axiom,[])).
% 11.65/2.03  
% 11.65/2.03  fof(f83,plain,(
% 11.65/2.03    ? [X0,X1] : (? [X2] : (~r2_relset_1(X0,X0,X2,k6_partfun1(X0)) & v2_funct_1(X1) & r2_relset_1(X0,X0,k1_partfun1(X0,X0,X0,X0,X2,X1),X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X2,X0,X0) & v1_funct_1(X2)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (? [X2] : (~r2_relset_1(sK0,sK0,X2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,X2,sK1),sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(X2,sK0,sK0) & v1_funct_1(X2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1))),
% 11.65/2.03    introduced(choice_axiom,[])).
% 11.65/2.03  
% 11.65/2.03  fof(f85,plain,(
% 11.65/2.03    (~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) & v2_funct_1(sK1) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK2,sK0,sK0) & v1_funct_1(sK2)) & m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) & v1_funct_2(sK1,sK0,sK0) & v1_funct_1(sK1)),
% 11.65/2.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f78,f84,f83])).
% 11.65/2.03  
% 11.65/2.03  fof(f143,plain,(
% 11.65/2.03    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 11.65/2.03    inference(cnf_transformation,[],[f85])).
% 11.65/2.03  
% 11.65/2.03  fof(f20,axiom,(
% 11.65/2.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f57,plain,(
% 11.65/2.03    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.03    inference(ennf_transformation,[],[f20])).
% 11.65/2.03  
% 11.65/2.03  fof(f115,plain,(
% 11.65/2.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.03    inference(cnf_transformation,[],[f57])).
% 11.65/2.03  
% 11.65/2.03  fof(f5,axiom,(
% 11.65/2.03    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f40,plain,(
% 11.65/2.03    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 11.65/2.03    inference(ennf_transformation,[],[f5])).
% 11.65/2.03  
% 11.65/2.03  fof(f81,plain,(
% 11.65/2.03    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 11.65/2.03    inference(nnf_transformation,[],[f40])).
% 11.65/2.03  
% 11.65/2.03  fof(f92,plain,(
% 11.65/2.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f81])).
% 11.65/2.03  
% 11.65/2.03  fof(f140,plain,(
% 11.65/2.03    m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 11.65/2.03    inference(cnf_transformation,[],[f85])).
% 11.65/2.03  
% 11.65/2.03  fof(f34,axiom,(
% 11.65/2.03    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => k1_relset_1(X0,X0,X1) = X0)),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f75,plain,(
% 11.65/2.03    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)))),
% 11.65/2.03    inference(ennf_transformation,[],[f34])).
% 11.65/2.03  
% 11.65/2.03  fof(f76,plain,(
% 11.65/2.03    ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1))),
% 11.65/2.03    inference(flattening,[],[f75])).
% 11.65/2.03  
% 11.65/2.03  fof(f137,plain,(
% 11.65/2.03    ( ! [X0,X1] : (k1_relset_1(X0,X0,X1) = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) | ~v1_funct_2(X1,X0,X0) | ~v1_funct_1(X1)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f76])).
% 11.65/2.03  
% 11.65/2.03  fof(f22,axiom,(
% 11.65/2.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f59,plain,(
% 11.65/2.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.03    inference(ennf_transformation,[],[f22])).
% 11.65/2.03  
% 11.65/2.03  fof(f117,plain,(
% 11.65/2.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.03    inference(cnf_transformation,[],[f59])).
% 11.65/2.03  
% 11.65/2.03  fof(f138,plain,(
% 11.65/2.03    v1_funct_1(sK1)),
% 11.65/2.03    inference(cnf_transformation,[],[f85])).
% 11.65/2.03  
% 11.65/2.03  fof(f139,plain,(
% 11.65/2.03    v1_funct_2(sK1,sK0,sK0)),
% 11.65/2.03    inference(cnf_transformation,[],[f85])).
% 11.65/2.03  
% 11.65/2.03  fof(f14,axiom,(
% 11.65/2.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((r1_tarski(X1,k1_relat_1(X0)) & v2_funct_1(X0)) => k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f47,plain,(
% 11.65/2.03    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | (~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.65/2.03    inference(ennf_transformation,[],[f14])).
% 11.65/2.03  
% 11.65/2.03  fof(f48,plain,(
% 11.65/2.03    ! [X0] : (! [X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.65/2.03    inference(flattening,[],[f47])).
% 11.65/2.03  
% 11.65/2.03  fof(f106,plain,(
% 11.65/2.03    ( ! [X0,X1] : (k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1 | ~r1_tarski(X1,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f48])).
% 11.65/2.03  
% 11.65/2.03  fof(f145,plain,(
% 11.65/2.03    v2_funct_1(sK1)),
% 11.65/2.03    inference(cnf_transformation,[],[f85])).
% 11.65/2.03  
% 11.65/2.03  fof(f6,axiom,(
% 11.65/2.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f94,plain,(
% 11.65/2.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 11.65/2.03    inference(cnf_transformation,[],[f6])).
% 11.65/2.03  
% 11.65/2.03  fof(f4,axiom,(
% 11.65/2.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f39,plain,(
% 11.65/2.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 11.65/2.03    inference(ennf_transformation,[],[f4])).
% 11.65/2.03  
% 11.65/2.03  fof(f91,plain,(
% 11.65/2.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f39])).
% 11.65/2.03  
% 11.65/2.03  fof(f29,axiom,(
% 11.65/2.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f67,plain,(
% 11.65/2.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.65/2.03    inference(ennf_transformation,[],[f29])).
% 11.65/2.03  
% 11.65/2.03  fof(f68,plain,(
% 11.65/2.03    ! [X0,X1,X2,X3,X4,X5] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.65/2.03    inference(flattening,[],[f67])).
% 11.65/2.03  
% 11.65/2.03  fof(f127,plain,(
% 11.65/2.03    ( ! [X4,X2,X0,X5,X3,X1] : (k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f68])).
% 11.65/2.03  
% 11.65/2.03  fof(f25,axiom,(
% 11.65/2.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f62,plain,(
% 11.65/2.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 11.65/2.03    inference(ennf_transformation,[],[f25])).
% 11.65/2.03  
% 11.65/2.03  fof(f63,plain,(
% 11.65/2.03    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.03    inference(flattening,[],[f62])).
% 11.65/2.03  
% 11.65/2.03  fof(f82,plain,(
% 11.65/2.03    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.03    inference(nnf_transformation,[],[f63])).
% 11.65/2.03  
% 11.65/2.03  fof(f120,plain,(
% 11.65/2.03    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.03    inference(cnf_transformation,[],[f82])).
% 11.65/2.03  
% 11.65/2.03  fof(f144,plain,(
% 11.65/2.03    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1)),
% 11.65/2.03    inference(cnf_transformation,[],[f85])).
% 11.65/2.03  
% 11.65/2.03  fof(f141,plain,(
% 11.65/2.03    v1_funct_1(sK2)),
% 11.65/2.03    inference(cnf_transformation,[],[f85])).
% 11.65/2.03  
% 11.65/2.03  fof(f27,axiom,(
% 11.65/2.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f65,plain,(
% 11.65/2.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 11.65/2.03    inference(ennf_transformation,[],[f27])).
% 11.65/2.03  
% 11.65/2.03  fof(f66,plain,(
% 11.65/2.03    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 11.65/2.03    inference(flattening,[],[f65])).
% 11.65/2.03  
% 11.65/2.03  fof(f125,plain,(
% 11.65/2.03    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f66])).
% 11.65/2.03  
% 11.65/2.03  fof(f8,axiom,(
% 11.65/2.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0))))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f42,plain,(
% 11.65/2.03    ! [X0] : (! [X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 11.65/2.03    inference(ennf_transformation,[],[f8])).
% 11.65/2.03  
% 11.65/2.03  fof(f96,plain,(
% 11.65/2.03    ( ! [X0,X1] : (k2_relat_1(k5_relat_1(X0,X1)) = k9_relat_1(X1,k2_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f42])).
% 11.65/2.03  
% 11.65/2.03  fof(f16,axiom,(
% 11.65/2.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f51,plain,(
% 11.65/2.03    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.65/2.03    inference(ennf_transformation,[],[f16])).
% 11.65/2.03  
% 11.65/2.03  fof(f52,plain,(
% 11.65/2.03    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.65/2.03    inference(flattening,[],[f51])).
% 11.65/2.03  
% 11.65/2.03  fof(f109,plain,(
% 11.65/2.03    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f52])).
% 11.65/2.03  
% 11.65/2.03  fof(f33,axiom,(
% 11.65/2.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f73,plain,(
% 11.65/2.03    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.65/2.03    inference(ennf_transformation,[],[f33])).
% 11.65/2.03  
% 11.65/2.03  fof(f74,plain,(
% 11.65/2.03    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.65/2.03    inference(flattening,[],[f73])).
% 11.65/2.03  
% 11.65/2.03  fof(f136,plain,(
% 11.65/2.03    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f74])).
% 11.65/2.03  
% 11.65/2.03  fof(f108,plain,(
% 11.65/2.03    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f52])).
% 11.65/2.03  
% 11.65/2.03  fof(f11,axiom,(
% 11.65/2.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f45,plain,(
% 11.65/2.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.65/2.03    inference(ennf_transformation,[],[f11])).
% 11.65/2.03  
% 11.65/2.03  fof(f46,plain,(
% 11.65/2.03    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.65/2.03    inference(flattening,[],[f45])).
% 11.65/2.03  
% 11.65/2.03  fof(f101,plain,(
% 11.65/2.03    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f46])).
% 11.65/2.03  
% 11.65/2.03  fof(f100,plain,(
% 11.65/2.03    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f46])).
% 11.65/2.03  
% 11.65/2.03  fof(f26,axiom,(
% 11.65/2.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f64,plain,(
% 11.65/2.03    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.03    inference(ennf_transformation,[],[f26])).
% 11.65/2.03  
% 11.65/2.03  fof(f122,plain,(
% 11.65/2.03    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.03    inference(cnf_transformation,[],[f64])).
% 11.65/2.03  
% 11.65/2.03  fof(f24,axiom,(
% 11.65/2.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f61,plain,(
% 11.65/2.03    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.03    inference(ennf_transformation,[],[f24])).
% 11.65/2.03  
% 11.65/2.03  fof(f119,plain,(
% 11.65/2.03    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.03    inference(cnf_transformation,[],[f61])).
% 11.65/2.03  
% 11.65/2.03  fof(f23,axiom,(
% 11.65/2.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f60,plain,(
% 11.65/2.03    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 11.65/2.03    inference(ennf_transformation,[],[f23])).
% 11.65/2.03  
% 11.65/2.03  fof(f118,plain,(
% 11.65/2.03    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.03    inference(cnf_transformation,[],[f60])).
% 11.65/2.03  
% 11.65/2.03  fof(f31,axiom,(
% 11.65/2.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f69,plain,(
% 11.65/2.03    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 11.65/2.03    inference(ennf_transformation,[],[f31])).
% 11.65/2.03  
% 11.65/2.03  fof(f70,plain,(
% 11.65/2.03    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 11.65/2.03    inference(flattening,[],[f69])).
% 11.65/2.03  
% 11.65/2.03  fof(f129,plain,(
% 11.65/2.03    ( ! [X4,X2,X0,X3,X1] : (v2_funct_1(X3) | k1_xboole_0 = X2 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f70])).
% 11.65/2.03  
% 11.65/2.03  fof(f142,plain,(
% 11.65/2.03    v1_funct_2(sK2,sK0,sK0)),
% 11.65/2.03    inference(cnf_transformation,[],[f85])).
% 11.65/2.03  
% 11.65/2.03  fof(f2,axiom,(
% 11.65/2.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f79,plain,(
% 11.65/2.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.65/2.03    inference(nnf_transformation,[],[f2])).
% 11.65/2.03  
% 11.65/2.03  fof(f80,plain,(
% 11.65/2.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 11.65/2.03    inference(flattening,[],[f79])).
% 11.65/2.03  
% 11.65/2.03  fof(f87,plain,(
% 11.65/2.03    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 11.65/2.03    inference(cnf_transformation,[],[f80])).
% 11.65/2.03  
% 11.65/2.03  fof(f158,plain,(
% 11.65/2.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 11.65/2.03    inference(equality_resolution,[],[f87])).
% 11.65/2.03  
% 11.65/2.03  fof(f89,plain,(
% 11.65/2.03    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f80])).
% 11.65/2.03  
% 11.65/2.03  fof(f1,axiom,(
% 11.65/2.03    v1_xboole_0(k1_xboole_0)),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f86,plain,(
% 11.65/2.03    v1_xboole_0(k1_xboole_0)),
% 11.65/2.03    inference(cnf_transformation,[],[f1])).
% 11.65/2.03  
% 11.65/2.03  fof(f21,axiom,(
% 11.65/2.03    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f58,plain,(
% 11.65/2.03    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 11.65/2.03    inference(ennf_transformation,[],[f21])).
% 11.65/2.03  
% 11.65/2.03  fof(f116,plain,(
% 11.65/2.03    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f58])).
% 11.65/2.03  
% 11.65/2.03  fof(f28,axiom,(
% 11.65/2.03    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f37,plain,(
% 11.65/2.03    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 11.65/2.03    inference(pure_predicate_removal,[],[f28])).
% 11.65/2.03  
% 11.65/2.03  fof(f126,plain,(
% 11.65/2.03    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 11.65/2.03    inference(cnf_transformation,[],[f37])).
% 11.65/2.03  
% 11.65/2.03  fof(f121,plain,(
% 11.65/2.03    ( ! [X2,X0,X3,X1] : (r2_relset_1(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.03    inference(cnf_transformation,[],[f82])).
% 11.65/2.03  
% 11.65/2.03  fof(f159,plain,(
% 11.65/2.03    ( ! [X0,X3,X1] : (r2_relset_1(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 11.65/2.03    inference(equality_resolution,[],[f121])).
% 11.65/2.03  
% 11.65/2.03  fof(f146,plain,(
% 11.65/2.03    ~r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0))),
% 11.65/2.03    inference(cnf_transformation,[],[f85])).
% 11.65/2.03  
% 11.65/2.03  fof(f3,axiom,(
% 11.65/2.03    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f38,plain,(
% 11.65/2.03    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 11.65/2.03    inference(ennf_transformation,[],[f3])).
% 11.65/2.03  
% 11.65/2.03  fof(f90,plain,(
% 11.65/2.03    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f38])).
% 11.65/2.03  
% 11.65/2.03  fof(f18,axiom,(
% 11.65/2.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((v2_funct_1(X1) & v2_funct_1(X0)) => k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)))))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f55,plain,(
% 11.65/2.03    ! [X0] : (! [X1] : ((k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | (~v2_funct_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.65/2.03    inference(ennf_transformation,[],[f18])).
% 11.65/2.03  
% 11.65/2.03  fof(f56,plain,(
% 11.65/2.03    ! [X0] : (! [X1] : (k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.65/2.03    inference(flattening,[],[f55])).
% 11.65/2.03  
% 11.65/2.03  fof(f112,plain,(
% 11.65/2.03    ( ! [X0,X1] : (k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) | ~v2_funct_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f56])).
% 11.65/2.03  
% 11.65/2.03  fof(f15,axiom,(
% 11.65/2.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = X0 & k2_relat_1(X0) = k1_relat_1(X1)) => k6_relat_1(k1_relat_1(X1)) = X1)))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f49,plain,(
% 11.65/2.03    ! [X0] : (! [X1] : ((k6_relat_1(k1_relat_1(X1)) = X1 | (k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.65/2.03    inference(ennf_transformation,[],[f15])).
% 11.65/2.03  
% 11.65/2.03  fof(f50,plain,(
% 11.65/2.03    ! [X0] : (! [X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.65/2.03    inference(flattening,[],[f49])).
% 11.65/2.03  
% 11.65/2.03  fof(f107,plain,(
% 11.65/2.03    ( ! [X0,X1] : (k6_relat_1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f50])).
% 11.65/2.03  
% 11.65/2.03  fof(f30,axiom,(
% 11.65/2.03    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f128,plain,(
% 11.65/2.03    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f30])).
% 11.65/2.03  
% 11.65/2.03  fof(f153,plain,(
% 11.65/2.03    ( ! [X0,X1] : (k6_partfun1(k1_relat_1(X1)) = X1 | k5_relat_1(X0,X1) != X0 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(definition_unfolding,[],[f107,f128])).
% 11.65/2.03  
% 11.65/2.03  fof(f17,axiom,(
% 11.65/2.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 11.65/2.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.65/2.03  
% 11.65/2.03  fof(f53,plain,(
% 11.65/2.03    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 11.65/2.03    inference(ennf_transformation,[],[f17])).
% 11.65/2.03  
% 11.65/2.03  fof(f54,plain,(
% 11.65/2.03    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 11.65/2.03    inference(flattening,[],[f53])).
% 11.65/2.03  
% 11.65/2.03  fof(f111,plain,(
% 11.65/2.03    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(cnf_transformation,[],[f54])).
% 11.65/2.03  
% 11.65/2.03  fof(f154,plain,(
% 11.65/2.03    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 11.65/2.03    inference(definition_unfolding,[],[f111,f128])).
% 11.65/2.03  
% 11.65/2.03  cnf(c_54,negated_conjecture,
% 11.65/2.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.65/2.03      inference(cnf_transformation,[],[f143]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1784,plain,
% 11.65/2.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_28,plain,
% 11.65/2.03      ( v5_relat_1(X0,X1)
% 11.65/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 11.65/2.03      inference(cnf_transformation,[],[f115]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7,plain,
% 11.65/2.03      ( ~ v5_relat_1(X0,X1)
% 11.65/2.03      | r1_tarski(k2_relat_1(X0),X1)
% 11.65/2.03      | ~ v1_relat_1(X0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f92]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_637,plain,
% 11.65/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | r1_tarski(k2_relat_1(X0),X2)
% 11.65/2.03      | ~ v1_relat_1(X0) ),
% 11.65/2.03      inference(resolution,[status(thm)],[c_28,c_7]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1777,plain,
% 11.65/2.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.65/2.03      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 11.65/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_637]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_2719,plain,
% 11.65/2.03      ( r1_tarski(k2_relat_1(sK2),sK0) = iProver_top
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1784,c_1777]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_57,negated_conjecture,
% 11.65/2.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.65/2.03      inference(cnf_transformation,[],[f140]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1781,plain,
% 11.65/2.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_50,plain,
% 11.65/2.03      ( ~ v1_funct_2(X0,X1,X1)
% 11.65/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X1)))
% 11.65/2.03      | ~ v1_funct_1(X0)
% 11.65/2.03      | k1_relset_1(X1,X1,X0) = X1 ),
% 11.65/2.03      inference(cnf_transformation,[],[f137]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1786,plain,
% 11.65/2.03      ( k1_relset_1(X0,X0,X1) = X0
% 11.65/2.03      | v1_funct_2(X1,X0,X0) != iProver_top
% 11.65/2.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) != iProver_top
% 11.65/2.03      | v1_funct_1(X1) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_50]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_3974,plain,
% 11.65/2.03      ( k1_relset_1(sK0,sK0,sK1) = sK0
% 11.65/2.03      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 11.65/2.03      | v1_funct_1(sK1) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1781,c_1786]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_31,plain,
% 11.65/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f117]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1802,plain,
% 11.65/2.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 11.65/2.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_3316,plain,
% 11.65/2.03      ( k1_relset_1(sK0,sK0,sK1) = k1_relat_1(sK1) ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1781,c_1802]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_3975,plain,
% 11.65/2.03      ( k1_relat_1(sK1) = sK0
% 11.65/2.03      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 11.65/2.03      | v1_funct_1(sK1) != iProver_top ),
% 11.65/2.03      inference(demodulation,[status(thm)],[c_3974,c_3316]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_59,negated_conjecture,
% 11.65/2.03      ( v1_funct_1(sK1) ),
% 11.65/2.03      inference(cnf_transformation,[],[f138]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_60,plain,
% 11.65/2.03      ( v1_funct_1(sK1) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_59]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_58,negated_conjecture,
% 11.65/2.03      ( v1_funct_2(sK1,sK0,sK0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f139]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_61,plain,
% 11.65/2.03      ( v1_funct_2(sK1,sK0,sK0) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_58]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7071,plain,
% 11.65/2.03      ( k1_relat_1(sK1) = sK0 ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_3975,c_60,c_61]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_20,plain,
% 11.65/2.03      ( ~ r1_tarski(X0,k1_relat_1(X1))
% 11.65/2.03      | ~ v2_funct_1(X1)
% 11.65/2.03      | ~ v1_funct_1(X1)
% 11.65/2.03      | ~ v1_relat_1(X1)
% 11.65/2.03      | k9_relat_1(k2_funct_1(X1),k9_relat_1(X1,X0)) = X0 ),
% 11.65/2.03      inference(cnf_transformation,[],[f106]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1810,plain,
% 11.65/2.03      ( k9_relat_1(k2_funct_1(X0),k9_relat_1(X0,X1)) = X1
% 11.65/2.03      | r1_tarski(X1,k1_relat_1(X0)) != iProver_top
% 11.65/2.03      | v2_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7077,plain,
% 11.65/2.03      ( k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0
% 11.65/2.03      | r1_tarski(X0,sK0) != iProver_top
% 11.65/2.03      | v2_funct_1(sK1) != iProver_top
% 11.65/2.03      | v1_funct_1(sK1) != iProver_top
% 11.65/2.03      | v1_relat_1(sK1) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_7071,c_1810]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_52,negated_conjecture,
% 11.65/2.03      ( v2_funct_1(sK1) ),
% 11.65/2.03      inference(cnf_transformation,[],[f145]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_67,plain,
% 11.65/2.03      ( v2_funct_1(sK1) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_8,plain,
% 11.65/2.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 11.65/2.03      inference(cnf_transformation,[],[f94]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_183,plain,
% 11.65/2.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_185,plain,
% 11.65/2.03      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) = iProver_top ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_183]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_5,plain,
% 11.65/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 11.65/2.03      | ~ v1_relat_1(X1)
% 11.65/2.03      | v1_relat_1(X0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f91]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1819,plain,
% 11.65/2.03      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 11.65/2.03      | v1_relat_1(X1) != iProver_top
% 11.65/2.03      | v1_relat_1(X0) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_3982,plain,
% 11.65/2.03      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 11.65/2.03      | v1_relat_1(sK1) = iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1781,c_1819]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_38398,plain,
% 11.65/2.03      ( r1_tarski(X0,sK0) != iProver_top
% 11.65/2.03      | k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0 ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_7077,c_60,c_67,c_185,c_3982]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_38399,plain,
% 11.65/2.03      ( k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,X0)) = X0
% 11.65/2.03      | r1_tarski(X0,sK0) != iProver_top ),
% 11.65/2.03      inference(renaming,[status(thm)],[c_38398]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_38405,plain,
% 11.65/2.03      ( k9_relat_1(k2_funct_1(sK1),k9_relat_1(sK1,k2_relat_1(sK2))) = k2_relat_1(sK2)
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_2719,c_38399]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_41,plain,
% 11.65/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.65/2.03      | ~ v1_funct_1(X0)
% 11.65/2.03      | ~ v1_funct_1(X3)
% 11.65/2.03      | k1_partfun1(X4,X5,X1,X2,X3,X0) = k5_relat_1(X3,X0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f127]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1794,plain,
% 11.65/2.03      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
% 11.65/2.03      | m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.65/2.03      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.03      | v1_funct_1(X5) != iProver_top
% 11.65/2.03      | v1_funct_1(X4) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7462,plain,
% 11.65/2.03      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 11.65/2.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.03      | v1_funct_1(X2) != iProver_top
% 11.65/2.03      | v1_funct_1(sK1) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1781,c_1794]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7744,plain,
% 11.65/2.03      ( v1_funct_1(X2) != iProver_top
% 11.65/2.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.03      | k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1) ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_7462,c_60]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7745,plain,
% 11.65/2.03      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK1) = k5_relat_1(X2,sK1)
% 11.65/2.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.03      | v1_funct_1(X2) != iProver_top ),
% 11.65/2.03      inference(renaming,[status(thm)],[c_7744]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7752,plain,
% 11.65/2.03      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k5_relat_1(sK2,sK1)
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1784,c_7745]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_35,plain,
% 11.65/2.03      ( ~ r2_relset_1(X0,X1,X2,X3)
% 11.65/2.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.65/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.65/2.03      | X3 = X2 ),
% 11.65/2.03      inference(cnf_transformation,[],[f120]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_53,negated_conjecture,
% 11.65/2.03      ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),sK1) ),
% 11.65/2.03      inference(cnf_transformation,[],[f144]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_666,plain,
% 11.65/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | X3 = X0
% 11.65/2.03      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != X0
% 11.65/2.03      | sK1 != X3
% 11.65/2.03      | sK0 != X2
% 11.65/2.03      | sK0 != X1 ),
% 11.65/2.03      inference(resolution_lifted,[status(thm)],[c_35,c_53]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_667,plain,
% 11.65/2.03      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.03      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 11.65/2.03      inference(unflattening,[status(thm)],[c_666]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_669,plain,
% 11.65/2.03      ( ~ m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.03      | sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_667,c_57]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1776,plain,
% 11.65/2.03      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 11.65/2.03      | m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_669]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_56,negated_conjecture,
% 11.65/2.03      ( v1_funct_1(sK2) ),
% 11.65/2.03      inference(cnf_transformation,[],[f141]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_38,plain,
% 11.65/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.65/2.03      | m1_subset_1(k1_partfun1(X4,X5,X1,X2,X3,X0),k1_zfmisc_1(k2_zfmisc_1(X4,X2)))
% 11.65/2.03      | ~ v1_funct_1(X0)
% 11.65/2.03      | ~ v1_funct_1(X3) ),
% 11.65/2.03      inference(cnf_transformation,[],[f125]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1888,plain,
% 11.65/2.03      ( m1_subset_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.03      | ~ v1_funct_1(sK1)
% 11.65/2.03      | ~ v1_funct_1(sK2) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_38]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_2449,plain,
% 11.65/2.03      ( sK1 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_1776,c_59,c_57,c_56,c_54,c_667,c_1888]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7754,plain,
% 11.65/2.03      ( k5_relat_1(sK2,sK1) = sK1 | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.03      inference(light_normalisation,[status(thm)],[c_7752,c_2449]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_63,plain,
% 11.65/2.03      ( v1_funct_1(sK2) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_56]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7957,plain,
% 11.65/2.03      ( k5_relat_1(sK2,sK1) = sK1 ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_7754,c_63]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_3981,plain,
% 11.65/2.03      ( v1_relat_1(k2_zfmisc_1(sK0,sK0)) != iProver_top
% 11.65/2.03      | v1_relat_1(sK2) = iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1784,c_1819]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_4324,plain,
% 11.65/2.03      ( v1_relat_1(sK2) = iProver_top ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_3981,c_185]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_4499,plain,
% 11.65/2.03      ( v1_relat_1(sK1) = iProver_top ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_3982,c_185]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_10,plain,
% 11.65/2.03      ( ~ v1_relat_1(X0)
% 11.65/2.03      | ~ v1_relat_1(X1)
% 11.65/2.03      | k9_relat_1(X1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,X1)) ),
% 11.65/2.03      inference(cnf_transformation,[],[f96]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1816,plain,
% 11.65/2.03      ( k9_relat_1(X0,k2_relat_1(X1)) = k2_relat_1(k5_relat_1(X1,X0))
% 11.65/2.03      | v1_relat_1(X1) != iProver_top
% 11.65/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_5016,plain,
% 11.65/2.03      ( k9_relat_1(sK1,k2_relat_1(X0)) = k2_relat_1(k5_relat_1(X0,sK1))
% 11.65/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_4499,c_1816]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6552,plain,
% 11.65/2.03      ( k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(k5_relat_1(sK2,sK1)) ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_4324,c_5016]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7959,plain,
% 11.65/2.03      ( k9_relat_1(sK1,k2_relat_1(sK2)) = k2_relat_1(sK1) ),
% 11.65/2.03      inference(demodulation,[status(thm)],[c_7957,c_6552]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1785,plain,
% 11.65/2.03      ( v2_funct_1(sK1) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_22,plain,
% 11.65/2.03      ( ~ v2_funct_1(X0)
% 11.65/2.03      | ~ v1_funct_1(X0)
% 11.65/2.03      | ~ v1_relat_1(X0)
% 11.65/2.03      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f109]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1808,plain,
% 11.65/2.03      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 11.65/2.03      | v2_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_5952,plain,
% 11.65/2.03      ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1)
% 11.65/2.03      | v1_funct_1(sK1) != iProver_top
% 11.65/2.03      | v1_relat_1(sK1) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1785,c_1808]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6207,plain,
% 11.65/2.03      ( k2_relat_1(k2_funct_1(sK1)) = k1_relat_1(sK1) ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_5952,c_60,c_185,c_3982]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7074,plain,
% 11.65/2.03      ( k2_relat_1(k2_funct_1(sK1)) = sK0 ),
% 11.65/2.03      inference(demodulation,[status(thm)],[c_7071,c_6207]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_47,plain,
% 11.65/2.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 11.65/2.03      | ~ v1_funct_1(X0)
% 11.65/2.03      | ~ v1_relat_1(X0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f136]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1788,plain,
% 11.65/2.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 11.65/2.03      | v1_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_47]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7085,plain,
% 11.65/2.03      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(k2_funct_1(sK1)),sK0))) = iProver_top
% 11.65/2.03      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_7074,c_1788]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_23,plain,
% 11.65/2.03      ( ~ v2_funct_1(X0)
% 11.65/2.03      | ~ v1_funct_1(X0)
% 11.65/2.03      | ~ v1_relat_1(X0)
% 11.65/2.03      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f108]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1807,plain,
% 11.65/2.03      ( k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 11.65/2.03      | v2_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_5947,plain,
% 11.65/2.03      ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1)
% 11.65/2.03      | v1_funct_1(sK1) != iProver_top
% 11.65/2.03      | v1_relat_1(sK1) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1785,c_1807]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6200,plain,
% 11.65/2.03      ( k1_relat_1(k2_funct_1(sK1)) = k2_relat_1(sK1) ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_5947,c_60,c_185,c_3982]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7088,plain,
% 11.65/2.03      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK1),sK0))) = iProver_top
% 11.65/2.03      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK1)) != iProver_top ),
% 11.65/2.03      inference(light_normalisation,[status(thm)],[c_7085,c_6200]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_14,plain,
% 11.65/2.03      ( ~ v1_funct_1(X0)
% 11.65/2.03      | v1_funct_1(k2_funct_1(X0))
% 11.65/2.03      | ~ v1_relat_1(X0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f101]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6059,plain,
% 11.65/2.03      ( v1_funct_1(k2_funct_1(sK1))
% 11.65/2.03      | ~ v1_funct_1(sK1)
% 11.65/2.03      | ~ v1_relat_1(sK1) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_14]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6060,plain,
% 11.65/2.03      ( v1_funct_1(k2_funct_1(sK1)) = iProver_top
% 11.65/2.03      | v1_funct_1(sK1) != iProver_top
% 11.65/2.03      | v1_relat_1(sK1) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_6059]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_15,plain,
% 11.65/2.03      ( ~ v1_funct_1(X0)
% 11.65/2.03      | ~ v1_relat_1(X0)
% 11.65/2.03      | v1_relat_1(k2_funct_1(X0)) ),
% 11.65/2.03      inference(cnf_transformation,[],[f100]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6073,plain,
% 11.65/2.03      ( ~ v1_funct_1(sK1)
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK1))
% 11.65/2.03      | ~ v1_relat_1(sK1) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_15]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6074,plain,
% 11.65/2.03      ( v1_funct_1(sK1) != iProver_top
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK1)) = iProver_top
% 11.65/2.03      | v1_relat_1(sK1) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_6073]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_9273,plain,
% 11.65/2.03      ( m1_subset_1(k2_funct_1(sK1),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK1),sK0))) = iProver_top ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_7088,c_60,c_185,c_3982,c_6060,c_6074]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_37,plain,
% 11.65/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f122]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1798,plain,
% 11.65/2.03      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 11.65/2.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_9281,plain,
% 11.65/2.03      ( k7_relset_1(k2_relat_1(sK1),sK0,k2_funct_1(sK1),k2_relat_1(sK1)) = k2_relset_1(k2_relat_1(sK1),sK0,k2_funct_1(sK1)) ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_9273,c_1798]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_33,plain,
% 11.65/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 11.65/2.03      inference(cnf_transformation,[],[f119]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1800,plain,
% 11.65/2.03      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 11.65/2.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_9282,plain,
% 11.65/2.03      ( k7_relset_1(k2_relat_1(sK1),sK0,k2_funct_1(sK1),X0) = k9_relat_1(k2_funct_1(sK1),X0) ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_9273,c_1800]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_32,plain,
% 11.65/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f118]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1801,plain,
% 11.65/2.03      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 11.65/2.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_9284,plain,
% 11.65/2.03      ( k2_relset_1(k2_relat_1(sK1),sK0,k2_funct_1(sK1)) = k2_relat_1(k2_funct_1(sK1)) ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_9273,c_1801]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_9290,plain,
% 11.65/2.03      ( k2_relset_1(k2_relat_1(sK1),sK0,k2_funct_1(sK1)) = sK0 ),
% 11.65/2.03      inference(light_normalisation,[status(thm)],[c_9284,c_7074]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_9292,plain,
% 11.65/2.03      ( k9_relat_1(k2_funct_1(sK1),k2_relat_1(sK1)) = sK0 ),
% 11.65/2.03      inference(demodulation,[status(thm)],[c_9281,c_9282,c_9290]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_38414,plain,
% 11.65/2.03      ( k2_relat_1(sK2) = sK0 | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(light_normalisation,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_38405,c_7959,c_9292]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7461,plain,
% 11.65/2.03      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
% 11.65/2.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.03      | v1_funct_1(X2) != iProver_top
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1784,c_1794]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7648,plain,
% 11.65/2.03      ( v1_funct_1(X2) != iProver_top
% 11.65/2.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.03      | k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2) ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_7461,c_63]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7649,plain,
% 11.65/2.03      ( k1_partfun1(X0,X1,sK0,sK0,X2,sK2) = k5_relat_1(X2,sK2)
% 11.65/2.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.03      | v1_funct_1(X2) != iProver_top ),
% 11.65/2.03      inference(renaming,[status(thm)],[c_7648]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7656,plain,
% 11.65/2.03      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2)
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1784,c_7649]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7667,plain,
% 11.65/2.03      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK2) = k5_relat_1(sK2,sK2) ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_7656,c_63]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_43,plain,
% 11.65/2.03      ( ~ v1_funct_2(X0,X1,X2)
% 11.65/2.03      | ~ v1_funct_2(X3,X4,X1)
% 11.65/2.03      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
% 11.65/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | v2_funct_1(X3)
% 11.65/2.03      | ~ v2_funct_1(k1_partfun1(X4,X1,X1,X2,X3,X0))
% 11.65/2.03      | ~ v1_funct_1(X0)
% 11.65/2.03      | ~ v1_funct_1(X3)
% 11.65/2.03      | k1_xboole_0 = X2 ),
% 11.65/2.03      inference(cnf_transformation,[],[f129]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1792,plain,
% 11.65/2.03      ( k1_xboole_0 = X0
% 11.65/2.03      | v1_funct_2(X1,X2,X0) != iProver_top
% 11.65/2.03      | v1_funct_2(X3,X4,X2) != iProver_top
% 11.65/2.03      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 11.65/2.03      | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X2))) != iProver_top
% 11.65/2.03      | v2_funct_1(X3) = iProver_top
% 11.65/2.03      | v2_funct_1(k1_partfun1(X4,X2,X2,X0,X3,X1)) != iProver_top
% 11.65/2.03      | v1_funct_1(X1) != iProver_top
% 11.65/2.03      | v1_funct_1(X3) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_8055,plain,
% 11.65/2.03      ( sK0 = k1_xboole_0
% 11.65/2.03      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 11.65/2.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.65/2.03      | v2_funct_1(k5_relat_1(sK2,sK2)) != iProver_top
% 11.65/2.03      | v2_funct_1(sK2) = iProver_top
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_7667,c_1792]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_62,plain,
% 11.65/2.03      ( m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_57]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_55,negated_conjecture,
% 11.65/2.03      ( v1_funct_2(sK2,sK0,sK0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f142]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_64,plain,
% 11.65/2.03      ( v1_funct_2(sK2,sK0,sK0) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_55]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_65,plain,
% 11.65/2.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_54]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_3,plain,
% 11.65/2.03      ( r1_tarski(X0,X0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f158]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_197,plain,
% 11.65/2.03      ( r1_tarski(sK0,sK0) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_3]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1,plain,
% 11.65/2.03      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 11.65/2.03      inference(cnf_transformation,[],[f89]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_201,plain,
% 11.65/2.03      ( ~ r1_tarski(sK0,sK0) | sK0 = sK0 ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_1]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_0,plain,
% 11.65/2.03      ( v1_xboole_0(k1_xboole_0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f86]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_203,plain,
% 11.65/2.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1012,plain,
% 11.65/2.03      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 11.65/2.03      theory(equality) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_2030,plain,
% 11.65/2.03      ( v1_xboole_0(X0)
% 11.65/2.03      | ~ v1_xboole_0(k1_xboole_0)
% 11.65/2.03      | X0 != k1_xboole_0 ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_1012]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_2031,plain,
% 11.65/2.03      ( X0 != k1_xboole_0
% 11.65/2.03      | v1_xboole_0(X0) = iProver_top
% 11.65/2.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_2030]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_2033,plain,
% 11.65/2.03      ( sK0 != k1_xboole_0
% 11.65/2.03      | v1_xboole_0(sK0) = iProver_top
% 11.65/2.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_2031]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1011,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_2217,plain,
% 11.65/2.03      ( X0 != X1 | X0 = k1_xboole_0 | k1_xboole_0 != X1 ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_1011]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_2218,plain,
% 11.65/2.03      ( sK0 != sK0 | sK0 = k1_xboole_0 | k1_xboole_0 != sK0 ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_2217]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_2146,plain,
% 11.65/2.03      ( ~ r1_tarski(X0,k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1))
% 11.65/2.03      | ~ r1_tarski(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),X0)
% 11.65/2.03      | X0 = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_1]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_2292,plain,
% 11.65/2.03      ( ~ r1_tarski(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1))
% 11.65/2.03      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_2146]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_2701,plain,
% 11.65/2.03      ( r1_tarski(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1),k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_3]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_2392,plain,
% 11.65/2.03      ( X0 != X1 | X0 = sK1 | sK1 != X1 ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_1011]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_3170,plain,
% 11.65/2.03      ( X0 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 11.65/2.03      | X0 = sK1
% 11.65/2.03      | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_2392]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_3856,plain,
% 11.65/2.03      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)
% 11.65/2.03      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) = sK1
% 11.65/2.03      | sK1 != k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_3170]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_30,plain,
% 11.65/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | ~ v1_xboole_0(X2)
% 11.65/2.03      | v1_xboole_0(X0) ),
% 11.65/2.03      inference(cnf_transformation,[],[f116]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1803,plain,
% 11.65/2.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 11.65/2.03      | v1_xboole_0(X2) != iProver_top
% 11.65/2.03      | v1_xboole_0(X0) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_4922,plain,
% 11.65/2.03      ( v1_xboole_0(sK2) = iProver_top
% 11.65/2.03      | v1_xboole_0(sK0) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1784,c_1803]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_40,plain,
% 11.65/2.03      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
% 11.65/2.03      inference(cnf_transformation,[],[f126]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_98,plain,
% 11.65/2.03      ( m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_40]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_34,plain,
% 11.65/2.03      ( r2_relset_1(X0,X1,X2,X2)
% 11.65/2.03      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 11.65/2.03      inference(cnf_transformation,[],[f159]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_51,negated_conjecture,
% 11.65/2.03      ( ~ r2_relset_1(sK0,sK0,sK2,k6_partfun1(sK0)) ),
% 11.65/2.03      inference(cnf_transformation,[],[f146]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_658,plain,
% 11.65/2.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | k6_partfun1(sK0) != X0
% 11.65/2.03      | sK2 != X0
% 11.65/2.03      | sK0 != X2
% 11.65/2.03      | sK0 != X1 ),
% 11.65/2.03      inference(resolution_lifted,[status(thm)],[c_34,c_51]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_659,plain,
% 11.65/2.03      ( ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
% 11.65/2.03      | sK2 != k6_partfun1(sK0) ),
% 11.65/2.03      inference(unflattening,[status(thm)],[c_658]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_4,plain,
% 11.65/2.03      ( ~ v1_xboole_0(X0) | ~ v1_xboole_0(X1) | X0 = X1 ),
% 11.65/2.03      inference(cnf_transformation,[],[f90]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1881,plain,
% 11.65/2.03      ( ~ v1_xboole_0(k6_partfun1(sK0))
% 11.65/2.03      | ~ v1_xboole_0(sK2)
% 11.65/2.03      | sK2 = k6_partfun1(sK0) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_4]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1882,plain,
% 11.65/2.03      ( sK2 = k6_partfun1(sK0)
% 11.65/2.03      | v1_xboole_0(k6_partfun1(sK0)) != iProver_top
% 11.65/2.03      | v1_xboole_0(sK2) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_1881]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1916,plain,
% 11.65/2.03      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.65/2.03      | ~ v1_xboole_0(X1)
% 11.65/2.03      | v1_xboole_0(sK2) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_30]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1917,plain,
% 11.65/2.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.65/2.03      | v1_xboole_0(X1) != iProver_top
% 11.65/2.03      | v1_xboole_0(sK2) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_1916]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1919,plain,
% 11.65/2.03      ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.65/2.03      | v1_xboole_0(sK2) = iProver_top
% 11.65/2.03      | v1_xboole_0(sK0) != iProver_top ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_1917]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1795,plain,
% 11.65/2.03      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) = iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_4920,plain,
% 11.65/2.03      ( v1_xboole_0(X0) != iProver_top
% 11.65/2.03      | v1_xboole_0(k6_partfun1(X0)) = iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1795,c_1803]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_4925,plain,
% 11.65/2.03      ( v1_xboole_0(k6_partfun1(sK0)) = iProver_top
% 11.65/2.03      | v1_xboole_0(sK0) != iProver_top ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_4920]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_5176,plain,
% 11.65/2.03      ( v1_xboole_0(sK0) != iProver_top ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_4922,c_65,c_98,c_659,c_1882,c_1919,c_4925]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_4773,plain,
% 11.65/2.03      ( ~ v1_funct_2(X0,X1,X2)
% 11.65/2.03      | ~ v1_funct_2(sK1,X2,X3)
% 11.65/2.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.65/2.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.65/2.03      | v2_funct_1(X0)
% 11.65/2.03      | ~ v2_funct_1(k1_partfun1(X1,X2,X2,X3,X0,sK1))
% 11.65/2.03      | ~ v1_funct_1(X0)
% 11.65/2.03      | ~ v1_funct_1(sK1)
% 11.65/2.03      | k1_xboole_0 = X3 ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_43]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_5913,plain,
% 11.65/2.03      ( ~ v1_funct_2(sK1,X0,X1)
% 11.65/2.03      | ~ v1_funct_2(sK2,X2,X0)
% 11.65/2.03      | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.65/2.03      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
% 11.65/2.03      | ~ v2_funct_1(k1_partfun1(X2,X0,X0,X1,sK2,sK1))
% 11.65/2.03      | v2_funct_1(sK2)
% 11.65/2.03      | ~ v1_funct_1(sK1)
% 11.65/2.03      | ~ v1_funct_1(sK2)
% 11.65/2.03      | k1_xboole_0 = X1 ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_4773]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_5914,plain,
% 11.65/2.03      ( k1_xboole_0 = X0
% 11.65/2.03      | v1_funct_2(sK1,X1,X0) != iProver_top
% 11.65/2.03      | v1_funct_2(sK2,X2,X1) != iProver_top
% 11.65/2.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top
% 11.65/2.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top
% 11.65/2.03      | v2_funct_1(k1_partfun1(X2,X1,X1,X0,sK2,sK1)) != iProver_top
% 11.65/2.03      | v2_funct_1(sK2) = iProver_top
% 11.65/2.03      | v1_funct_1(sK1) != iProver_top
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_5913]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_5916,plain,
% 11.65/2.03      ( k1_xboole_0 = sK0
% 11.65/2.03      | v1_funct_2(sK1,sK0,sK0) != iProver_top
% 11.65/2.03      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 11.65/2.03      | m1_subset_1(sK1,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.65/2.03      | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) != iProver_top
% 11.65/2.03      | v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) != iProver_top
% 11.65/2.03      | v2_funct_1(sK2) = iProver_top
% 11.65/2.03      | v1_funct_1(sK1) != iProver_top
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_5914]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1025,plain,
% 11.65/2.03      ( ~ v2_funct_1(X0) | v2_funct_1(X1) | X1 != X0 ),
% 11.65/2.03      theory(equality) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_4025,plain,
% 11.65/2.03      ( v2_funct_1(X0) | ~ v2_funct_1(sK1) | X0 != sK1 ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_1025]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6264,plain,
% 11.65/2.03      ( v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1))
% 11.65/2.03      | ~ v2_funct_1(sK1)
% 11.65/2.03      | k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != sK1 ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_4025]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6279,plain,
% 11.65/2.03      ( k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1) != sK1
% 11.65/2.03      | v2_funct_1(k1_partfun1(sK0,sK0,sK0,sK0,sK2,sK1)) = iProver_top
% 11.65/2.03      | v2_funct_1(sK1) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_6264]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_17105,plain,
% 11.65/2.03      ( v2_funct_1(sK2) = iProver_top ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_8055,c_59,c_60,c_61,c_57,c_62,c_56,c_63,c_64,c_54,
% 11.65/2.03                 c_65,c_67,c_98,c_197,c_201,c_203,c_659,c_667,c_1882,
% 11.65/2.03                 c_1888,c_1919,c_2033,c_2218,c_2292,c_2701,c_3856,c_4925,
% 11.65/2.03                 c_5916,c_6279]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_26,plain,
% 11.65/2.03      ( ~ v2_funct_1(X0)
% 11.65/2.03      | ~ v2_funct_1(X1)
% 11.65/2.03      | ~ v1_funct_1(X0)
% 11.65/2.03      | ~ v1_funct_1(X1)
% 11.65/2.03      | ~ v1_relat_1(X0)
% 11.65/2.03      | ~ v1_relat_1(X1)
% 11.65/2.03      | k5_relat_1(k2_funct_1(X1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,X1)) ),
% 11.65/2.03      inference(cnf_transformation,[],[f112]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1804,plain,
% 11.65/2.03      ( k5_relat_1(k2_funct_1(X0),k2_funct_1(X1)) = k2_funct_1(k5_relat_1(X1,X0))
% 11.65/2.03      | v2_funct_1(X1) != iProver_top
% 11.65/2.03      | v2_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_funct_1(X1) != iProver_top
% 11.65/2.03      | v1_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_relat_1(X1) != iProver_top
% 11.65/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_8248,plain,
% 11.65/2.03      ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK1))
% 11.65/2.03      | v2_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_funct_1(sK1) != iProver_top
% 11.65/2.03      | v1_relat_1(X0) != iProver_top
% 11.65/2.03      | v1_relat_1(sK1) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1785,c_1804]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_8450,plain,
% 11.65/2.03      ( v1_relat_1(X0) != iProver_top
% 11.65/2.03      | k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK1))
% 11.65/2.03      | v2_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_funct_1(X0) != iProver_top ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_8248,c_60,c_185,c_3982]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_8451,plain,
% 11.65/2.03      ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(X0)) = k2_funct_1(k5_relat_1(X0,sK1))
% 11.65/2.03      | v2_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.03      inference(renaming,[status(thm)],[c_8450]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_17109,plain,
% 11.65/2.03      ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) = k2_funct_1(k5_relat_1(sK2,sK1))
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_17105,c_8451]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_17117,plain,
% 11.65/2.03      ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK1)
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(light_normalisation,[status(thm)],[c_17109,c_7957]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_27813,plain,
% 11.65/2.03      ( k5_relat_1(k2_funct_1(sK1),k2_funct_1(sK2)) = k2_funct_1(sK1) ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_17117,c_63,c_185,c_3981]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_21,plain,
% 11.65/2.03      ( ~ v1_funct_1(X0)
% 11.65/2.03      | ~ v1_funct_1(X1)
% 11.65/2.03      | ~ v1_relat_1(X0)
% 11.65/2.03      | ~ v1_relat_1(X1)
% 11.65/2.03      | k5_relat_1(X0,X1) != X0
% 11.65/2.03      | k1_relat_1(X1) != k2_relat_1(X0)
% 11.65/2.03      | k6_partfun1(k1_relat_1(X1)) = X1 ),
% 11.65/2.03      inference(cnf_transformation,[],[f153]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1809,plain,
% 11.65/2.03      ( k5_relat_1(X0,X1) != X0
% 11.65/2.03      | k1_relat_1(X1) != k2_relat_1(X0)
% 11.65/2.03      | k6_partfun1(k1_relat_1(X1)) = X1
% 11.65/2.03      | v1_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_funct_1(X1) != iProver_top
% 11.65/2.03      | v1_relat_1(X0) != iProver_top
% 11.65/2.03      | v1_relat_1(X1) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_27817,plain,
% 11.65/2.03      ( k1_relat_1(k2_funct_1(sK2)) != k2_relat_1(k2_funct_1(sK1))
% 11.65/2.03      | k6_partfun1(k1_relat_1(k2_funct_1(sK2))) = k2_funct_1(sK2)
% 11.65/2.03      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 11.65/2.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK1)) != iProver_top
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_27813,c_1809]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_17114,plain,
% 11.65/2.03      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2)
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_17105,c_1807]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_24780,plain,
% 11.65/2.03      ( k1_relat_1(k2_funct_1(sK2)) = k2_relat_1(sK2) ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_17114,c_63,c_185,c_3981]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_27818,plain,
% 11.65/2.03      ( k6_partfun1(k2_relat_1(sK2)) = k2_funct_1(sK2)
% 11.65/2.03      | k2_relat_1(sK2) != sK0
% 11.65/2.03      | v1_funct_1(k2_funct_1(sK1)) != iProver_top
% 11.65/2.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK1)) != iProver_top
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top ),
% 11.65/2.03      inference(light_normalisation,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_27817,c_7074,c_24780]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_24,plain,
% 11.65/2.03      ( ~ v2_funct_1(X0)
% 11.65/2.03      | ~ v1_funct_1(X0)
% 11.65/2.03      | ~ v1_relat_1(X0)
% 11.65/2.03      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) ),
% 11.65/2.03      inference(cnf_transformation,[],[f154]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1806,plain,
% 11.65/2.03      ( k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
% 11.65/2.03      | v2_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_funct_1(X0) != iProver_top
% 11.65/2.03      | v1_relat_1(X0) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_17111,plain,
% 11.65/2.03      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2))
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_17105,c_1806]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_27645,plain,
% 11.65/2.03      ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(k2_relat_1(sK2)) ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_17111,c_63,c_185,c_3981]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_27647,plain,
% 11.65/2.03      ( k6_partfun1(k1_relat_1(sK2)) = sK2
% 11.65/2.03      | k6_partfun1(k2_relat_1(sK2)) != k2_funct_1(sK2)
% 11.65/2.03      | k2_relat_1(k2_funct_1(sK2)) != k1_relat_1(sK2)
% 11.65/2.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_27645,c_1809]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_3973,plain,
% 11.65/2.03      ( k1_relset_1(sK0,sK0,sK2) = sK0
% 11.65/2.03      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1784,c_1786]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_3315,plain,
% 11.65/2.03      ( k1_relset_1(sK0,sK0,sK2) = k1_relat_1(sK2) ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_1784,c_1802]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_3976,plain,
% 11.65/2.03      ( k1_relat_1(sK2) = sK0
% 11.65/2.03      | v1_funct_2(sK2,sK0,sK0) != iProver_top
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top ),
% 11.65/2.03      inference(demodulation,[status(thm)],[c_3973,c_3315]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_7274,plain,
% 11.65/2.03      ( k1_relat_1(sK2) = sK0 ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_3976,c_63,c_64]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_17113,plain,
% 11.65/2.03      ( k2_relat_1(k2_funct_1(sK2)) = k1_relat_1(sK2)
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(superposition,[status(thm)],[c_17105,c_1808]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_17115,plain,
% 11.65/2.03      ( k2_relat_1(k2_funct_1(sK2)) = sK0
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(light_normalisation,[status(thm)],[c_17113,c_7274]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_23852,plain,
% 11.65/2.03      ( k2_relat_1(k2_funct_1(sK2)) = sK0 ),
% 11.65/2.03      inference(global_propositional_subsumption,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_17115,c_63,c_185,c_3981]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_27648,plain,
% 11.65/2.03      ( k6_partfun1(k2_relat_1(sK2)) != k2_funct_1(sK2)
% 11.65/2.03      | k6_partfun1(sK0) = sK2
% 11.65/2.03      | sK0 != sK0
% 11.65/2.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(light_normalisation,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_27647,c_7274,c_23852]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_27649,plain,
% 11.65/2.03      ( k6_partfun1(k2_relat_1(sK2)) != k2_funct_1(sK2)
% 11.65/2.03      | k6_partfun1(sK0) = sK2
% 11.65/2.03      | v1_funct_1(k2_funct_1(sK2)) != iProver_top
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK2)) != iProver_top
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(equality_resolution_simp,[status(thm)],[c_27648]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6070,plain,
% 11.65/2.03      ( ~ v1_funct_1(sK2)
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK2))
% 11.65/2.03      | ~ v1_relat_1(sK2) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_15]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6071,plain,
% 11.65/2.03      ( v1_funct_1(sK2) != iProver_top
% 11.65/2.03      | v1_relat_1(k2_funct_1(sK2)) = iProver_top
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_6070]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6056,plain,
% 11.65/2.03      ( v1_funct_1(k2_funct_1(sK2))
% 11.65/2.03      | ~ v1_funct_1(sK2)
% 11.65/2.03      | ~ v1_relat_1(sK2) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_14]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_6057,plain,
% 11.65/2.03      ( v1_funct_1(k2_funct_1(sK2)) = iProver_top
% 11.65/2.03      | v1_funct_1(sK2) != iProver_top
% 11.65/2.03      | v1_relat_1(sK2) != iProver_top ),
% 11.65/2.03      inference(predicate_to_equality,[status(thm)],[c_6056]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1010,plain,( X0 = X0 ),theory(equality) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_2042,plain,
% 11.65/2.03      ( sK2 = sK2 ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_1010]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1886,plain,
% 11.65/2.03      ( k6_partfun1(sK0) != X0 | sK2 != X0 | sK2 = k6_partfun1(sK0) ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_1011]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(c_1950,plain,
% 11.65/2.03      ( k6_partfun1(sK0) != sK2 | sK2 = k6_partfun1(sK0) | sK2 != sK2 ),
% 11.65/2.03      inference(instantiation,[status(thm)],[c_1886]) ).
% 11.65/2.03  
% 11.65/2.03  cnf(contradiction,plain,
% 11.65/2.03      ( $false ),
% 11.65/2.03      inference(minisat,
% 11.65/2.03                [status(thm)],
% 11.65/2.03                [c_38414,c_27818,c_27649,c_6074,c_6071,c_6060,c_6057,
% 11.65/2.03                 c_3982,c_3981,c_2042,c_1950,c_659,c_185,c_98,c_63,c_60]) ).
% 11.65/2.03  
% 11.65/2.03  
% 11.65/2.03  % SZS output end CNFRefutation for theBenchmark.p
% 11.65/2.03  
% 11.65/2.03  ------                               Statistics
% 11.65/2.03  
% 11.65/2.03  ------ General
% 11.65/2.03  
% 11.65/2.03  abstr_ref_over_cycles:                  0
% 11.65/2.03  abstr_ref_under_cycles:                 0
% 11.65/2.03  gc_basic_clause_elim:                   0
% 11.65/2.03  forced_gc_time:                         0
% 11.65/2.03  parsing_time:                           0.012
% 11.65/2.03  unif_index_cands_time:                  0.
% 11.65/2.03  unif_index_add_time:                    0.
% 11.65/2.03  orderings_time:                         0.
% 11.65/2.03  out_proof_time:                         0.026
% 11.65/2.03  total_time:                             1.258
% 11.65/2.03  num_of_symbols:                         59
% 11.65/2.03  num_of_terms:                           50043
% 11.65/2.03  
% 11.65/2.03  ------ Preprocessing
% 11.65/2.03  
% 11.65/2.03  num_of_splits:                          0
% 11.65/2.03  num_of_split_atoms:                     0
% 11.65/2.03  num_of_reused_defs:                     0
% 11.65/2.03  num_eq_ax_congr_red:                    52
% 11.65/2.03  num_of_sem_filtered_clauses:            1
% 11.65/2.03  num_of_subtypes:                        0
% 11.65/2.03  monotx_restored_types:                  0
% 11.65/2.03  sat_num_of_epr_types:                   0
% 11.65/2.03  sat_num_of_non_cyclic_types:            0
% 11.65/2.03  sat_guarded_non_collapsed_types:        0
% 11.65/2.03  num_pure_diseq_elim:                    0
% 11.65/2.03  simp_replaced_by:                       0
% 11.65/2.03  res_preprocessed:                       253
% 11.65/2.04  prep_upred:                             0
% 11.65/2.04  prep_unflattend:                        11
% 11.65/2.04  smt_new_axioms:                         0
% 11.65/2.04  pred_elim_cands:                        7
% 11.65/2.04  pred_elim:                              3
% 11.65/2.04  pred_elim_cl:                           4
% 11.65/2.04  pred_elim_cycles:                       5
% 11.65/2.04  merged_defs:                            0
% 11.65/2.04  merged_defs_ncl:                        0
% 11.65/2.04  bin_hyper_res:                          0
% 11.65/2.04  prep_cycles:                            4
% 11.65/2.04  pred_elim_time:                         0.004
% 11.65/2.04  splitting_time:                         0.
% 11.65/2.04  sem_filter_time:                        0.
% 11.65/2.04  monotx_time:                            0.
% 11.65/2.04  subtype_inf_time:                       0.
% 11.65/2.04  
% 11.65/2.04  ------ Problem properties
% 11.65/2.04  
% 11.65/2.04  clauses:                                53
% 11.65/2.04  conjectures:                            7
% 11.65/2.04  epr:                                    9
% 11.65/2.04  horn:                                   52
% 11.65/2.04  ground:                                 11
% 11.65/2.04  unary:                                  18
% 11.65/2.04  binary:                                 8
% 11.65/2.04  lits:                                   156
% 11.65/2.04  lits_eq:                                32
% 11.65/2.04  fd_pure:                                0
% 11.65/2.04  fd_pseudo:                              0
% 11.65/2.04  fd_cond:                                1
% 11.65/2.04  fd_pseudo_cond:                         2
% 11.65/2.04  ac_symbols:                             0
% 11.65/2.04  
% 11.65/2.04  ------ Propositional Solver
% 11.65/2.04  
% 11.65/2.04  prop_solver_calls:                      35
% 11.65/2.04  prop_fast_solver_calls:                 2629
% 11.65/2.04  smt_solver_calls:                       0
% 11.65/2.04  smt_fast_solver_calls:                  0
% 11.65/2.04  prop_num_of_clauses:                    19724
% 11.65/2.04  prop_preprocess_simplified:             35592
% 11.65/2.04  prop_fo_subsumed:                       231
% 11.65/2.04  prop_solver_time:                       0.
% 11.65/2.04  smt_solver_time:                        0.
% 11.65/2.04  smt_fast_solver_time:                   0.
% 11.65/2.04  prop_fast_solver_time:                  0.
% 11.65/2.04  prop_unsat_core_time:                   0.003
% 11.65/2.04  
% 11.65/2.04  ------ QBF
% 11.65/2.04  
% 11.65/2.04  qbf_q_res:                              0
% 11.65/2.04  qbf_num_tautologies:                    0
% 11.65/2.04  qbf_prep_cycles:                        0
% 11.65/2.04  
% 11.65/2.04  ------ BMC1
% 11.65/2.04  
% 11.65/2.04  bmc1_current_bound:                     -1
% 11.65/2.04  bmc1_last_solved_bound:                 -1
% 11.65/2.04  bmc1_unsat_core_size:                   -1
% 11.65/2.04  bmc1_unsat_core_parents_size:           -1
% 11.65/2.04  bmc1_merge_next_fun:                    0
% 11.65/2.04  bmc1_unsat_core_clauses_time:           0.
% 11.65/2.04  
% 11.65/2.04  ------ Instantiation
% 11.65/2.04  
% 11.65/2.04  inst_num_of_clauses:                    5863
% 11.65/2.04  inst_num_in_passive:                    1508
% 11.65/2.04  inst_num_in_active:                     1728
% 11.65/2.04  inst_num_in_unprocessed:                2627
% 11.65/2.04  inst_num_of_loops:                      2080
% 11.65/2.04  inst_num_of_learning_restarts:          0
% 11.65/2.04  inst_num_moves_active_passive:          347
% 11.65/2.04  inst_lit_activity:                      0
% 11.65/2.04  inst_lit_activity_moves:                2
% 11.65/2.04  inst_num_tautologies:                   0
% 11.65/2.04  inst_num_prop_implied:                  0
% 11.65/2.04  inst_num_existing_simplified:           0
% 11.65/2.04  inst_num_eq_res_simplified:             0
% 11.65/2.04  inst_num_child_elim:                    0
% 11.65/2.04  inst_num_of_dismatching_blockings:      2901
% 11.65/2.04  inst_num_of_non_proper_insts:           5290
% 11.65/2.04  inst_num_of_duplicates:                 0
% 11.65/2.04  inst_inst_num_from_inst_to_res:         0
% 11.65/2.04  inst_dismatching_checking_time:         0.
% 11.65/2.04  
% 11.65/2.04  ------ Resolution
% 11.65/2.04  
% 11.65/2.04  res_num_of_clauses:                     0
% 11.65/2.04  res_num_in_passive:                     0
% 11.65/2.04  res_num_in_active:                      0
% 11.65/2.04  res_num_of_loops:                       257
% 11.65/2.04  res_forward_subset_subsumed:            848
% 11.65/2.04  res_backward_subset_subsumed:           0
% 11.65/2.04  res_forward_subsumed:                   0
% 11.65/2.04  res_backward_subsumed:                  0
% 11.65/2.04  res_forward_subsumption_resolution:     0
% 11.65/2.04  res_backward_subsumption_resolution:    0
% 11.65/2.04  res_clause_to_clause_subsumption:       1950
% 11.65/2.04  res_orphan_elimination:                 0
% 11.65/2.04  res_tautology_del:                      320
% 11.65/2.04  res_num_eq_res_simplified:              0
% 11.65/2.04  res_num_sel_changes:                    0
% 11.65/2.04  res_moves_from_active_to_pass:          0
% 11.65/2.04  
% 11.65/2.04  ------ Superposition
% 11.65/2.04  
% 11.65/2.04  sup_time_total:                         0.
% 11.65/2.04  sup_time_generating:                    0.
% 11.65/2.04  sup_time_sim_full:                      0.
% 11.65/2.04  sup_time_sim_immed:                     0.
% 11.65/2.04  
% 11.65/2.04  sup_num_of_clauses:                     1010
% 11.65/2.04  sup_num_in_active:                      393
% 11.65/2.04  sup_num_in_passive:                     617
% 11.65/2.04  sup_num_of_loops:                       415
% 11.65/2.04  sup_fw_superposition:                   627
% 11.65/2.04  sup_bw_superposition:                   667
% 11.65/2.04  sup_immediate_simplified:               424
% 11.65/2.04  sup_given_eliminated:                   1
% 11.65/2.04  comparisons_done:                       0
% 11.65/2.04  comparisons_avoided:                    0
% 11.65/2.04  
% 11.65/2.04  ------ Simplifications
% 11.65/2.04  
% 11.65/2.04  
% 11.65/2.04  sim_fw_subset_subsumed:                 36
% 11.65/2.04  sim_bw_subset_subsumed:                 12
% 11.65/2.04  sim_fw_subsumed:                        36
% 11.65/2.04  sim_bw_subsumed:                        0
% 11.65/2.04  sim_fw_subsumption_res:                 0
% 11.65/2.04  sim_bw_subsumption_res:                 0
% 11.65/2.04  sim_tautology_del:                      24
% 11.65/2.04  sim_eq_tautology_del:                   142
% 11.65/2.04  sim_eq_res_simp:                        4
% 11.65/2.04  sim_fw_demodulated:                     38
% 11.65/2.04  sim_bw_demodulated:                     23
% 11.65/2.04  sim_light_normalised:                   344
% 11.65/2.04  sim_joinable_taut:                      0
% 11.65/2.04  sim_joinable_simp:                      0
% 11.65/2.04  sim_ac_normalised:                      0
% 11.65/2.04  sim_smt_subsumption:                    0
% 11.65/2.04  
%------------------------------------------------------------------------------
