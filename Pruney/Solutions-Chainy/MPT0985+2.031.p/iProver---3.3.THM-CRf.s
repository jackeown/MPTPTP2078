%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:02:26 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :  172 (1244 expanded)
%              Number of clauses        :  102 ( 399 expanded)
%              Number of leaves         :   21 ( 248 expanded)
%              Depth                    :   19
%              Number of atoms          :  557 (6522 expanded)
%              Number of equality atoms :  216 (1208 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f40,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f41,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f56,plain,
    ( ? [X0,X1,X2] :
        ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
          | ~ v1_funct_1(k2_funct_1(X2)) )
        & k2_relset_1(X0,X1,X2) = X1
        & v2_funct_1(X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
        | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
        | ~ v1_funct_1(k2_funct_1(sK4)) )
      & k2_relset_1(sK2,sK3,sK4) = sK3
      & v2_funct_1(sK4)
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK4,sK2,sK3)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
      | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
      | ~ v1_funct_1(k2_funct_1(sK4)) )
    & k2_relset_1(sK2,sK3,sK4) = sK3
    & v2_funct_1(sK4)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK4,sK2,sK3)
    & v1_funct_1(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f56])).

fof(f97,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f57])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f33])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f17,axiom,(
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

fof(f36,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f37,plain,(
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
    inference(flattening,[],[f36])).

fof(f55,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f96,plain,(
    v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f57])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f99,plain,(
    k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f57])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f29,plain,(
    ! [X0] :
      ( ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f78,plain,(
    ! [X0] :
      ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f98,plain,(
    v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f95,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f57])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( ( k1_xboole_0 = k2_relat_1(X0)
          | k1_xboole_0 = k1_relat_1(X0) )
       => k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f25,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ( k1_xboole_0 != k2_relat_1(X0)
        & k1_xboole_0 != k1_relat_1(X0) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f74,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | k1_xboole_0 != k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f76,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f46])).

fof(f48,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK1(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f43,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f42])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f7])).

fof(f72,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f100,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f57])).

fof(f77,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f18,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f39,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f38])).

fof(f94,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f79,plain,(
    ! [X0] :
      ( k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f93,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_40,negated_conjecture,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_2746,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_27,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_25,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_489,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(resolution,[status(thm)],[c_27,c_25])).

cnf(c_493,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_funct_2(X0,X1,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_489,c_27,c_25])).

cnf(c_494,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1) ),
    inference(renaming,[status(thm)],[c_493])).

cnf(c_33,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1288,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | ~ v1_xboole_0(X1)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(resolution,[status(thm)],[c_494,c_33])).

cnf(c_2741,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1288])).

cnf(c_4121,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0
    | v1_funct_1(sK4) != iProver_top
    | v1_xboole_0(sK2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2746,c_2741])).

cnf(c_41,negated_conjecture,
    ( v1_funct_2(sK4,sK2,sK3) ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1413,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK2 != X1
    | sK3 != X2
    | sK4 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_33,c_41])).

cnf(c_1414,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK4) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_1413])).

cnf(c_1921,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3123,plain,
    ( sK3 != X0
    | sK3 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1921])).

cnf(c_3448,plain,
    ( sK3 != sK3
    | sK3 = k1_xboole_0
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3123])).

cnf(c_1920,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_3449,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_1920])).

cnf(c_4251,plain,
    ( k1_relset_1(sK2,sK3,sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4121,c_40,c_1414,c_3448,c_3449])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_2749,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_5507,plain,
    ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2746,c_2749])).

cnf(c_5892,plain,
    ( k1_relat_1(sK4) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4251,c_5507])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2748,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4876,plain,
    ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
    inference(superposition,[status(thm)],[c_2746,c_2748])).

cnf(c_38,negated_conjecture,
    ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_4888,plain,
    ( k2_relat_1(sK4) = sK3 ),
    inference(light_normalisation,[status(thm)],[c_4876,c_38])).

cnf(c_21,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_39,negated_conjecture,
    ( v2_funct_1(sK4) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_515,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_39])).

cnf(c_516,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_515])).

cnf(c_42,negated_conjecture,
    ( v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_518,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_516,c_42])).

cnf(c_2743,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_518])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_3087,plain,
    ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_3100,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2743,c_42,c_40,c_516,c_3087])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_2753,plain,
    ( k1_relat_1(X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4215,plain,
    ( k2_funct_1(sK4) = k1_xboole_0
    | k2_relat_1(sK4) != k1_xboole_0
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3100,c_2753])).

cnf(c_19,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | v1_relat_1(k2_funct_1(X0)) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_3079,plain,
    ( ~ v1_funct_1(sK4)
    | v1_relat_1(k2_funct_1(sK4))
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_4216,plain,
    ( ~ v1_relat_1(k2_funct_1(sK4))
    | k2_funct_1(sK4) = k1_xboole_0
    | k2_relat_1(sK4) != k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4215])).

cnf(c_4345,plain,
    ( k2_relat_1(sK4) != k1_xboole_0
    | k2_funct_1(sK4) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4215,c_42,c_40,c_3079,c_3087,c_4216])).

cnf(c_4346,plain,
    ( k2_funct_1(sK4) = k1_xboole_0
    | k2_relat_1(sK4) != k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_4345])).

cnf(c_4911,plain,
    ( k2_funct_1(sK4) = k1_xboole_0
    | sK3 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_4888,c_4346])).

cnf(c_5,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1922,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_3090,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK3)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_1922])).

cnf(c_3092,plain,
    ( v1_xboole_0(sK3)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK3 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3090])).

cnf(c_4042,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(k2_funct_1(sK4))
    | k2_funct_1(sK4) != X0 ),
    inference(instantiation,[status(thm)],[c_1922])).

cnf(c_4044,plain,
    ( v1_xboole_0(k2_funct_1(sK4))
    | ~ v1_xboole_0(k1_xboole_0)
    | k2_funct_1(sK4) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_4042])).

cnf(c_3,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK1(X0,X1),X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2762,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2764,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4158,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_2762,c_2764])).

cnf(c_13,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2757,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_37,negated_conjecture,
    ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_1384,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_xboole_0(X1)
    | k2_funct_1(sK4) != X0
    | sK2 != X2
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_494,c_37])).

cnf(c_1385,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_xboole_0(sK3) ),
    inference(unflattening,[status(thm)],[c_1384])).

cnf(c_2737,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1385])).

cnf(c_43,plain,
    ( v1_funct_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_45,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_1386,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1385])).

cnf(c_18,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(k2_funct_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_3072,plain,
    ( v1_funct_1(k2_funct_1(sK4))
    | ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3073,plain,
    ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
    | v1_funct_1(sK4) != iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3072])).

cnf(c_3088,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
    | v1_relat_1(sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3087])).

cnf(c_3129,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2737,c_43,c_45,c_1386,c_3073,c_3088])).

cnf(c_3836,plain,
    ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_2757,c_3129])).

cnf(c_4573,plain,
    ( v1_xboole_0(k2_funct_1(sK4)) != iProver_top
    | v1_xboole_0(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4158,c_3836])).

cnf(c_4583,plain,
    ( ~ v1_xboole_0(k2_funct_1(sK4))
    | ~ v1_xboole_0(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4573])).

cnf(c_5183,plain,
    ( sK3 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4911,c_5,c_3092,c_4044,c_4583])).

cnf(c_6031,plain,
    ( k1_relat_1(sK4) = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5892,c_5,c_3092,c_4044,c_4583,c_4911])).

cnf(c_4914,plain,
    ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
    inference(demodulation,[status(thm)],[c_4888,c_3100])).

cnf(c_34,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_2747,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_5084,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k2_relat_1(k2_funct_1(sK4))))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4914,c_2747])).

cnf(c_20,plain,
    ( ~ v2_funct_1(X0)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_529,plain,
    ( ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
    | sK4 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_39])).

cnf(c_530,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(unflattening,[status(thm)],[c_529])).

cnf(c_532,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_530,c_42])).

cnf(c_2742,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_532])).

cnf(c_3096,plain,
    ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2742,c_42,c_40,c_530,c_3087])).

cnf(c_5089,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_5084,c_3096])).

cnf(c_3080,plain,
    ( v1_funct_1(sK4) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) = iProver_top
    | v1_relat_1(sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3079])).

cnf(c_5920,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5089,c_43,c_45,c_3073,c_3080,c_3088])).

cnf(c_6036,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6031,c_5920])).

cnf(c_35,plain,
    ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1506,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(X0)
    | k2_funct_1(sK4) != X0
    | k1_relat_1(X0) != sK3
    | k2_relat_1(X0) != sK2 ),
    inference(resolution_lifted,[status(thm)],[c_35,c_37])).

cnf(c_1507,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | ~ v1_relat_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(unflattening,[status(thm)],[c_1506])).

cnf(c_1519,plain,
    ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
    | ~ v1_funct_1(k2_funct_1(sK4))
    | k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1507,c_22])).

cnf(c_2731,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1519])).

cnf(c_1508,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | v1_funct_1(k2_funct_1(sK4)) != iProver_top
    | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1507])).

cnf(c_3160,plain,
    ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2731,c_43,c_45,c_1508,c_3073,c_3080,c_3088])).

cnf(c_3161,plain,
    ( k1_relat_1(k2_funct_1(sK4)) != sK3
    | k2_relat_1(k2_funct_1(sK4)) != sK2
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(renaming,[status(thm)],[c_3160])).

cnf(c_3164,plain,
    ( k1_relat_1(sK4) != sK2
    | k2_relat_1(sK4) != sK3
    | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_3161,c_3096,c_3100])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6036,c_5892,c_5183,c_4888,c_3164])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:28:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 3.06/0.99  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/0.99  
% 3.06/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.06/0.99  
% 3.06/0.99  ------  iProver source info
% 3.06/0.99  
% 3.06/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.06/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.06/0.99  git: non_committed_changes: false
% 3.06/0.99  git: last_make_outside_of_git: false
% 3.06/0.99  
% 3.06/0.99  ------ 
% 3.06/0.99  
% 3.06/0.99  ------ Input Options
% 3.06/0.99  
% 3.06/0.99  --out_options                           all
% 3.06/0.99  --tptp_safe_out                         true
% 3.06/0.99  --problem_path                          ""
% 3.06/0.99  --include_path                          ""
% 3.06/0.99  --clausifier                            res/vclausify_rel
% 3.06/0.99  --clausifier_options                    --mode clausify
% 3.06/0.99  --stdin                                 false
% 3.06/0.99  --stats_out                             all
% 3.06/0.99  
% 3.06/0.99  ------ General Options
% 3.06/0.99  
% 3.06/0.99  --fof                                   false
% 3.06/0.99  --time_out_real                         305.
% 3.06/0.99  --time_out_virtual                      -1.
% 3.06/0.99  --symbol_type_check                     false
% 3.06/0.99  --clausify_out                          false
% 3.06/0.99  --sig_cnt_out                           false
% 3.06/0.99  --trig_cnt_out                          false
% 3.06/0.99  --trig_cnt_out_tolerance                1.
% 3.06/0.99  --trig_cnt_out_sk_spl                   false
% 3.06/0.99  --abstr_cl_out                          false
% 3.06/0.99  
% 3.06/0.99  ------ Global Options
% 3.06/0.99  
% 3.06/0.99  --schedule                              default
% 3.06/0.99  --add_important_lit                     false
% 3.06/0.99  --prop_solver_per_cl                    1000
% 3.06/0.99  --min_unsat_core                        false
% 3.06/0.99  --soft_assumptions                      false
% 3.06/0.99  --soft_lemma_size                       3
% 3.06/0.99  --prop_impl_unit_size                   0
% 3.06/0.99  --prop_impl_unit                        []
% 3.06/0.99  --share_sel_clauses                     true
% 3.06/0.99  --reset_solvers                         false
% 3.06/0.99  --bc_imp_inh                            [conj_cone]
% 3.06/0.99  --conj_cone_tolerance                   3.
% 3.06/0.99  --extra_neg_conj                        none
% 3.06/0.99  --large_theory_mode                     true
% 3.06/0.99  --prolific_symb_bound                   200
% 3.06/0.99  --lt_threshold                          2000
% 3.06/0.99  --clause_weak_htbl                      true
% 3.06/0.99  --gc_record_bc_elim                     false
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing Options
% 3.06/0.99  
% 3.06/0.99  --preprocessing_flag                    true
% 3.06/0.99  --time_out_prep_mult                    0.1
% 3.06/0.99  --splitting_mode                        input
% 3.06/0.99  --splitting_grd                         true
% 3.06/0.99  --splitting_cvd                         false
% 3.06/0.99  --splitting_cvd_svl                     false
% 3.06/0.99  --splitting_nvd                         32
% 3.06/0.99  --sub_typing                            true
% 3.06/0.99  --prep_gs_sim                           true
% 3.06/0.99  --prep_unflatten                        true
% 3.06/0.99  --prep_res_sim                          true
% 3.06/0.99  --prep_upred                            true
% 3.06/0.99  --prep_sem_filter                       exhaustive
% 3.06/0.99  --prep_sem_filter_out                   false
% 3.06/0.99  --pred_elim                             true
% 3.06/0.99  --res_sim_input                         true
% 3.06/0.99  --eq_ax_congr_red                       true
% 3.06/0.99  --pure_diseq_elim                       true
% 3.06/0.99  --brand_transform                       false
% 3.06/0.99  --non_eq_to_eq                          false
% 3.06/0.99  --prep_def_merge                        true
% 3.06/0.99  --prep_def_merge_prop_impl              false
% 3.06/0.99  --prep_def_merge_mbd                    true
% 3.06/0.99  --prep_def_merge_tr_red                 false
% 3.06/0.99  --prep_def_merge_tr_cl                  false
% 3.06/0.99  --smt_preprocessing                     true
% 3.06/0.99  --smt_ac_axioms                         fast
% 3.06/0.99  --preprocessed_out                      false
% 3.06/0.99  --preprocessed_stats                    false
% 3.06/0.99  
% 3.06/0.99  ------ Abstraction refinement Options
% 3.06/0.99  
% 3.06/0.99  --abstr_ref                             []
% 3.06/0.99  --abstr_ref_prep                        false
% 3.06/0.99  --abstr_ref_until_sat                   false
% 3.06/0.99  --abstr_ref_sig_restrict                funpre
% 3.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/0.99  --abstr_ref_under                       []
% 3.06/0.99  
% 3.06/0.99  ------ SAT Options
% 3.06/0.99  
% 3.06/0.99  --sat_mode                              false
% 3.06/0.99  --sat_fm_restart_options                ""
% 3.06/0.99  --sat_gr_def                            false
% 3.06/0.99  --sat_epr_types                         true
% 3.06/0.99  --sat_non_cyclic_types                  false
% 3.06/0.99  --sat_finite_models                     false
% 3.06/0.99  --sat_fm_lemmas                         false
% 3.06/0.99  --sat_fm_prep                           false
% 3.06/0.99  --sat_fm_uc_incr                        true
% 3.06/0.99  --sat_out_model                         small
% 3.06/0.99  --sat_out_clauses                       false
% 3.06/0.99  
% 3.06/0.99  ------ QBF Options
% 3.06/0.99  
% 3.06/0.99  --qbf_mode                              false
% 3.06/0.99  --qbf_elim_univ                         false
% 3.06/0.99  --qbf_dom_inst                          none
% 3.06/0.99  --qbf_dom_pre_inst                      false
% 3.06/0.99  --qbf_sk_in                             false
% 3.06/0.99  --qbf_pred_elim                         true
% 3.06/0.99  --qbf_split                             512
% 3.06/0.99  
% 3.06/0.99  ------ BMC1 Options
% 3.06/0.99  
% 3.06/0.99  --bmc1_incremental                      false
% 3.06/0.99  --bmc1_axioms                           reachable_all
% 3.06/0.99  --bmc1_min_bound                        0
% 3.06/0.99  --bmc1_max_bound                        -1
% 3.06/0.99  --bmc1_max_bound_default                -1
% 3.06/0.99  --bmc1_symbol_reachability              true
% 3.06/0.99  --bmc1_property_lemmas                  false
% 3.06/0.99  --bmc1_k_induction                      false
% 3.06/0.99  --bmc1_non_equiv_states                 false
% 3.06/0.99  --bmc1_deadlock                         false
% 3.06/0.99  --bmc1_ucm                              false
% 3.06/0.99  --bmc1_add_unsat_core                   none
% 3.06/0.99  --bmc1_unsat_core_children              false
% 3.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/0.99  --bmc1_out_stat                         full
% 3.06/0.99  --bmc1_ground_init                      false
% 3.06/0.99  --bmc1_pre_inst_next_state              false
% 3.06/0.99  --bmc1_pre_inst_state                   false
% 3.06/0.99  --bmc1_pre_inst_reach_state             false
% 3.06/0.99  --bmc1_out_unsat_core                   false
% 3.06/0.99  --bmc1_aig_witness_out                  false
% 3.06/0.99  --bmc1_verbose                          false
% 3.06/0.99  --bmc1_dump_clauses_tptp                false
% 3.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.06/0.99  --bmc1_dump_file                        -
% 3.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.06/0.99  --bmc1_ucm_extend_mode                  1
% 3.06/0.99  --bmc1_ucm_init_mode                    2
% 3.06/0.99  --bmc1_ucm_cone_mode                    none
% 3.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.06/0.99  --bmc1_ucm_relax_model                  4
% 3.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/0.99  --bmc1_ucm_layered_model                none
% 3.06/0.99  --bmc1_ucm_max_lemma_size               10
% 3.06/0.99  
% 3.06/0.99  ------ AIG Options
% 3.06/0.99  
% 3.06/0.99  --aig_mode                              false
% 3.06/0.99  
% 3.06/0.99  ------ Instantiation Options
% 3.06/0.99  
% 3.06/0.99  --instantiation_flag                    true
% 3.06/0.99  --inst_sos_flag                         false
% 3.06/0.99  --inst_sos_phase                        true
% 3.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/0.99  --inst_lit_sel_side                     num_symb
% 3.06/0.99  --inst_solver_per_active                1400
% 3.06/0.99  --inst_solver_calls_frac                1.
% 3.06/0.99  --inst_passive_queue_type               priority_queues
% 3.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/0.99  --inst_passive_queues_freq              [25;2]
% 3.06/0.99  --inst_dismatching                      true
% 3.06/0.99  --inst_eager_unprocessed_to_passive     true
% 3.06/0.99  --inst_prop_sim_given                   true
% 3.06/0.99  --inst_prop_sim_new                     false
% 3.06/0.99  --inst_subs_new                         false
% 3.06/0.99  --inst_eq_res_simp                      false
% 3.06/0.99  --inst_subs_given                       false
% 3.06/0.99  --inst_orphan_elimination               true
% 3.06/0.99  --inst_learning_loop_flag               true
% 3.06/0.99  --inst_learning_start                   3000
% 3.06/0.99  --inst_learning_factor                  2
% 3.06/0.99  --inst_start_prop_sim_after_learn       3
% 3.06/0.99  --inst_sel_renew                        solver
% 3.06/0.99  --inst_lit_activity_flag                true
% 3.06/0.99  --inst_restr_to_given                   false
% 3.06/0.99  --inst_activity_threshold               500
% 3.06/0.99  --inst_out_proof                        true
% 3.06/0.99  
% 3.06/0.99  ------ Resolution Options
% 3.06/0.99  
% 3.06/0.99  --resolution_flag                       true
% 3.06/0.99  --res_lit_sel                           adaptive
% 3.06/0.99  --res_lit_sel_side                      none
% 3.06/0.99  --res_ordering                          kbo
% 3.06/0.99  --res_to_prop_solver                    active
% 3.06/0.99  --res_prop_simpl_new                    false
% 3.06/0.99  --res_prop_simpl_given                  true
% 3.06/0.99  --res_passive_queue_type                priority_queues
% 3.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/0.99  --res_passive_queues_freq               [15;5]
% 3.06/0.99  --res_forward_subs                      full
% 3.06/0.99  --res_backward_subs                     full
% 3.06/0.99  --res_forward_subs_resolution           true
% 3.06/0.99  --res_backward_subs_resolution          true
% 3.06/0.99  --res_orphan_elimination                true
% 3.06/0.99  --res_time_limit                        2.
% 3.06/0.99  --res_out_proof                         true
% 3.06/0.99  
% 3.06/0.99  ------ Superposition Options
% 3.06/0.99  
% 3.06/0.99  --superposition_flag                    true
% 3.06/0.99  --sup_passive_queue_type                priority_queues
% 3.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.06/0.99  --demod_completeness_check              fast
% 3.06/0.99  --demod_use_ground                      true
% 3.06/0.99  --sup_to_prop_solver                    passive
% 3.06/0.99  --sup_prop_simpl_new                    true
% 3.06/0.99  --sup_prop_simpl_given                  true
% 3.06/0.99  --sup_fun_splitting                     false
% 3.06/0.99  --sup_smt_interval                      50000
% 3.06/0.99  
% 3.06/0.99  ------ Superposition Simplification Setup
% 3.06/0.99  
% 3.06/0.99  --sup_indices_passive                   []
% 3.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_full_bw                           [BwDemod]
% 3.06/0.99  --sup_immed_triv                        [TrivRules]
% 3.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_immed_bw_main                     []
% 3.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.99  
% 3.06/0.99  ------ Combination Options
% 3.06/0.99  
% 3.06/0.99  --comb_res_mult                         3
% 3.06/0.99  --comb_sup_mult                         2
% 3.06/0.99  --comb_inst_mult                        10
% 3.06/0.99  
% 3.06/0.99  ------ Debug Options
% 3.06/0.99  
% 3.06/0.99  --dbg_backtrace                         false
% 3.06/0.99  --dbg_dump_prop_clauses                 false
% 3.06/0.99  --dbg_dump_prop_clauses_file            -
% 3.06/0.99  --dbg_out_stat                          false
% 3.06/0.99  ------ Parsing...
% 3.06/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.06/0.99  ------ Proving...
% 3.06/0.99  ------ Problem Properties 
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  clauses                                 41
% 3.06/0.99  conjectures                             3
% 3.06/0.99  EPR                                     7
% 3.06/0.99  Horn                                    33
% 3.06/0.99  unary                                   7
% 3.06/0.99  binary                                  13
% 3.06/0.99  lits                                    109
% 3.06/0.99  lits eq                                 39
% 3.06/0.99  fd_pure                                 0
% 3.06/0.99  fd_pseudo                               0
% 3.06/0.99  fd_cond                                 4
% 3.06/0.99  fd_pseudo_cond                          1
% 3.06/0.99  AC symbols                              0
% 3.06/0.99  
% 3.06/0.99  ------ Schedule dynamic 5 is on 
% 3.06/0.99  
% 3.06/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  ------ 
% 3.06/0.99  Current options:
% 3.06/0.99  ------ 
% 3.06/0.99  
% 3.06/0.99  ------ Input Options
% 3.06/0.99  
% 3.06/0.99  --out_options                           all
% 3.06/0.99  --tptp_safe_out                         true
% 3.06/0.99  --problem_path                          ""
% 3.06/0.99  --include_path                          ""
% 3.06/0.99  --clausifier                            res/vclausify_rel
% 3.06/0.99  --clausifier_options                    --mode clausify
% 3.06/0.99  --stdin                                 false
% 3.06/0.99  --stats_out                             all
% 3.06/0.99  
% 3.06/0.99  ------ General Options
% 3.06/0.99  
% 3.06/0.99  --fof                                   false
% 3.06/0.99  --time_out_real                         305.
% 3.06/0.99  --time_out_virtual                      -1.
% 3.06/0.99  --symbol_type_check                     false
% 3.06/0.99  --clausify_out                          false
% 3.06/0.99  --sig_cnt_out                           false
% 3.06/0.99  --trig_cnt_out                          false
% 3.06/0.99  --trig_cnt_out_tolerance                1.
% 3.06/0.99  --trig_cnt_out_sk_spl                   false
% 3.06/0.99  --abstr_cl_out                          false
% 3.06/0.99  
% 3.06/0.99  ------ Global Options
% 3.06/0.99  
% 3.06/0.99  --schedule                              default
% 3.06/0.99  --add_important_lit                     false
% 3.06/0.99  --prop_solver_per_cl                    1000
% 3.06/0.99  --min_unsat_core                        false
% 3.06/0.99  --soft_assumptions                      false
% 3.06/0.99  --soft_lemma_size                       3
% 3.06/0.99  --prop_impl_unit_size                   0
% 3.06/0.99  --prop_impl_unit                        []
% 3.06/0.99  --share_sel_clauses                     true
% 3.06/0.99  --reset_solvers                         false
% 3.06/0.99  --bc_imp_inh                            [conj_cone]
% 3.06/0.99  --conj_cone_tolerance                   3.
% 3.06/0.99  --extra_neg_conj                        none
% 3.06/0.99  --large_theory_mode                     true
% 3.06/0.99  --prolific_symb_bound                   200
% 3.06/0.99  --lt_threshold                          2000
% 3.06/0.99  --clause_weak_htbl                      true
% 3.06/0.99  --gc_record_bc_elim                     false
% 3.06/0.99  
% 3.06/0.99  ------ Preprocessing Options
% 3.06/0.99  
% 3.06/0.99  --preprocessing_flag                    true
% 3.06/0.99  --time_out_prep_mult                    0.1
% 3.06/0.99  --splitting_mode                        input
% 3.06/0.99  --splitting_grd                         true
% 3.06/0.99  --splitting_cvd                         false
% 3.06/0.99  --splitting_cvd_svl                     false
% 3.06/0.99  --splitting_nvd                         32
% 3.06/0.99  --sub_typing                            true
% 3.06/0.99  --prep_gs_sim                           true
% 3.06/0.99  --prep_unflatten                        true
% 3.06/0.99  --prep_res_sim                          true
% 3.06/0.99  --prep_upred                            true
% 3.06/0.99  --prep_sem_filter                       exhaustive
% 3.06/0.99  --prep_sem_filter_out                   false
% 3.06/0.99  --pred_elim                             true
% 3.06/0.99  --res_sim_input                         true
% 3.06/0.99  --eq_ax_congr_red                       true
% 3.06/0.99  --pure_diseq_elim                       true
% 3.06/0.99  --brand_transform                       false
% 3.06/0.99  --non_eq_to_eq                          false
% 3.06/0.99  --prep_def_merge                        true
% 3.06/0.99  --prep_def_merge_prop_impl              false
% 3.06/0.99  --prep_def_merge_mbd                    true
% 3.06/0.99  --prep_def_merge_tr_red                 false
% 3.06/0.99  --prep_def_merge_tr_cl                  false
% 3.06/0.99  --smt_preprocessing                     true
% 3.06/0.99  --smt_ac_axioms                         fast
% 3.06/0.99  --preprocessed_out                      false
% 3.06/0.99  --preprocessed_stats                    false
% 3.06/0.99  
% 3.06/0.99  ------ Abstraction refinement Options
% 3.06/0.99  
% 3.06/0.99  --abstr_ref                             []
% 3.06/0.99  --abstr_ref_prep                        false
% 3.06/0.99  --abstr_ref_until_sat                   false
% 3.06/0.99  --abstr_ref_sig_restrict                funpre
% 3.06/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.06/0.99  --abstr_ref_under                       []
% 3.06/0.99  
% 3.06/0.99  ------ SAT Options
% 3.06/0.99  
% 3.06/0.99  --sat_mode                              false
% 3.06/0.99  --sat_fm_restart_options                ""
% 3.06/0.99  --sat_gr_def                            false
% 3.06/0.99  --sat_epr_types                         true
% 3.06/0.99  --sat_non_cyclic_types                  false
% 3.06/0.99  --sat_finite_models                     false
% 3.06/0.99  --sat_fm_lemmas                         false
% 3.06/0.99  --sat_fm_prep                           false
% 3.06/0.99  --sat_fm_uc_incr                        true
% 3.06/0.99  --sat_out_model                         small
% 3.06/0.99  --sat_out_clauses                       false
% 3.06/0.99  
% 3.06/0.99  ------ QBF Options
% 3.06/0.99  
% 3.06/0.99  --qbf_mode                              false
% 3.06/0.99  --qbf_elim_univ                         false
% 3.06/0.99  --qbf_dom_inst                          none
% 3.06/0.99  --qbf_dom_pre_inst                      false
% 3.06/0.99  --qbf_sk_in                             false
% 3.06/0.99  --qbf_pred_elim                         true
% 3.06/0.99  --qbf_split                             512
% 3.06/0.99  
% 3.06/0.99  ------ BMC1 Options
% 3.06/0.99  
% 3.06/0.99  --bmc1_incremental                      false
% 3.06/0.99  --bmc1_axioms                           reachable_all
% 3.06/0.99  --bmc1_min_bound                        0
% 3.06/0.99  --bmc1_max_bound                        -1
% 3.06/0.99  --bmc1_max_bound_default                -1
% 3.06/0.99  --bmc1_symbol_reachability              true
% 3.06/0.99  --bmc1_property_lemmas                  false
% 3.06/0.99  --bmc1_k_induction                      false
% 3.06/0.99  --bmc1_non_equiv_states                 false
% 3.06/0.99  --bmc1_deadlock                         false
% 3.06/0.99  --bmc1_ucm                              false
% 3.06/0.99  --bmc1_add_unsat_core                   none
% 3.06/0.99  --bmc1_unsat_core_children              false
% 3.06/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.06/0.99  --bmc1_out_stat                         full
% 3.06/0.99  --bmc1_ground_init                      false
% 3.06/0.99  --bmc1_pre_inst_next_state              false
% 3.06/0.99  --bmc1_pre_inst_state                   false
% 3.06/0.99  --bmc1_pre_inst_reach_state             false
% 3.06/0.99  --bmc1_out_unsat_core                   false
% 3.06/0.99  --bmc1_aig_witness_out                  false
% 3.06/0.99  --bmc1_verbose                          false
% 3.06/0.99  --bmc1_dump_clauses_tptp                false
% 3.06/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.06/0.99  --bmc1_dump_file                        -
% 3.06/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.06/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.06/0.99  --bmc1_ucm_extend_mode                  1
% 3.06/0.99  --bmc1_ucm_init_mode                    2
% 3.06/0.99  --bmc1_ucm_cone_mode                    none
% 3.06/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.06/0.99  --bmc1_ucm_relax_model                  4
% 3.06/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.06/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.06/0.99  --bmc1_ucm_layered_model                none
% 3.06/0.99  --bmc1_ucm_max_lemma_size               10
% 3.06/0.99  
% 3.06/0.99  ------ AIG Options
% 3.06/0.99  
% 3.06/0.99  --aig_mode                              false
% 3.06/0.99  
% 3.06/0.99  ------ Instantiation Options
% 3.06/0.99  
% 3.06/0.99  --instantiation_flag                    true
% 3.06/0.99  --inst_sos_flag                         false
% 3.06/0.99  --inst_sos_phase                        true
% 3.06/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.06/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.06/0.99  --inst_lit_sel_side                     none
% 3.06/0.99  --inst_solver_per_active                1400
% 3.06/0.99  --inst_solver_calls_frac                1.
% 3.06/0.99  --inst_passive_queue_type               priority_queues
% 3.06/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.06/0.99  --inst_passive_queues_freq              [25;2]
% 3.06/0.99  --inst_dismatching                      true
% 3.06/0.99  --inst_eager_unprocessed_to_passive     true
% 3.06/0.99  --inst_prop_sim_given                   true
% 3.06/0.99  --inst_prop_sim_new                     false
% 3.06/0.99  --inst_subs_new                         false
% 3.06/0.99  --inst_eq_res_simp                      false
% 3.06/0.99  --inst_subs_given                       false
% 3.06/0.99  --inst_orphan_elimination               true
% 3.06/0.99  --inst_learning_loop_flag               true
% 3.06/0.99  --inst_learning_start                   3000
% 3.06/0.99  --inst_learning_factor                  2
% 3.06/0.99  --inst_start_prop_sim_after_learn       3
% 3.06/0.99  --inst_sel_renew                        solver
% 3.06/0.99  --inst_lit_activity_flag                true
% 3.06/0.99  --inst_restr_to_given                   false
% 3.06/0.99  --inst_activity_threshold               500
% 3.06/0.99  --inst_out_proof                        true
% 3.06/0.99  
% 3.06/0.99  ------ Resolution Options
% 3.06/0.99  
% 3.06/0.99  --resolution_flag                       false
% 3.06/0.99  --res_lit_sel                           adaptive
% 3.06/0.99  --res_lit_sel_side                      none
% 3.06/0.99  --res_ordering                          kbo
% 3.06/0.99  --res_to_prop_solver                    active
% 3.06/0.99  --res_prop_simpl_new                    false
% 3.06/0.99  --res_prop_simpl_given                  true
% 3.06/0.99  --res_passive_queue_type                priority_queues
% 3.06/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.06/0.99  --res_passive_queues_freq               [15;5]
% 3.06/0.99  --res_forward_subs                      full
% 3.06/0.99  --res_backward_subs                     full
% 3.06/0.99  --res_forward_subs_resolution           true
% 3.06/0.99  --res_backward_subs_resolution          true
% 3.06/0.99  --res_orphan_elimination                true
% 3.06/0.99  --res_time_limit                        2.
% 3.06/0.99  --res_out_proof                         true
% 3.06/0.99  
% 3.06/0.99  ------ Superposition Options
% 3.06/0.99  
% 3.06/0.99  --superposition_flag                    true
% 3.06/0.99  --sup_passive_queue_type                priority_queues
% 3.06/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.06/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.06/0.99  --demod_completeness_check              fast
% 3.06/0.99  --demod_use_ground                      true
% 3.06/0.99  --sup_to_prop_solver                    passive
% 3.06/0.99  --sup_prop_simpl_new                    true
% 3.06/0.99  --sup_prop_simpl_given                  true
% 3.06/0.99  --sup_fun_splitting                     false
% 3.06/0.99  --sup_smt_interval                      50000
% 3.06/0.99  
% 3.06/0.99  ------ Superposition Simplification Setup
% 3.06/0.99  
% 3.06/0.99  --sup_indices_passive                   []
% 3.06/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.06/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.06/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_full_bw                           [BwDemod]
% 3.06/0.99  --sup_immed_triv                        [TrivRules]
% 3.06/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.06/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_immed_bw_main                     []
% 3.06/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.06/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.06/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.06/0.99  
% 3.06/0.99  ------ Combination Options
% 3.06/0.99  
% 3.06/0.99  --comb_res_mult                         3
% 3.06/0.99  --comb_sup_mult                         2
% 3.06/0.99  --comb_inst_mult                        10
% 3.06/0.99  
% 3.06/0.99  ------ Debug Options
% 3.06/0.99  
% 3.06/0.99  --dbg_backtrace                         false
% 3.06/0.99  --dbg_dump_prop_clauses                 false
% 3.06/0.99  --dbg_dump_prop_clauses_file            -
% 3.06/0.99  --dbg_out_stat                          false
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  ------ Proving...
% 3.06/0.99  
% 3.06/0.99  
% 3.06/0.99  % SZS status Theorem for theBenchmark.p
% 3.06/0.99  
% 3.06/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.06/0.99  
% 3.06/0.99  fof(f19,conjecture,(
% 3.06/0.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f20,negated_conjecture,(
% 3.06/0.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 3.06/0.99    inference(negated_conjecture,[],[f19])).
% 3.06/0.99  
% 3.06/0.99  fof(f40,plain,(
% 3.06/0.99    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 3.06/0.99    inference(ennf_transformation,[],[f20])).
% 3.06/0.99  
% 3.06/0.99  fof(f41,plain,(
% 3.06/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 3.06/0.99    inference(flattening,[],[f40])).
% 3.06/0.99  
% 3.06/0.99  fof(f56,plain,(
% 3.06/0.99    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4))),
% 3.06/0.99    introduced(choice_axiom,[])).
% 3.06/0.99  
% 3.06/0.99  fof(f57,plain,(
% 3.06/0.99    (~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))) & k2_relset_1(sK2,sK3,sK4) = sK3 & v2_funct_1(sK4) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK4,sK2,sK3) & v1_funct_1(sK4)),
% 3.06/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f56])).
% 3.06/0.99  
% 3.06/0.99  fof(f97,plain,(
% 3.06/0.99    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.06/0.99    inference(cnf_transformation,[],[f57])).
% 3.06/0.99  
% 3.06/0.99  fof(f16,axiom,(
% 3.06/0.99    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f35,plain,(
% 3.06/0.99    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 3.06/0.99    inference(ennf_transformation,[],[f16])).
% 3.06/0.99  
% 3.06/0.99  fof(f85,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 3.06/0.99    inference(cnf_transformation,[],[f35])).
% 3.06/0.99  
% 3.06/0.99  fof(f15,axiom,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_partfun1(X2,X0) & v1_funct_1(X2)) => (v1_funct_2(X2,X0,X1) & v1_funct_1(X2))))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f33,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | (~v1_partfun1(X2,X0) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(ennf_transformation,[],[f15])).
% 3.06/0.99  
% 3.06/0.99  fof(f34,plain,(
% 3.06/0.99    ! [X0,X1,X2] : ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(flattening,[],[f33])).
% 3.06/0.99  
% 3.06/0.99  fof(f84,plain,(
% 3.06/0.99    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | ~v1_partfun1(X2,X0) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/0.99    inference(cnf_transformation,[],[f34])).
% 3.06/0.99  
% 3.06/0.99  fof(f17,axiom,(
% 3.06/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.06/0.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/0.99  
% 3.06/0.99  fof(f36,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(ennf_transformation,[],[f17])).
% 3.06/0.99  
% 3.06/0.99  fof(f37,plain,(
% 3.06/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/0.99    inference(flattening,[],[f36])).
% 3.06/0.99  
% 3.06/0.99  fof(f55,plain,(
% 3.06/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(nnf_transformation,[],[f37])).
% 3.06/1.00  
% 3.06/1.00  fof(f86,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f55])).
% 3.06/1.00  
% 3.06/1.00  fof(f96,plain,(
% 3.06/1.00    v1_funct_2(sK4,sK2,sK3)),
% 3.06/1.00    inference(cnf_transformation,[],[f57])).
% 3.06/1.00  
% 3.06/1.00  fof(f13,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f31,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f13])).
% 3.06/1.00  
% 3.06/1.00  fof(f81,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f31])).
% 3.06/1.00  
% 3.06/1.00  fof(f14,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f32,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f14])).
% 3.06/1.00  
% 3.06/1.00  fof(f82,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f32])).
% 3.06/1.00  
% 3.06/1.00  fof(f99,plain,(
% 3.06/1.00    k2_relset_1(sK2,sK3,sK4) = sK3),
% 3.06/1.00    inference(cnf_transformation,[],[f57])).
% 3.06/1.00  
% 3.06/1.00  fof(f11,axiom,(
% 3.06/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f28,plain,(
% 3.06/1.00    ! [X0] : (((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.06/1.00    inference(ennf_transformation,[],[f11])).
% 3.06/1.00  
% 3.06/1.00  fof(f29,plain,(
% 3.06/1.00    ! [X0] : ((k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/1.00    inference(flattening,[],[f28])).
% 3.06/1.00  
% 3.06/1.00  fof(f78,plain,(
% 3.06/1.00    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f29])).
% 3.06/1.00  
% 3.06/1.00  fof(f98,plain,(
% 3.06/1.00    v2_funct_1(sK4)),
% 3.06/1.00    inference(cnf_transformation,[],[f57])).
% 3.06/1.00  
% 3.06/1.00  fof(f95,plain,(
% 3.06/1.00    v1_funct_1(sK4)),
% 3.06/1.00    inference(cnf_transformation,[],[f57])).
% 3.06/1.00  
% 3.06/1.00  fof(f12,axiom,(
% 3.06/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f30,plain,(
% 3.06/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.06/1.00    inference(ennf_transformation,[],[f12])).
% 3.06/1.00  
% 3.06/1.00  fof(f80,plain,(
% 3.06/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.06/1.00    inference(cnf_transformation,[],[f30])).
% 3.06/1.00  
% 3.06/1.00  fof(f9,axiom,(
% 3.06/1.00    ! [X0] : (v1_relat_1(X0) => ((k1_xboole_0 = k2_relat_1(X0) | k1_xboole_0 = k1_relat_1(X0)) => k1_xboole_0 = X0))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f24,plain,(
% 3.06/1.00    ! [X0] : ((k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 3.06/1.00    inference(ennf_transformation,[],[f9])).
% 3.06/1.00  
% 3.06/1.00  fof(f25,plain,(
% 3.06/1.00    ! [X0] : (k1_xboole_0 = X0 | (k1_xboole_0 != k2_relat_1(X0) & k1_xboole_0 != k1_relat_1(X0)) | ~v1_relat_1(X0))),
% 3.06/1.00    inference(flattening,[],[f24])).
% 3.06/1.00  
% 3.06/1.00  fof(f74,plain,(
% 3.06/1.00    ( ! [X0] : (k1_xboole_0 = X0 | k1_xboole_0 != k1_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f25])).
% 3.06/1.00  
% 3.06/1.00  fof(f10,axiom,(
% 3.06/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f26,plain,(
% 3.06/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.06/1.00    inference(ennf_transformation,[],[f10])).
% 3.06/1.00  
% 3.06/1.00  fof(f27,plain,(
% 3.06/1.00    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/1.00    inference(flattening,[],[f26])).
% 3.06/1.00  
% 3.06/1.00  fof(f76,plain,(
% 3.06/1.00    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f27])).
% 3.06/1.00  
% 3.06/1.00  fof(f3,axiom,(
% 3.06/1.00    v1_xboole_0(k1_xboole_0)),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f63,plain,(
% 3.06/1.00    v1_xboole_0(k1_xboole_0)),
% 3.06/1.00    inference(cnf_transformation,[],[f3])).
% 3.06/1.00  
% 3.06/1.00  fof(f2,axiom,(
% 3.06/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f21,plain,(
% 3.06/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.06/1.00    inference(ennf_transformation,[],[f2])).
% 3.06/1.00  
% 3.06/1.00  fof(f46,plain,(
% 3.06/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.06/1.00    inference(nnf_transformation,[],[f21])).
% 3.06/1.00  
% 3.06/1.00  fof(f47,plain,(
% 3.06/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.06/1.00    inference(rectify,[],[f46])).
% 3.06/1.00  
% 3.06/1.00  fof(f48,plain,(
% 3.06/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.06/1.00    introduced(choice_axiom,[])).
% 3.06/1.00  
% 3.06/1.00  fof(f49,plain,(
% 3.06/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f47,f48])).
% 3.06/1.00  
% 3.06/1.00  fof(f61,plain,(
% 3.06/1.00    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f49])).
% 3.06/1.00  
% 3.06/1.00  fof(f1,axiom,(
% 3.06/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f42,plain,(
% 3.06/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.06/1.00    inference(nnf_transformation,[],[f1])).
% 3.06/1.00  
% 3.06/1.00  fof(f43,plain,(
% 3.06/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.06/1.00    inference(rectify,[],[f42])).
% 3.06/1.00  
% 3.06/1.00  fof(f44,plain,(
% 3.06/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.06/1.00    introduced(choice_axiom,[])).
% 3.06/1.00  
% 3.06/1.00  fof(f45,plain,(
% 3.06/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.06/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f43,f44])).
% 3.06/1.00  
% 3.06/1.00  fof(f58,plain,(
% 3.06/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f45])).
% 3.06/1.00  
% 3.06/1.00  fof(f7,axiom,(
% 3.06/1.00    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f54,plain,(
% 3.06/1.00    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.06/1.00    inference(nnf_transformation,[],[f7])).
% 3.06/1.00  
% 3.06/1.00  fof(f72,plain,(
% 3.06/1.00    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f54])).
% 3.06/1.00  
% 3.06/1.00  fof(f100,plain,(
% 3.06/1.00    ~m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) | ~v1_funct_2(k2_funct_1(sK4),sK3,sK2) | ~v1_funct_1(k2_funct_1(sK4))),
% 3.06/1.00    inference(cnf_transformation,[],[f57])).
% 3.06/1.00  
% 3.06/1.00  fof(f77,plain,(
% 3.06/1.00    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f27])).
% 3.06/1.00  
% 3.06/1.00  fof(f18,axiom,(
% 3.06/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 3.06/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.06/1.00  
% 3.06/1.00  fof(f38,plain,(
% 3.06/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.06/1.00    inference(ennf_transformation,[],[f18])).
% 3.06/1.00  
% 3.06/1.00  fof(f39,plain,(
% 3.06/1.00    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.06/1.00    inference(flattening,[],[f38])).
% 3.06/1.00  
% 3.06/1.00  fof(f94,plain,(
% 3.06/1.00    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f39])).
% 3.06/1.00  
% 3.06/1.00  fof(f79,plain,(
% 3.06/1.00    ( ! [X0] : (k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f29])).
% 3.06/1.00  
% 3.06/1.00  fof(f93,plain,(
% 3.06/1.00    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.06/1.00    inference(cnf_transformation,[],[f39])).
% 3.06/1.00  
% 3.06/1.00  cnf(c_40,negated_conjecture,
% 3.06/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.06/1.00      inference(cnf_transformation,[],[f97]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2746,plain,
% 3.06/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_27,plain,
% 3.06/1.00      ( v1_partfun1(X0,X1)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_xboole_0(X1) ),
% 3.06/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_25,plain,
% 3.06/1.00      ( v1_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ v1_partfun1(X0,X1)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_489,plain,
% 3.06/1.00      ( v1_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_xboole_0(X1) ),
% 3.06/1.00      inference(resolution,[status(thm)],[c_27,c_25]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_493,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | v1_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_xboole_0(X1) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_489,c_27,c_25]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_494,plain,
% 3.06/1.00      ( v1_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_xboole_0(X1) ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_493]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_33,plain,
% 3.06/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 3.06/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.06/1.00      | k1_xboole_0 = X2 ),
% 3.06/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1288,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_xboole_0(X1)
% 3.06/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.06/1.00      | k1_xboole_0 = X2 ),
% 3.06/1.00      inference(resolution,[status(thm)],[c_494,c_33]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2741,plain,
% 3.06/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 3.06/1.00      | k1_xboole_0 = X1
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.06/1.00      | v1_funct_1(X2) != iProver_top
% 3.06/1.00      | v1_xboole_0(X0) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_1288]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4121,plain,
% 3.06/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2
% 3.06/1.00      | sK3 = k1_xboole_0
% 3.06/1.00      | v1_funct_1(sK4) != iProver_top
% 3.06/1.00      | v1_xboole_0(sK2) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_2746,c_2741]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_41,negated_conjecture,
% 3.06/1.00      ( v1_funct_2(sK4,sK2,sK3) ),
% 3.06/1.00      inference(cnf_transformation,[],[f96]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1413,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k1_relset_1(X1,X2,X0) = X1
% 3.06/1.00      | sK2 != X1
% 3.06/1.00      | sK3 != X2
% 3.06/1.00      | sK4 != X0
% 3.06/1.00      | k1_xboole_0 = X2 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_33,c_41]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1414,plain,
% 3.06/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.06/1.00      | k1_relset_1(sK2,sK3,sK4) = sK2
% 3.06/1.00      | k1_xboole_0 = sK3 ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_1413]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1921,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3123,plain,
% 3.06/1.00      ( sK3 != X0 | sK3 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_1921]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3448,plain,
% 3.06/1.00      ( sK3 != sK3 | sK3 = k1_xboole_0 | k1_xboole_0 != sK3 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_3123]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1920,plain,( X0 = X0 ),theory(equality) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3449,plain,
% 3.06/1.00      ( sK3 = sK3 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_1920]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4251,plain,
% 3.06/1.00      ( k1_relset_1(sK2,sK3,sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_4121,c_40,c_1414,c_3448,c_3449]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_23,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2749,plain,
% 3.06/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5507,plain,
% 3.06/1.00      ( k1_relset_1(sK2,sK3,sK4) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_2746,c_2749]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5892,plain,
% 3.06/1.00      ( k1_relat_1(sK4) = sK2 | sK3 = k1_xboole_0 ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_4251,c_5507]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_24,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2748,plain,
% 3.06/1.00      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.06/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4876,plain,
% 3.06/1.00      ( k2_relset_1(sK2,sK3,sK4) = k2_relat_1(sK4) ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_2746,c_2748]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_38,negated_conjecture,
% 3.06/1.00      ( k2_relset_1(sK2,sK3,sK4) = sK3 ),
% 3.06/1.00      inference(cnf_transformation,[],[f99]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4888,plain,
% 3.06/1.00      ( k2_relat_1(sK4) = sK3 ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_4876,c_38]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_21,plain,
% 3.06/1.00      ( ~ v2_funct_1(X0)
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_relat_1(X0)
% 3.06/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_39,negated_conjecture,
% 3.06/1.00      ( v2_funct_1(sK4) ),
% 3.06/1.00      inference(cnf_transformation,[],[f98]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_515,plain,
% 3.06/1.00      ( ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_relat_1(X0)
% 3.06/1.00      | k1_relat_1(k2_funct_1(X0)) = k2_relat_1(X0)
% 3.06/1.00      | sK4 != X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_21,c_39]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_516,plain,
% 3.06/1.00      ( ~ v1_funct_1(sK4)
% 3.06/1.00      | ~ v1_relat_1(sK4)
% 3.06/1.00      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_515]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_42,negated_conjecture,
% 3.06/1.00      ( v1_funct_1(sK4) ),
% 3.06/1.00      inference(cnf_transformation,[],[f95]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_518,plain,
% 3.06/1.00      ( ~ v1_relat_1(sK4)
% 3.06/1.00      | k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_516,c_42]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2743,plain,
% 3.06/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4)
% 3.06/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_518]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_22,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | v1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3087,plain,
% 3.06/1.00      ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.06/1.00      | v1_relat_1(sK4) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_22]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3100,plain,
% 3.06/1.00      ( k1_relat_1(k2_funct_1(sK4)) = k2_relat_1(sK4) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_2743,c_42,c_40,c_516,c_3087]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_17,plain,
% 3.06/1.00      ( ~ v1_relat_1(X0)
% 3.06/1.00      | k1_relat_1(X0) != k1_xboole_0
% 3.06/1.00      | k1_xboole_0 = X0 ),
% 3.06/1.00      inference(cnf_transformation,[],[f74]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2753,plain,
% 3.06/1.00      ( k1_relat_1(X0) != k1_xboole_0
% 3.06/1.00      | k1_xboole_0 = X0
% 3.06/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4215,plain,
% 3.06/1.00      ( k2_funct_1(sK4) = k1_xboole_0
% 3.06/1.00      | k2_relat_1(sK4) != k1_xboole_0
% 3.06/1.00      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_3100,c_2753]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_19,plain,
% 3.06/1.00      ( ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_relat_1(X0)
% 3.06/1.00      | v1_relat_1(k2_funct_1(X0)) ),
% 3.06/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3079,plain,
% 3.06/1.00      ( ~ v1_funct_1(sK4)
% 3.06/1.00      | v1_relat_1(k2_funct_1(sK4))
% 3.06/1.00      | ~ v1_relat_1(sK4) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_19]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4216,plain,
% 3.06/1.00      ( ~ v1_relat_1(k2_funct_1(sK4))
% 3.06/1.00      | k2_funct_1(sK4) = k1_xboole_0
% 3.06/1.00      | k2_relat_1(sK4) != k1_xboole_0 ),
% 3.06/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4215]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4345,plain,
% 3.06/1.00      ( k2_relat_1(sK4) != k1_xboole_0 | k2_funct_1(sK4) = k1_xboole_0 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_4215,c_42,c_40,c_3079,c_3087,c_4216]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4346,plain,
% 3.06/1.00      ( k2_funct_1(sK4) = k1_xboole_0 | k2_relat_1(sK4) != k1_xboole_0 ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_4345]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4911,plain,
% 3.06/1.00      ( k2_funct_1(sK4) = k1_xboole_0 | sK3 != k1_xboole_0 ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_4888,c_4346]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5,plain,
% 3.06/1.00      ( v1_xboole_0(k1_xboole_0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f63]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1922,plain,
% 3.06/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 3.06/1.00      theory(equality) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3090,plain,
% 3.06/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK3) | sK3 != X0 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_1922]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3092,plain,
% 3.06/1.00      ( v1_xboole_0(sK3)
% 3.06/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.06/1.00      | sK3 != k1_xboole_0 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_3090]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4042,plain,
% 3.06/1.00      ( ~ v1_xboole_0(X0)
% 3.06/1.00      | v1_xboole_0(k2_funct_1(sK4))
% 3.06/1.00      | k2_funct_1(sK4) != X0 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_1922]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4044,plain,
% 3.06/1.00      ( v1_xboole_0(k2_funct_1(sK4))
% 3.06/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 3.06/1.00      | k2_funct_1(sK4) != k1_xboole_0 ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_4042]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3,plain,
% 3.06/1.00      ( r1_tarski(X0,X1) | r2_hidden(sK1(X0,X1),X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f61]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2762,plain,
% 3.06/1.00      ( r1_tarski(X0,X1) = iProver_top
% 3.06/1.00      | r2_hidden(sK1(X0,X1),X0) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1,plain,
% 3.06/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.06/1.00      inference(cnf_transformation,[],[f58]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2764,plain,
% 3.06/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.06/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4158,plain,
% 3.06/1.00      ( r1_tarski(X0,X1) = iProver_top | v1_xboole_0(X0) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_2762,c_2764]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_13,plain,
% 3.06/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.06/1.00      inference(cnf_transformation,[],[f72]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2757,plain,
% 3.06/1.00      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.06/1.00      | r1_tarski(X0,X1) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_37,negated_conjecture,
% 3.06/1.00      ( ~ v1_funct_2(k2_funct_1(sK4),sK3,sK2)
% 3.06/1.00      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.06/1.00      | ~ v1_funct_1(k2_funct_1(sK4)) ),
% 3.06/1.00      inference(cnf_transformation,[],[f100]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1384,plain,
% 3.06/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.06/1.00      | ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.06/1.00      | ~ v1_xboole_0(X1)
% 3.06/1.00      | k2_funct_1(sK4) != X0
% 3.06/1.00      | sK2 != X2
% 3.06/1.00      | sK3 != X1 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_494,c_37]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1385,plain,
% 3.06/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.06/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.06/1.00      | ~ v1_xboole_0(sK3) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_1384]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2737,plain,
% 3.06/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.06/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.06/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_1385]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_43,plain,
% 3.06/1.00      ( v1_funct_1(sK4) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_45,plain,
% 3.06/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1386,plain,
% 3.06/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.06/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.06/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_1385]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_18,plain,
% 3.06/1.00      ( ~ v1_funct_1(X0)
% 3.06/1.00      | v1_funct_1(k2_funct_1(X0))
% 3.06/1.00      | ~ v1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f77]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3072,plain,
% 3.06/1.00      ( v1_funct_1(k2_funct_1(sK4))
% 3.06/1.00      | ~ v1_funct_1(sK4)
% 3.06/1.00      | ~ v1_relat_1(sK4) ),
% 3.06/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3073,plain,
% 3.06/1.00      ( v1_funct_1(k2_funct_1(sK4)) = iProver_top
% 3.06/1.00      | v1_funct_1(sK4) != iProver_top
% 3.06/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_3072]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3088,plain,
% 3.06/1.00      ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) != iProver_top
% 3.06/1.00      | v1_relat_1(sK4) = iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_3087]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3129,plain,
% 3.06/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.06/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_2737,c_43,c_45,c_1386,c_3073,c_3088]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3836,plain,
% 3.06/1.00      ( r1_tarski(k2_funct_1(sK4),k2_zfmisc_1(sK3,sK2)) != iProver_top
% 3.06/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_2757,c_3129]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4573,plain,
% 3.06/1.00      ( v1_xboole_0(k2_funct_1(sK4)) != iProver_top
% 3.06/1.00      | v1_xboole_0(sK3) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_4158,c_3836]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4583,plain,
% 3.06/1.00      ( ~ v1_xboole_0(k2_funct_1(sK4)) | ~ v1_xboole_0(sK3) ),
% 3.06/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_4573]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5183,plain,
% 3.06/1.00      ( sK3 != k1_xboole_0 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_4911,c_5,c_3092,c_4044,c_4583]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_6031,plain,
% 3.06/1.00      ( k1_relat_1(sK4) = sK2 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_5892,c_5,c_3092,c_4044,c_4583,c_4911]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_4914,plain,
% 3.06/1.00      ( k1_relat_1(k2_funct_1(sK4)) = sK3 ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_4888,c_3100]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_34,plain,
% 3.06/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2747,plain,
% 3.06/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) = iProver_top
% 3.06/1.00      | v1_funct_1(X0) != iProver_top
% 3.06/1.00      | v1_relat_1(X0) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5084,plain,
% 3.06/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k2_relat_1(k2_funct_1(sK4))))) = iProver_top
% 3.06/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.06/1.00      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.06/1.00      inference(superposition,[status(thm)],[c_4914,c_2747]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_20,plain,
% 3.06/1.00      ( ~ v2_funct_1(X0)
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_relat_1(X0)
% 3.06/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_529,plain,
% 3.06/1.00      ( ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_relat_1(X0)
% 3.06/1.00      | k2_relat_1(k2_funct_1(X0)) = k1_relat_1(X0)
% 3.06/1.00      | sK4 != X0 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_20,c_39]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_530,plain,
% 3.06/1.00      ( ~ v1_funct_1(sK4)
% 3.06/1.00      | ~ v1_relat_1(sK4)
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_529]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_532,plain,
% 3.06/1.00      ( ~ v1_relat_1(sK4)
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_530,c_42]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2742,plain,
% 3.06/1.00      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4)
% 3.06/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_532]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3096,plain,
% 3.06/1.00      ( k2_relat_1(k2_funct_1(sK4)) = k1_relat_1(sK4) ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_2742,c_42,c_40,c_530,c_3087]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5089,plain,
% 3.06/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top
% 3.06/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.06/1.00      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_5084,c_3096]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3080,plain,
% 3.06/1.00      ( v1_funct_1(sK4) != iProver_top
% 3.06/1.00      | v1_relat_1(k2_funct_1(sK4)) = iProver_top
% 3.06/1.00      | v1_relat_1(sK4) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_3079]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_5920,plain,
% 3.06/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_relat_1(sK4)))) = iProver_top ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_5089,c_43,c_45,c_3073,c_3080,c_3088]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_6036,plain,
% 3.06/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) = iProver_top ),
% 3.06/1.00      inference(demodulation,[status(thm)],[c_6031,c_5920]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_35,plain,
% 3.06/1.00      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_relat_1(X0) ),
% 3.06/1.00      inference(cnf_transformation,[],[f93]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1506,plain,
% 3.06/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.06/1.00      | ~ v1_funct_1(X0)
% 3.06/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.06/1.00      | ~ v1_relat_1(X0)
% 3.06/1.00      | k2_funct_1(sK4) != X0
% 3.06/1.00      | k1_relat_1(X0) != sK3
% 3.06/1.00      | k2_relat_1(X0) != sK2 ),
% 3.06/1.00      inference(resolution_lifted,[status(thm)],[c_35,c_37]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1507,plain,
% 3.06/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.06/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.06/1.00      | ~ v1_relat_1(k2_funct_1(sK4))
% 3.06/1.00      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 3.06/1.00      inference(unflattening,[status(thm)],[c_1506]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1519,plain,
% 3.06/1.00      ( ~ m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2)))
% 3.06/1.00      | ~ v1_funct_1(k2_funct_1(sK4))
% 3.06/1.00      | k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2 ),
% 3.06/1.00      inference(forward_subsumption_resolution,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_1507,c_22]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_2731,plain,
% 3.06/1.00      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.06/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.06/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_1519]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_1508,plain,
% 3.06/1.00      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.06/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.06/1.00      | v1_funct_1(k2_funct_1(sK4)) != iProver_top
% 3.06/1.00      | v1_relat_1(k2_funct_1(sK4)) != iProver_top ),
% 3.06/1.00      inference(predicate_to_equality,[status(thm)],[c_1507]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3160,plain,
% 3.06/1.00      ( m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.06/1.00      | k1_relat_1(k2_funct_1(sK4)) != sK3 ),
% 3.06/1.00      inference(global_propositional_subsumption,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_2731,c_43,c_45,c_1508,c_3073,c_3080,c_3088]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3161,plain,
% 3.06/1.00      ( k1_relat_1(k2_funct_1(sK4)) != sK3
% 3.06/1.00      | k2_relat_1(k2_funct_1(sK4)) != sK2
% 3.06/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.06/1.00      inference(renaming,[status(thm)],[c_3160]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(c_3164,plain,
% 3.06/1.00      ( k1_relat_1(sK4) != sK2
% 3.06/1.00      | k2_relat_1(sK4) != sK3
% 3.06/1.00      | m1_subset_1(k2_funct_1(sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK2))) != iProver_top ),
% 3.06/1.00      inference(light_normalisation,[status(thm)],[c_3161,c_3096,c_3100]) ).
% 3.06/1.00  
% 3.06/1.00  cnf(contradiction,plain,
% 3.06/1.00      ( $false ),
% 3.06/1.00      inference(minisat,
% 3.06/1.00                [status(thm)],
% 3.06/1.00                [c_6036,c_5892,c_5183,c_4888,c_3164]) ).
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.06/1.00  
% 3.06/1.00  ------                               Statistics
% 3.06/1.00  
% 3.06/1.00  ------ General
% 3.06/1.00  
% 3.06/1.00  abstr_ref_over_cycles:                  0
% 3.06/1.00  abstr_ref_under_cycles:                 0
% 3.06/1.00  gc_basic_clause_elim:                   0
% 3.06/1.00  forced_gc_time:                         0
% 3.06/1.00  parsing_time:                           0.009
% 3.06/1.00  unif_index_cands_time:                  0.
% 3.06/1.00  unif_index_add_time:                    0.
% 3.06/1.00  orderings_time:                         0.
% 3.06/1.00  out_proof_time:                         0.01
% 3.06/1.00  total_time:                             0.202
% 3.06/1.00  num_of_symbols:                         53
% 3.06/1.00  num_of_terms:                           4357
% 3.06/1.00  
% 3.06/1.00  ------ Preprocessing
% 3.06/1.00  
% 3.06/1.00  num_of_splits:                          0
% 3.06/1.00  num_of_split_atoms:                     0
% 3.06/1.00  num_of_reused_defs:                     0
% 3.06/1.00  num_eq_ax_congr_red:                    22
% 3.06/1.00  num_of_sem_filtered_clauses:            1
% 3.06/1.00  num_of_subtypes:                        0
% 3.06/1.00  monotx_restored_types:                  0
% 3.06/1.00  sat_num_of_epr_types:                   0
% 3.06/1.00  sat_num_of_non_cyclic_types:            0
% 3.06/1.00  sat_guarded_non_collapsed_types:        0
% 3.06/1.00  num_pure_diseq_elim:                    0
% 3.06/1.00  simp_replaced_by:                       0
% 3.06/1.00  res_preprocessed:                       192
% 3.06/1.00  prep_upred:                             0
% 3.06/1.00  prep_unflattend:                        85
% 3.06/1.00  smt_new_axioms:                         0
% 3.06/1.00  pred_elim_cands:                        6
% 3.06/1.00  pred_elim:                              3
% 3.06/1.00  pred_elim_cl:                           -1
% 3.06/1.00  pred_elim_cycles:                       6
% 3.06/1.00  merged_defs:                            8
% 3.06/1.00  merged_defs_ncl:                        0
% 3.06/1.00  bin_hyper_res:                          9
% 3.06/1.00  prep_cycles:                            4
% 3.06/1.00  pred_elim_time:                         0.048
% 3.06/1.00  splitting_time:                         0.
% 3.06/1.00  sem_filter_time:                        0.
% 3.06/1.00  monotx_time:                            0.
% 3.06/1.00  subtype_inf_time:                       0.
% 3.06/1.00  
% 3.06/1.00  ------ Problem properties
% 3.06/1.00  
% 3.06/1.00  clauses:                                41
% 3.06/1.00  conjectures:                            3
% 3.06/1.00  epr:                                    7
% 3.06/1.00  horn:                                   33
% 3.06/1.00  ground:                                 15
% 3.06/1.00  unary:                                  7
% 3.06/1.00  binary:                                 13
% 3.06/1.00  lits:                                   109
% 3.06/1.00  lits_eq:                                39
% 3.06/1.00  fd_pure:                                0
% 3.06/1.00  fd_pseudo:                              0
% 3.06/1.00  fd_cond:                                4
% 3.06/1.00  fd_pseudo_cond:                         1
% 3.06/1.00  ac_symbols:                             0
% 3.06/1.00  
% 3.06/1.00  ------ Propositional Solver
% 3.06/1.00  
% 3.06/1.00  prop_solver_calls:                      28
% 3.06/1.00  prop_fast_solver_calls:                 1427
% 3.06/1.00  smt_solver_calls:                       0
% 3.06/1.00  smt_fast_solver_calls:                  0
% 3.06/1.00  prop_num_of_clauses:                    1836
% 3.06/1.00  prop_preprocess_simplified:             6890
% 3.06/1.00  prop_fo_subsumed:                       33
% 3.06/1.00  prop_solver_time:                       0.
% 3.06/1.00  smt_solver_time:                        0.
% 3.06/1.00  smt_fast_solver_time:                   0.
% 3.06/1.00  prop_fast_solver_time:                  0.
% 3.06/1.00  prop_unsat_core_time:                   0.
% 3.06/1.00  
% 3.06/1.00  ------ QBF
% 3.06/1.00  
% 3.06/1.00  qbf_q_res:                              0
% 3.06/1.00  qbf_num_tautologies:                    0
% 3.06/1.00  qbf_prep_cycles:                        0
% 3.06/1.00  
% 3.06/1.00  ------ BMC1
% 3.06/1.00  
% 3.06/1.00  bmc1_current_bound:                     -1
% 3.06/1.00  bmc1_last_solved_bound:                 -1
% 3.06/1.00  bmc1_unsat_core_size:                   -1
% 3.06/1.00  bmc1_unsat_core_parents_size:           -1
% 3.06/1.00  bmc1_merge_next_fun:                    0
% 3.06/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.06/1.00  
% 3.06/1.00  ------ Instantiation
% 3.06/1.00  
% 3.06/1.00  inst_num_of_clauses:                    515
% 3.06/1.00  inst_num_in_passive:                    235
% 3.06/1.00  inst_num_in_active:                     243
% 3.06/1.00  inst_num_in_unprocessed:                37
% 3.06/1.00  inst_num_of_loops:                      340
% 3.06/1.00  inst_num_of_learning_restarts:          0
% 3.06/1.00  inst_num_moves_active_passive:          94
% 3.06/1.00  inst_lit_activity:                      0
% 3.06/1.00  inst_lit_activity_moves:                0
% 3.06/1.00  inst_num_tautologies:                   0
% 3.06/1.00  inst_num_prop_implied:                  0
% 3.06/1.00  inst_num_existing_simplified:           0
% 3.06/1.00  inst_num_eq_res_simplified:             0
% 3.06/1.00  inst_num_child_elim:                    0
% 3.06/1.00  inst_num_of_dismatching_blockings:      162
% 3.06/1.00  inst_num_of_non_proper_insts:           449
% 3.06/1.00  inst_num_of_duplicates:                 0
% 3.06/1.00  inst_inst_num_from_inst_to_res:         0
% 3.06/1.00  inst_dismatching_checking_time:         0.
% 3.06/1.00  
% 3.06/1.00  ------ Resolution
% 3.06/1.00  
% 3.06/1.00  res_num_of_clauses:                     0
% 3.06/1.00  res_num_in_passive:                     0
% 3.06/1.00  res_num_in_active:                      0
% 3.06/1.00  res_num_of_loops:                       196
% 3.06/1.00  res_forward_subset_subsumed:            17
% 3.06/1.00  res_backward_subset_subsumed:           0
% 3.06/1.00  res_forward_subsumed:                   1
% 3.06/1.00  res_backward_subsumed:                  0
% 3.06/1.00  res_forward_subsumption_resolution:     2
% 3.06/1.00  res_backward_subsumption_resolution:    0
% 3.06/1.00  res_clause_to_clause_subsumption:       202
% 3.06/1.00  res_orphan_elimination:                 0
% 3.06/1.00  res_tautology_del:                      60
% 3.06/1.00  res_num_eq_res_simplified:              0
% 3.06/1.00  res_num_sel_changes:                    0
% 3.06/1.00  res_moves_from_active_to_pass:          0
% 3.06/1.00  
% 3.06/1.00  ------ Superposition
% 3.06/1.00  
% 3.06/1.00  sup_time_total:                         0.
% 3.06/1.00  sup_time_generating:                    0.
% 3.06/1.00  sup_time_sim_full:                      0.
% 3.06/1.00  sup_time_sim_immed:                     0.
% 3.06/1.00  
% 3.06/1.00  sup_num_of_clauses:                     76
% 3.06/1.00  sup_num_in_active:                      49
% 3.06/1.00  sup_num_in_passive:                     27
% 3.06/1.00  sup_num_of_loops:                       67
% 3.06/1.00  sup_fw_superposition:                   41
% 3.06/1.00  sup_bw_superposition:                   25
% 3.06/1.00  sup_immediate_simplified:               10
% 3.06/1.00  sup_given_eliminated:                   0
% 3.06/1.00  comparisons_done:                       0
% 3.06/1.00  comparisons_avoided:                    7
% 3.06/1.00  
% 3.06/1.00  ------ Simplifications
% 3.06/1.00  
% 3.06/1.00  
% 3.06/1.00  sim_fw_subset_subsumed:                 2
% 3.06/1.00  sim_bw_subset_subsumed:                 5
% 3.06/1.00  sim_fw_subsumed:                        0
% 3.06/1.00  sim_bw_subsumed:                        0
% 3.06/1.00  sim_fw_subsumption_res:                 0
% 3.06/1.00  sim_bw_subsumption_res:                 0
% 3.06/1.00  sim_tautology_del:                      3
% 3.06/1.00  sim_eq_tautology_del:                   2
% 3.06/1.00  sim_eq_res_simp:                        1
% 3.06/1.00  sim_fw_demodulated:                     5
% 3.06/1.00  sim_bw_demodulated:                     15
% 3.06/1.00  sim_light_normalised:                   10
% 3.06/1.00  sim_joinable_taut:                      0
% 3.06/1.00  sim_joinable_simp:                      0
% 3.06/1.00  sim_ac_normalised:                      0
% 3.06/1.00  sim_smt_subsumption:                    0
% 3.06/1.00  
%------------------------------------------------------------------------------
