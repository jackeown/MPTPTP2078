%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:06:53 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  234 (50208 expanded)
%              Number of clauses        :  163 (13695 expanded)
%              Number of leaves         :   18 (10082 expanded)
%              Depth                    :   31
%              Number of atoms          :  783 (368475 expanded)
%              Number of equality atoms :  379 (115951 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( ( k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f19,plain,(
    ! [X0] :
      ( ( v2_funct_1(X0)
      <=> ! [X1,X2] :
            ( X1 = X2
            | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
            | ~ r2_hidden(X2,k1_relat_1(X0))
            | ~ r2_hidden(X1,k1_relat_1(X0)) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f34,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X1,X2] :
              ( X1 = X2
              | k1_funct_1(X0,X1) != k1_funct_1(X0,X2)
              | ~ r2_hidden(X2,k1_relat_1(X0))
              | ~ r2_hidden(X1,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f35,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ? [X1,X2] :
              ( X1 != X2
              & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
              & r2_hidden(X2,k1_relat_1(X0))
              & r2_hidden(X1,k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1,X2] :
          ( X1 != X2
          & k1_funct_1(X0,X1) = k1_funct_1(X0,X2)
          & r2_hidden(X2,k1_relat_1(X0))
          & r2_hidden(X1,k1_relat_1(X0)) )
     => ( sK0(X0) != sK1(X0)
        & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
        & r2_hidden(sK1(X0),k1_relat_1(X0))
        & r2_hidden(sK0(X0),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( ( v2_funct_1(X0)
          | ( sK0(X0) != sK1(X0)
            & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
            & r2_hidden(sK1(X0),k1_relat_1(X0))
            & r2_hidden(sK0(X0),k1_relat_1(X0)) ) )
        & ( ! [X3,X4] :
              ( X3 = X4
              | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
              | ~ r2_hidden(X4,k1_relat_1(X0))
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ v2_funct_1(X0) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f36])).

fof(f58,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f13,conjecture,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => ( v2_funct_1(X1)
      <=> ! [X2,X3] :
            ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v1_funct_2(X1,X0,X0)
          & v1_funct_1(X1) )
       => ( v2_funct_1(X1)
        <=> ! [X2,X3] :
              ( ( k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
                & r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => X2 = X3 ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f27,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( v2_funct_1(X1)
      <~> ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) ) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f38,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f39,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X2,X3] :
            ( X2 = X3
            | k1_funct_1(X1,X2) != k1_funct_1(X1,X3)
            | ~ r2_hidden(X3,X0)
            | ~ r2_hidden(X2,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(flattening,[],[f38])).

fof(f40,plain,(
    ? [X0,X1] :
      ( ( ? [X2,X3] :
            ( X2 != X3
            & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
            & r2_hidden(X3,X0)
            & r2_hidden(X2,X0) )
        | ~ v2_funct_1(X1) )
      & ( ! [X4,X5] :
            ( X4 = X5
            | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
            | ~ r2_hidden(X5,X0)
            | ~ r2_hidden(X4,X0) )
        | v2_funct_1(X1) )
      & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_funct_2(X1,X0,X0)
      & v1_funct_1(X1) ) ),
    inference(rectify,[],[f39])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ? [X2,X3] :
          ( X2 != X3
          & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( sK4 != sK5
        & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5)
        & r2_hidden(sK5,X0)
        & r2_hidden(sK4,X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1] :
        ( ( ? [X2,X3] :
              ( X2 != X3
              & k1_funct_1(X1,X2) = k1_funct_1(X1,X3)
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | ~ v2_funct_1(X1) )
        & ( ! [X4,X5] :
              ( X4 = X5
              | k1_funct_1(X1,X4) != k1_funct_1(X1,X5)
              | ~ r2_hidden(X5,X0)
              | ~ r2_hidden(X4,X0) )
          | v2_funct_1(X1) )
        & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
   => ( ( ? [X3,X2] :
            ( X2 != X3
            & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3)
            & r2_hidden(X3,sK2)
            & r2_hidden(X2,sK2) )
        | ~ v2_funct_1(sK3) )
      & ( ! [X5,X4] :
            ( X4 = X5
            | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
            | ~ r2_hidden(X5,sK2)
            | ~ r2_hidden(X4,sK2) )
        | v2_funct_1(sK3) )
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
      & v1_funct_2(sK3,sK2,sK2)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ( ( sK4 != sK5
        & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
        & r2_hidden(sK5,sK2)
        & r2_hidden(sK4,sK2) )
      | ~ v2_funct_1(sK3) )
    & ( ! [X4,X5] :
          ( X4 = X5
          | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
          | ~ r2_hidden(X5,sK2)
          | ~ r2_hidden(X4,sK2) )
      | v2_funct_1(sK3) )
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    & v1_funct_2(sK3,sK2,sK2)
    & v1_funct_1(sK3) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f40,f42,f41])).

fof(f66,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f68,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ( ( r2_hidden(X2,X0)
          & v2_funct_1(X3) )
       => ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f25])).

fof(f65,plain,(
    ! [X2,X0,X3,X1] :
      ( k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2
      | k1_xboole_0 = X1
      | ~ r2_hidden(X2,X0)
      | ~ v2_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f67,plain,(
    v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f29])).

fof(f44,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f75,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f44])).

fof(f46,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f59,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | sK0(X0) != sK1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,
    ( sK4 != sK5
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f57,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK1(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f56,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | r2_hidden(sK0(X0),k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f55,plain,(
    ! [X4,X0,X3] :
      ( X3 = X4
      | k1_funct_1(X0,X3) != k1_funct_1(X0,X4)
      | ~ r2_hidden(X4,k1_relat_1(X0))
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f16])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f69,plain,(
    ! [X4,X5] :
      ( X4 = X5
      | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5)
      | ~ r2_hidden(X5,sK2)
      | ~ r2_hidden(X4,sK2)
      | v2_funct_1(sK3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f71,plain,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f72,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f43])).

fof(f4,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f31])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f77,plain,(
    ! [X1] : k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0 ),
    inference(equality_resolution,[],[f48])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( r2_hidden(X0,k1_relat_1(X1))
          & v2_funct_1(X1) )
       => ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
          & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0
        & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 )
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f20])).

fof(f60,plain,(
    ! [X0,X1] :
      ( k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
      | ~ r2_hidden(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f21])).

cnf(c_12,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_420,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_421,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_3388,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_422,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_3660,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | v1_relat_1(sK3) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_3661,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
    | v1_relat_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3660])).

cnf(c_4206,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3388,c_32,c_422,c_3661])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f65])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK3,sK2,sK2) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_365,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(X3,X1)
    | ~ v1_funct_1(X0)
    | ~ v2_funct_1(X0)
    | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
    | sK2 != X2
    | sK2 != X1
    | sK3 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_28])).

cnf(c_366,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
    | ~ r2_hidden(X0,sK2)
    | ~ v1_funct_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(unflattening,[status(thm)],[c_365])).

cnf(c_370,plain,
    ( ~ r2_hidden(X0,sK2)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | k1_xboole_0 = sK2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_366,c_29,c_27])).

cnf(c_2720,plain,
    ( ~ v2_funct_1(sK3)
    | sP3_iProver_split
    | k1_xboole_0 = sK2 ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_370])).

cnf(c_3391,plain,
    ( k1_xboole_0 = sK2
    | v2_funct_1(sK3) != iProver_top
    | sP3_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2720])).

cnf(c_4212,plain,
    ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0
    | sP3_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_4206,c_3391])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK4,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_3396,plain,
    ( r2_hidden(sK4,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2719,plain,
    ( ~ r2_hidden(X0,sK2)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | ~ sP3_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP3_iProver_split])],[c_370])).

cnf(c_3392,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,sK2) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2719])).

cnf(c_3958,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | v2_funct_1(sK3) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3396,c_3392])).

cnf(c_4213,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_4206,c_3958])).

cnf(c_6081,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4212,c_4213])).

cnf(c_2,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_90,plain,
    ( r1_tarski(sK3,sK3) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X0 = X1 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_94,plain,
    ( ~ r1_tarski(sK3,sK3)
    | sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_11,plain,
    ( ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_433,plain,
    ( ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK1(X0) != sK0(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_434,plain,
    ( ~ v1_relat_1(sK3)
    | v2_funct_1(sK3)
    | sK1(sK3) != sK0(sK3) ),
    inference(unflattening,[status(thm)],[c_433])).

cnf(c_22,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | sK4 != sK5 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_798,plain,
    ( ~ v1_relat_1(sK3)
    | sK1(sK3) != sK0(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_434,c_22])).

cnf(c_923,plain,
    ( ~ v1_relat_1(sK3)
    | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_421,c_22])).

cnf(c_13,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_407,plain,
    ( r2_hidden(sK1(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_408,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_407])).

cnf(c_1048,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_408,c_22])).

cnf(c_14,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | ~ v1_funct_1(X0)
    | v2_funct_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_394,plain,
    ( r2_hidden(sK0(X0),k1_relat_1(X0))
    | ~ v1_relat_1(X0)
    | v2_funct_1(X0)
    | sK3 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_395,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(unflattening,[status(thm)],[c_394])).

cnf(c_1173,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | sK5 != sK4 ),
    inference(resolution,[status(thm)],[c_395,c_22])).

cnf(c_2730,plain,
    ( X0 != X1
    | sK1(X0) = sK1(X1) ),
    theory(equality)).

cnf(c_2742,plain,
    ( sK1(sK3) = sK1(sK3)
    | sK3 != sK3 ),
    inference(instantiation,[status(thm)],[c_2730])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | X0 = X2
    | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_482,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(X2,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | X2 = X0
    | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_483,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(unflattening,[status(thm)],[c_482])).

cnf(c_2714,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_483])).

cnf(c_2723,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3759,plain,
    ( sK1(sK3) != X0
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != X0 ),
    inference(instantiation,[status(thm)],[c_2723])).

cnf(c_3884,plain,
    ( sK1(sK3) != sK1(sK3)
    | sK1(sK3) = sK0(sK3)
    | sK0(sK3) != sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_3759])).

cnf(c_2713,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ r2_hidden(X1,k1_relat_1(sK3))
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0)
    | ~ sP0_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP0_iProver_split])],[c_483])).

cnf(c_4756,plain,
    ( ~ r2_hidden(sK1(X0),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(X0))
    | sK0(sK3) = sK1(X0) ),
    inference(instantiation,[status(thm)],[c_2713])).

cnf(c_4758,plain,
    ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
    | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
    | ~ sP0_iProver_split
    | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
    | sK0(sK3) = sK1(sK3) ),
    inference(instantiation,[status(thm)],[c_4756])).

cnf(c_3390,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_396,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_395])).

cnf(c_4658,plain,
    ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3390,c_32,c_396,c_3661])).

cnf(c_3394,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_3400,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4942,plain,
    ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
    inference(superposition,[status(thm)],[c_3394,c_3400])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_3401,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5485,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
    | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4942,c_3401])).

cnf(c_5744,plain,
    ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5485,c_32])).

cnf(c_10,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_3403,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_5750,plain,
    ( m1_subset_1(X0,sK2) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5744,c_3403])).

cnf(c_8439,plain,
    ( m1_subset_1(sK0(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_5750])).

cnf(c_30,plain,
    ( v1_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_67,plain,
    ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_69,plain,
    ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_67])).

cnf(c_70,plain,
    ( sK1(X0) != sK0(X0)
    | v1_relat_1(X0) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v2_funct_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_72,plain,
    ( sK1(sK3) != sK0(sK3)
    | v1_relat_1(sK3) != iProver_top
    | v1_funct_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_70])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK2)
    | ~ r2_hidden(X1,sK2)
    | v2_funct_1(sK3)
    | X1 = X0
    | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3756,plain,
    ( ~ r2_hidden(sK1(sK3),sK2)
    | ~ r2_hidden(sK0(sK3),sK2)
    | v2_funct_1(sK3)
    | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_3757,plain,
    ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
    | sK1(sK3) = sK0(sK3)
    | r2_hidden(sK1(sK3),sK2) != iProver_top
    | r2_hidden(sK0(sK3),sK2) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3756])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_3404,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_5749,plain,
    ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
    inference(superposition,[status(thm)],[c_5744,c_3404])).

cnf(c_3389,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_409,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_408])).

cnf(c_4523,plain,
    ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3389,c_32,c_409,c_3661])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_8,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_214,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_8])).

cnf(c_215,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_214])).

cnf(c_272,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(bin_hyper_res,[status(thm)],[c_6,c_215])).

cnf(c_3393,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_272])).

cnf(c_4786,plain,
    ( r2_hidden(sK1(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4523,c_3393])).

cnf(c_8309,plain,
    ( r2_hidden(sK1(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5749,c_4786])).

cnf(c_4785,plain,
    ( r2_hidden(sK0(sK3),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_4658,c_3393])).

cnf(c_8310,plain,
    ( r2_hidden(sK0(sK3),sK2) = iProver_top
    | v2_funct_1(sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_5749,c_4785])).

cnf(c_8452,plain,
    ( v2_funct_1(sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8439,c_30,c_32,c_69,c_72,c_3661,c_3757,c_8309,c_8310])).

cnf(c_8454,plain,
    ( v2_funct_1(sK3) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8452])).

cnf(c_8457,plain,
    ( sK2 = k1_xboole_0
    | sP3_iProver_split = iProver_top ),
    inference(superposition,[status(thm)],[c_8452,c_3391])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK5,sK2)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_3397,plain,
    ( r2_hidden(sK5,sK2) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3957,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | v2_funct_1(sK3) != iProver_top
    | sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_3397,c_3392])).

cnf(c_8459,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
    | sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_8452,c_3957])).

cnf(c_23,negated_conjecture,
    ( ~ v2_funct_1(sK3)
    | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_3398,plain,
    ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_8463,plain,
    ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
    inference(superposition,[status(thm)],[c_8452,c_3398])).

cnf(c_8472,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sP3_iProver_split != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8459,c_8463])).

cnf(c_9292,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8457,c_8472])).

cnf(c_8458,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sP3_iProver_split != iProver_top ),
    inference(superposition,[status(thm)],[c_8452,c_3958])).

cnf(c_9293,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
    | sK2 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_8457,c_8458])).

cnf(c_9867,plain,
    ( sK2 = k1_xboole_0
    | sK5 = sK4 ),
    inference(superposition,[status(thm)],[c_9292,c_9293])).

cnf(c_9869,plain,
    ( sK2 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6081,c_27,c_90,c_94,c_798,c_923,c_1048,c_1173,c_2742,c_2714,c_3660,c_3884,c_4758,c_8454,c_9867])).

cnf(c_9890,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9869,c_3397])).

cnf(c_10250,plain,
    ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9890,c_30,c_32,c_69,c_72,c_3661,c_3757,c_8309,c_8310])).

cnf(c_10255,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10250,c_3393])).

cnf(c_7,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_3406,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4320,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_3406,c_3404])).

cnf(c_4783,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3397,c_3393])).

cnf(c_9884,plain,
    ( r2_hidden(sK5,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9869,c_4783])).

cnf(c_11598,plain,
    ( r2_hidden(sK5,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10255,c_30,c_32,c_69,c_72,c_3661,c_3757,c_4320,c_8309,c_8310,c_9884])).

cnf(c_4321,plain,
    ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3394,c_3404])).

cnf(c_3408,plain,
    ( X0 = X1
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_5648,plain,
    ( k2_zfmisc_1(sK2,sK2) = sK3
    | r1_tarski(k2_zfmisc_1(sK2,sK2),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_4321,c_3408])).

cnf(c_9880,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK3
    | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9869,c_5648])).

cnf(c_4,plain,
    ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f77])).

cnf(c_9934,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9880,c_4])).

cnf(c_4327,plain,
    ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4320])).

cnf(c_5232,plain,
    ( ~ r1_tarski(X0,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,X0)
    | X0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_5233,plain,
    ( X0 = k1_xboole_0
    | r1_tarski(X0,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5232])).

cnf(c_5235,plain,
    ( sK3 = k1_xboole_0
    | r1_tarski(sK3,k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5233])).

cnf(c_7458,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
    | r1_tarski(X0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_7459,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(X0,k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7458])).

cnf(c_7461,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_7459])).

cnf(c_9892,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9869,c_3394])).

cnf(c_9894,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9892,c_4])).

cnf(c_11032,plain,
    ( sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9934,c_4327,c_5235,c_7461,c_9894])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v1_funct_1(X1)
    | ~ v2_funct_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f60])).

cnf(c_446,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | ~ v2_funct_1(X1)
    | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
    | sK3 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_29])).

cnf(c_447,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_446])).

cnf(c_2717,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK3))
    | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | ~ sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[sP2_iProver_split])],[c_447])).

cnf(c_3386,plain,
    ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
    | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2717])).

cnf(c_11073,plain,
    ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) = X0
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | sP2_iProver_split != iProver_top ),
    inference(demodulation,[status(thm)],[c_11032,c_3386])).

cnf(c_2718,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v2_funct_1(sK3)
    | sP2_iProver_split ),
    inference(splitting,[splitting(split),new_symbols(definition,[])],[c_447])).

cnf(c_2756,plain,
    ( v1_relat_1(sK3) != iProver_top
    | v2_funct_1(sK3) != iProver_top
    | sP2_iProver_split = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2718])).

cnf(c_12248,plain,
    ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
    | k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11073,c_30,c_32,c_69,c_72,c_2756,c_3661,c_3757,c_8309,c_8310])).

cnf(c_12249,plain,
    ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) = X0
    | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_12248])).

cnf(c_12256,plain,
    ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_11598,c_12249])).

cnf(c_11044,plain,
    ( k1_funct_1(k1_xboole_0,sK5) = k1_funct_1(k1_xboole_0,sK4) ),
    inference(demodulation,[status(thm)],[c_11032,c_8463])).

cnf(c_12261,plain,
    ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK4)) = sK5 ),
    inference(light_normalisation,[status(thm)],[c_12256,c_11044])).

cnf(c_9891,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9869,c_3396])).

cnf(c_10260,plain,
    ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9891,c_30,c_32,c_69,c_72,c_3661,c_3757,c_8309,c_8310])).

cnf(c_10265,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10260,c_3393])).

cnf(c_4784,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(sK2,X0) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3396,c_3393])).

cnf(c_9883,plain,
    ( r2_hidden(sK4,X0) = iProver_top
    | r1_tarski(k1_xboole_0,X0) != iProver_top
    | v2_funct_1(sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_9869,c_4784])).

cnf(c_11713,plain,
    ( r2_hidden(sK4,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_10265,c_30,c_32,c_69,c_72,c_3661,c_3757,c_4320,c_8309,c_8310,c_9883])).

cnf(c_12257,plain,
    ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_11713,c_12249])).

cnf(c_13821,plain,
    ( sK5 = sK4 ),
    inference(light_normalisation,[status(thm)],[c_12261,c_12257])).

cnf(c_11045,plain,
    ( v2_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11032,c_8452])).

cnf(c_3399,plain,
    ( sK4 != sK5
    | v2_funct_1(sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_11081,plain,
    ( sK5 != sK4
    | v2_funct_1(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11032,c_3399])).

cnf(c_11210,plain,
    ( sK5 != sK4 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_11045,c_11081])).

cnf(c_13823,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13821,c_11210])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 10:25:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.34  % Running in FOF mode
% 3.61/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.61/0.99  
% 3.61/0.99  ------  iProver source info
% 3.61/0.99  
% 3.61/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.61/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.61/0.99  git: non_committed_changes: false
% 3.61/0.99  git: last_make_outside_of_git: false
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  
% 3.61/0.99  ------ Input Options
% 3.61/0.99  
% 3.61/0.99  --out_options                           all
% 3.61/0.99  --tptp_safe_out                         true
% 3.61/0.99  --problem_path                          ""
% 3.61/0.99  --include_path                          ""
% 3.61/0.99  --clausifier                            res/vclausify_rel
% 3.61/0.99  --clausifier_options                    --mode clausify
% 3.61/0.99  --stdin                                 false
% 3.61/0.99  --stats_out                             all
% 3.61/0.99  
% 3.61/0.99  ------ General Options
% 3.61/0.99  
% 3.61/0.99  --fof                                   false
% 3.61/0.99  --time_out_real                         305.
% 3.61/0.99  --time_out_virtual                      -1.
% 3.61/0.99  --symbol_type_check                     false
% 3.61/0.99  --clausify_out                          false
% 3.61/0.99  --sig_cnt_out                           false
% 3.61/0.99  --trig_cnt_out                          false
% 3.61/0.99  --trig_cnt_out_tolerance                1.
% 3.61/0.99  --trig_cnt_out_sk_spl                   false
% 3.61/0.99  --abstr_cl_out                          false
% 3.61/0.99  
% 3.61/0.99  ------ Global Options
% 3.61/0.99  
% 3.61/0.99  --schedule                              default
% 3.61/0.99  --add_important_lit                     false
% 3.61/0.99  --prop_solver_per_cl                    1000
% 3.61/0.99  --min_unsat_core                        false
% 3.61/0.99  --soft_assumptions                      false
% 3.61/0.99  --soft_lemma_size                       3
% 3.61/0.99  --prop_impl_unit_size                   0
% 3.61/0.99  --prop_impl_unit                        []
% 3.61/0.99  --share_sel_clauses                     true
% 3.61/0.99  --reset_solvers                         false
% 3.61/0.99  --bc_imp_inh                            [conj_cone]
% 3.61/0.99  --conj_cone_tolerance                   3.
% 3.61/0.99  --extra_neg_conj                        none
% 3.61/0.99  --large_theory_mode                     true
% 3.61/0.99  --prolific_symb_bound                   200
% 3.61/0.99  --lt_threshold                          2000
% 3.61/0.99  --clause_weak_htbl                      true
% 3.61/0.99  --gc_record_bc_elim                     false
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing Options
% 3.61/0.99  
% 3.61/0.99  --preprocessing_flag                    true
% 3.61/0.99  --time_out_prep_mult                    0.1
% 3.61/0.99  --splitting_mode                        input
% 3.61/0.99  --splitting_grd                         true
% 3.61/0.99  --splitting_cvd                         false
% 3.61/0.99  --splitting_cvd_svl                     false
% 3.61/0.99  --splitting_nvd                         32
% 3.61/0.99  --sub_typing                            true
% 3.61/0.99  --prep_gs_sim                           true
% 3.61/0.99  --prep_unflatten                        true
% 3.61/0.99  --prep_res_sim                          true
% 3.61/0.99  --prep_upred                            true
% 3.61/0.99  --prep_sem_filter                       exhaustive
% 3.61/0.99  --prep_sem_filter_out                   false
% 3.61/0.99  --pred_elim                             true
% 3.61/0.99  --res_sim_input                         true
% 3.61/0.99  --eq_ax_congr_red                       true
% 3.61/0.99  --pure_diseq_elim                       true
% 3.61/0.99  --brand_transform                       false
% 3.61/0.99  --non_eq_to_eq                          false
% 3.61/0.99  --prep_def_merge                        true
% 3.61/0.99  --prep_def_merge_prop_impl              false
% 3.61/0.99  --prep_def_merge_mbd                    true
% 3.61/0.99  --prep_def_merge_tr_red                 false
% 3.61/0.99  --prep_def_merge_tr_cl                  false
% 3.61/0.99  --smt_preprocessing                     true
% 3.61/0.99  --smt_ac_axioms                         fast
% 3.61/0.99  --preprocessed_out                      false
% 3.61/0.99  --preprocessed_stats                    false
% 3.61/0.99  
% 3.61/0.99  ------ Abstraction refinement Options
% 3.61/0.99  
% 3.61/0.99  --abstr_ref                             []
% 3.61/0.99  --abstr_ref_prep                        false
% 3.61/0.99  --abstr_ref_until_sat                   false
% 3.61/0.99  --abstr_ref_sig_restrict                funpre
% 3.61/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/0.99  --abstr_ref_under                       []
% 3.61/0.99  
% 3.61/0.99  ------ SAT Options
% 3.61/0.99  
% 3.61/0.99  --sat_mode                              false
% 3.61/0.99  --sat_fm_restart_options                ""
% 3.61/0.99  --sat_gr_def                            false
% 3.61/0.99  --sat_epr_types                         true
% 3.61/0.99  --sat_non_cyclic_types                  false
% 3.61/0.99  --sat_finite_models                     false
% 3.61/0.99  --sat_fm_lemmas                         false
% 3.61/0.99  --sat_fm_prep                           false
% 3.61/0.99  --sat_fm_uc_incr                        true
% 3.61/0.99  --sat_out_model                         small
% 3.61/0.99  --sat_out_clauses                       false
% 3.61/0.99  
% 3.61/0.99  ------ QBF Options
% 3.61/0.99  
% 3.61/0.99  --qbf_mode                              false
% 3.61/0.99  --qbf_elim_univ                         false
% 3.61/0.99  --qbf_dom_inst                          none
% 3.61/0.99  --qbf_dom_pre_inst                      false
% 3.61/0.99  --qbf_sk_in                             false
% 3.61/0.99  --qbf_pred_elim                         true
% 3.61/0.99  --qbf_split                             512
% 3.61/0.99  
% 3.61/0.99  ------ BMC1 Options
% 3.61/0.99  
% 3.61/0.99  --bmc1_incremental                      false
% 3.61/0.99  --bmc1_axioms                           reachable_all
% 3.61/0.99  --bmc1_min_bound                        0
% 3.61/0.99  --bmc1_max_bound                        -1
% 3.61/0.99  --bmc1_max_bound_default                -1
% 3.61/0.99  --bmc1_symbol_reachability              true
% 3.61/0.99  --bmc1_property_lemmas                  false
% 3.61/0.99  --bmc1_k_induction                      false
% 3.61/0.99  --bmc1_non_equiv_states                 false
% 3.61/0.99  --bmc1_deadlock                         false
% 3.61/0.99  --bmc1_ucm                              false
% 3.61/0.99  --bmc1_add_unsat_core                   none
% 3.61/0.99  --bmc1_unsat_core_children              false
% 3.61/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/0.99  --bmc1_out_stat                         full
% 3.61/0.99  --bmc1_ground_init                      false
% 3.61/0.99  --bmc1_pre_inst_next_state              false
% 3.61/0.99  --bmc1_pre_inst_state                   false
% 3.61/0.99  --bmc1_pre_inst_reach_state             false
% 3.61/0.99  --bmc1_out_unsat_core                   false
% 3.61/0.99  --bmc1_aig_witness_out                  false
% 3.61/0.99  --bmc1_verbose                          false
% 3.61/0.99  --bmc1_dump_clauses_tptp                false
% 3.61/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.61/0.99  --bmc1_dump_file                        -
% 3.61/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.61/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.61/0.99  --bmc1_ucm_extend_mode                  1
% 3.61/0.99  --bmc1_ucm_init_mode                    2
% 3.61/0.99  --bmc1_ucm_cone_mode                    none
% 3.61/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.61/0.99  --bmc1_ucm_relax_model                  4
% 3.61/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.61/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/0.99  --bmc1_ucm_layered_model                none
% 3.61/0.99  --bmc1_ucm_max_lemma_size               10
% 3.61/0.99  
% 3.61/0.99  ------ AIG Options
% 3.61/0.99  
% 3.61/0.99  --aig_mode                              false
% 3.61/0.99  
% 3.61/0.99  ------ Instantiation Options
% 3.61/0.99  
% 3.61/0.99  --instantiation_flag                    true
% 3.61/0.99  --inst_sos_flag                         false
% 3.61/0.99  --inst_sos_phase                        true
% 3.61/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/0.99  --inst_lit_sel_side                     num_symb
% 3.61/0.99  --inst_solver_per_active                1400
% 3.61/0.99  --inst_solver_calls_frac                1.
% 3.61/0.99  --inst_passive_queue_type               priority_queues
% 3.61/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/0.99  --inst_passive_queues_freq              [25;2]
% 3.61/0.99  --inst_dismatching                      true
% 3.61/0.99  --inst_eager_unprocessed_to_passive     true
% 3.61/0.99  --inst_prop_sim_given                   true
% 3.61/0.99  --inst_prop_sim_new                     false
% 3.61/0.99  --inst_subs_new                         false
% 3.61/0.99  --inst_eq_res_simp                      false
% 3.61/0.99  --inst_subs_given                       false
% 3.61/0.99  --inst_orphan_elimination               true
% 3.61/0.99  --inst_learning_loop_flag               true
% 3.61/0.99  --inst_learning_start                   3000
% 3.61/0.99  --inst_learning_factor                  2
% 3.61/0.99  --inst_start_prop_sim_after_learn       3
% 3.61/0.99  --inst_sel_renew                        solver
% 3.61/0.99  --inst_lit_activity_flag                true
% 3.61/0.99  --inst_restr_to_given                   false
% 3.61/0.99  --inst_activity_threshold               500
% 3.61/0.99  --inst_out_proof                        true
% 3.61/0.99  
% 3.61/0.99  ------ Resolution Options
% 3.61/0.99  
% 3.61/0.99  --resolution_flag                       true
% 3.61/0.99  --res_lit_sel                           adaptive
% 3.61/0.99  --res_lit_sel_side                      none
% 3.61/0.99  --res_ordering                          kbo
% 3.61/0.99  --res_to_prop_solver                    active
% 3.61/0.99  --res_prop_simpl_new                    false
% 3.61/0.99  --res_prop_simpl_given                  true
% 3.61/0.99  --res_passive_queue_type                priority_queues
% 3.61/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/0.99  --res_passive_queues_freq               [15;5]
% 3.61/0.99  --res_forward_subs                      full
% 3.61/0.99  --res_backward_subs                     full
% 3.61/0.99  --res_forward_subs_resolution           true
% 3.61/0.99  --res_backward_subs_resolution          true
% 3.61/0.99  --res_orphan_elimination                true
% 3.61/0.99  --res_time_limit                        2.
% 3.61/0.99  --res_out_proof                         true
% 3.61/0.99  
% 3.61/0.99  ------ Superposition Options
% 3.61/0.99  
% 3.61/0.99  --superposition_flag                    true
% 3.61/0.99  --sup_passive_queue_type                priority_queues
% 3.61/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.61/0.99  --demod_completeness_check              fast
% 3.61/0.99  --demod_use_ground                      true
% 3.61/0.99  --sup_to_prop_solver                    passive
% 3.61/0.99  --sup_prop_simpl_new                    true
% 3.61/0.99  --sup_prop_simpl_given                  true
% 3.61/0.99  --sup_fun_splitting                     false
% 3.61/0.99  --sup_smt_interval                      50000
% 3.61/0.99  
% 3.61/0.99  ------ Superposition Simplification Setup
% 3.61/0.99  
% 3.61/0.99  --sup_indices_passive                   []
% 3.61/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.99  --sup_full_bw                           [BwDemod]
% 3.61/0.99  --sup_immed_triv                        [TrivRules]
% 3.61/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.99  --sup_immed_bw_main                     []
% 3.61/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.99  
% 3.61/0.99  ------ Combination Options
% 3.61/0.99  
% 3.61/0.99  --comb_res_mult                         3
% 3.61/0.99  --comb_sup_mult                         2
% 3.61/0.99  --comb_inst_mult                        10
% 3.61/0.99  
% 3.61/0.99  ------ Debug Options
% 3.61/0.99  
% 3.61/0.99  --dbg_backtrace                         false
% 3.61/0.99  --dbg_dump_prop_clauses                 false
% 3.61/0.99  --dbg_dump_prop_clauses_file            -
% 3.61/0.99  --dbg_out_stat                          false
% 3.61/0.99  ------ Parsing...
% 3.61/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... gs_s  sp: 4 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.61/0.99  ------ Proving...
% 3.61/0.99  ------ Problem Properties 
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  clauses                                 31
% 3.61/0.99  conjectures                             6
% 3.61/0.99  EPR                                     10
% 3.61/0.99  Horn                                    25
% 3.61/0.99  unary                                   5
% 3.61/0.99  binary                                  9
% 3.61/0.99  lits                                    78
% 3.61/0.99  lits eq                                 19
% 3.61/0.99  fd_pure                                 0
% 3.61/0.99  fd_pseudo                               0
% 3.61/0.99  fd_cond                                 1
% 3.61/0.99  fd_pseudo_cond                          3
% 3.61/0.99  AC symbols                              0
% 3.61/0.99  
% 3.61/0.99  ------ Schedule dynamic 5 is on 
% 3.61/0.99  
% 3.61/0.99  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  ------ 
% 3.61/0.99  Current options:
% 3.61/0.99  ------ 
% 3.61/0.99  
% 3.61/0.99  ------ Input Options
% 3.61/0.99  
% 3.61/0.99  --out_options                           all
% 3.61/0.99  --tptp_safe_out                         true
% 3.61/0.99  --problem_path                          ""
% 3.61/0.99  --include_path                          ""
% 3.61/0.99  --clausifier                            res/vclausify_rel
% 3.61/0.99  --clausifier_options                    --mode clausify
% 3.61/0.99  --stdin                                 false
% 3.61/0.99  --stats_out                             all
% 3.61/0.99  
% 3.61/0.99  ------ General Options
% 3.61/0.99  
% 3.61/0.99  --fof                                   false
% 3.61/0.99  --time_out_real                         305.
% 3.61/0.99  --time_out_virtual                      -1.
% 3.61/0.99  --symbol_type_check                     false
% 3.61/0.99  --clausify_out                          false
% 3.61/0.99  --sig_cnt_out                           false
% 3.61/0.99  --trig_cnt_out                          false
% 3.61/0.99  --trig_cnt_out_tolerance                1.
% 3.61/0.99  --trig_cnt_out_sk_spl                   false
% 3.61/0.99  --abstr_cl_out                          false
% 3.61/0.99  
% 3.61/0.99  ------ Global Options
% 3.61/0.99  
% 3.61/0.99  --schedule                              default
% 3.61/0.99  --add_important_lit                     false
% 3.61/0.99  --prop_solver_per_cl                    1000
% 3.61/0.99  --min_unsat_core                        false
% 3.61/0.99  --soft_assumptions                      false
% 3.61/0.99  --soft_lemma_size                       3
% 3.61/0.99  --prop_impl_unit_size                   0
% 3.61/0.99  --prop_impl_unit                        []
% 3.61/0.99  --share_sel_clauses                     true
% 3.61/0.99  --reset_solvers                         false
% 3.61/0.99  --bc_imp_inh                            [conj_cone]
% 3.61/0.99  --conj_cone_tolerance                   3.
% 3.61/0.99  --extra_neg_conj                        none
% 3.61/0.99  --large_theory_mode                     true
% 3.61/0.99  --prolific_symb_bound                   200
% 3.61/0.99  --lt_threshold                          2000
% 3.61/0.99  --clause_weak_htbl                      true
% 3.61/0.99  --gc_record_bc_elim                     false
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing Options
% 3.61/0.99  
% 3.61/0.99  --preprocessing_flag                    true
% 3.61/0.99  --time_out_prep_mult                    0.1
% 3.61/0.99  --splitting_mode                        input
% 3.61/0.99  --splitting_grd                         true
% 3.61/0.99  --splitting_cvd                         false
% 3.61/0.99  --splitting_cvd_svl                     false
% 3.61/0.99  --splitting_nvd                         32
% 3.61/0.99  --sub_typing                            true
% 3.61/0.99  --prep_gs_sim                           true
% 3.61/0.99  --prep_unflatten                        true
% 3.61/0.99  --prep_res_sim                          true
% 3.61/0.99  --prep_upred                            true
% 3.61/0.99  --prep_sem_filter                       exhaustive
% 3.61/0.99  --prep_sem_filter_out                   false
% 3.61/0.99  --pred_elim                             true
% 3.61/0.99  --res_sim_input                         true
% 3.61/0.99  --eq_ax_congr_red                       true
% 3.61/0.99  --pure_diseq_elim                       true
% 3.61/0.99  --brand_transform                       false
% 3.61/0.99  --non_eq_to_eq                          false
% 3.61/0.99  --prep_def_merge                        true
% 3.61/0.99  --prep_def_merge_prop_impl              false
% 3.61/0.99  --prep_def_merge_mbd                    true
% 3.61/0.99  --prep_def_merge_tr_red                 false
% 3.61/0.99  --prep_def_merge_tr_cl                  false
% 3.61/0.99  --smt_preprocessing                     true
% 3.61/0.99  --smt_ac_axioms                         fast
% 3.61/0.99  --preprocessed_out                      false
% 3.61/0.99  --preprocessed_stats                    false
% 3.61/0.99  
% 3.61/0.99  ------ Abstraction refinement Options
% 3.61/0.99  
% 3.61/0.99  --abstr_ref                             []
% 3.61/0.99  --abstr_ref_prep                        false
% 3.61/0.99  --abstr_ref_until_sat                   false
% 3.61/0.99  --abstr_ref_sig_restrict                funpre
% 3.61/0.99  --abstr_ref_af_restrict_to_split_sk     false
% 3.61/0.99  --abstr_ref_under                       []
% 3.61/0.99  
% 3.61/0.99  ------ SAT Options
% 3.61/0.99  
% 3.61/0.99  --sat_mode                              false
% 3.61/0.99  --sat_fm_restart_options                ""
% 3.61/0.99  --sat_gr_def                            false
% 3.61/0.99  --sat_epr_types                         true
% 3.61/0.99  --sat_non_cyclic_types                  false
% 3.61/0.99  --sat_finite_models                     false
% 3.61/0.99  --sat_fm_lemmas                         false
% 3.61/0.99  --sat_fm_prep                           false
% 3.61/0.99  --sat_fm_uc_incr                        true
% 3.61/0.99  --sat_out_model                         small
% 3.61/0.99  --sat_out_clauses                       false
% 3.61/0.99  
% 3.61/0.99  ------ QBF Options
% 3.61/0.99  
% 3.61/0.99  --qbf_mode                              false
% 3.61/0.99  --qbf_elim_univ                         false
% 3.61/0.99  --qbf_dom_inst                          none
% 3.61/0.99  --qbf_dom_pre_inst                      false
% 3.61/0.99  --qbf_sk_in                             false
% 3.61/0.99  --qbf_pred_elim                         true
% 3.61/0.99  --qbf_split                             512
% 3.61/0.99  
% 3.61/0.99  ------ BMC1 Options
% 3.61/0.99  
% 3.61/0.99  --bmc1_incremental                      false
% 3.61/0.99  --bmc1_axioms                           reachable_all
% 3.61/0.99  --bmc1_min_bound                        0
% 3.61/0.99  --bmc1_max_bound                        -1
% 3.61/0.99  --bmc1_max_bound_default                -1
% 3.61/0.99  --bmc1_symbol_reachability              true
% 3.61/0.99  --bmc1_property_lemmas                  false
% 3.61/0.99  --bmc1_k_induction                      false
% 3.61/0.99  --bmc1_non_equiv_states                 false
% 3.61/0.99  --bmc1_deadlock                         false
% 3.61/0.99  --bmc1_ucm                              false
% 3.61/0.99  --bmc1_add_unsat_core                   none
% 3.61/0.99  --bmc1_unsat_core_children              false
% 3.61/0.99  --bmc1_unsat_core_extrapolate_axioms    false
% 3.61/0.99  --bmc1_out_stat                         full
% 3.61/0.99  --bmc1_ground_init                      false
% 3.61/0.99  --bmc1_pre_inst_next_state              false
% 3.61/0.99  --bmc1_pre_inst_state                   false
% 3.61/0.99  --bmc1_pre_inst_reach_state             false
% 3.61/0.99  --bmc1_out_unsat_core                   false
% 3.61/0.99  --bmc1_aig_witness_out                  false
% 3.61/0.99  --bmc1_verbose                          false
% 3.61/0.99  --bmc1_dump_clauses_tptp                false
% 3.61/0.99  --bmc1_dump_unsat_core_tptp             false
% 3.61/0.99  --bmc1_dump_file                        -
% 3.61/0.99  --bmc1_ucm_expand_uc_limit              128
% 3.61/0.99  --bmc1_ucm_n_expand_iterations          6
% 3.61/0.99  --bmc1_ucm_extend_mode                  1
% 3.61/0.99  --bmc1_ucm_init_mode                    2
% 3.61/0.99  --bmc1_ucm_cone_mode                    none
% 3.61/0.99  --bmc1_ucm_reduced_relation_type        0
% 3.61/0.99  --bmc1_ucm_relax_model                  4
% 3.61/0.99  --bmc1_ucm_full_tr_after_sat            true
% 3.61/0.99  --bmc1_ucm_expand_neg_assumptions       false
% 3.61/0.99  --bmc1_ucm_layered_model                none
% 3.61/0.99  --bmc1_ucm_max_lemma_size               10
% 3.61/0.99  
% 3.61/0.99  ------ AIG Options
% 3.61/0.99  
% 3.61/0.99  --aig_mode                              false
% 3.61/0.99  
% 3.61/0.99  ------ Instantiation Options
% 3.61/0.99  
% 3.61/0.99  --instantiation_flag                    true
% 3.61/0.99  --inst_sos_flag                         false
% 3.61/0.99  --inst_sos_phase                        true
% 3.61/0.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.61/0.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.61/0.99  --inst_lit_sel_side                     none
% 3.61/0.99  --inst_solver_per_active                1400
% 3.61/0.99  --inst_solver_calls_frac                1.
% 3.61/0.99  --inst_passive_queue_type               priority_queues
% 3.61/0.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.61/0.99  --inst_passive_queues_freq              [25;2]
% 3.61/0.99  --inst_dismatching                      true
% 3.61/0.99  --inst_eager_unprocessed_to_passive     true
% 3.61/0.99  --inst_prop_sim_given                   true
% 3.61/0.99  --inst_prop_sim_new                     false
% 3.61/0.99  --inst_subs_new                         false
% 3.61/0.99  --inst_eq_res_simp                      false
% 3.61/0.99  --inst_subs_given                       false
% 3.61/0.99  --inst_orphan_elimination               true
% 3.61/0.99  --inst_learning_loop_flag               true
% 3.61/0.99  --inst_learning_start                   3000
% 3.61/0.99  --inst_learning_factor                  2
% 3.61/0.99  --inst_start_prop_sim_after_learn       3
% 3.61/0.99  --inst_sel_renew                        solver
% 3.61/0.99  --inst_lit_activity_flag                true
% 3.61/0.99  --inst_restr_to_given                   false
% 3.61/0.99  --inst_activity_threshold               500
% 3.61/0.99  --inst_out_proof                        true
% 3.61/0.99  
% 3.61/0.99  ------ Resolution Options
% 3.61/0.99  
% 3.61/0.99  --resolution_flag                       false
% 3.61/0.99  --res_lit_sel                           adaptive
% 3.61/0.99  --res_lit_sel_side                      none
% 3.61/0.99  --res_ordering                          kbo
% 3.61/0.99  --res_to_prop_solver                    active
% 3.61/0.99  --res_prop_simpl_new                    false
% 3.61/0.99  --res_prop_simpl_given                  true
% 3.61/0.99  --res_passive_queue_type                priority_queues
% 3.61/0.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.61/0.99  --res_passive_queues_freq               [15;5]
% 3.61/0.99  --res_forward_subs                      full
% 3.61/0.99  --res_backward_subs                     full
% 3.61/0.99  --res_forward_subs_resolution           true
% 3.61/0.99  --res_backward_subs_resolution          true
% 3.61/0.99  --res_orphan_elimination                true
% 3.61/0.99  --res_time_limit                        2.
% 3.61/0.99  --res_out_proof                         true
% 3.61/0.99  
% 3.61/0.99  ------ Superposition Options
% 3.61/0.99  
% 3.61/0.99  --superposition_flag                    true
% 3.61/0.99  --sup_passive_queue_type                priority_queues
% 3.61/0.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.61/0.99  --sup_passive_queues_freq               [8;1;4]
% 3.61/0.99  --demod_completeness_check              fast
% 3.61/0.99  --demod_use_ground                      true
% 3.61/0.99  --sup_to_prop_solver                    passive
% 3.61/0.99  --sup_prop_simpl_new                    true
% 3.61/0.99  --sup_prop_simpl_given                  true
% 3.61/0.99  --sup_fun_splitting                     false
% 3.61/0.99  --sup_smt_interval                      50000
% 3.61/0.99  
% 3.61/0.99  ------ Superposition Simplification Setup
% 3.61/0.99  
% 3.61/0.99  --sup_indices_passive                   []
% 3.61/0.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.61/0.99  --sup_full_triv                         [TrivRules;PropSubs]
% 3.61/0.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.99  --sup_full_bw                           [BwDemod]
% 3.61/0.99  --sup_immed_triv                        [TrivRules]
% 3.61/0.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.61/0.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.99  --sup_immed_bw_main                     []
% 3.61/0.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.99  --sup_input_triv                        [Unflattening;TrivRules]
% 3.61/0.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.61/0.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.61/0.99  
% 3.61/0.99  ------ Combination Options
% 3.61/0.99  
% 3.61/0.99  --comb_res_mult                         3
% 3.61/0.99  --comb_sup_mult                         2
% 3.61/0.99  --comb_inst_mult                        10
% 3.61/0.99  
% 3.61/0.99  ------ Debug Options
% 3.61/0.99  
% 3.61/0.99  --dbg_backtrace                         false
% 3.61/0.99  --dbg_dump_prop_clauses                 false
% 3.61/0.99  --dbg_dump_prop_clauses_file            -
% 3.61/0.99  --dbg_out_stat                          false
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  ------ Proving...
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS status Theorem for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99   Resolution empty clause
% 3.61/0.99  
% 3.61/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  fof(f7,axiom,(
% 3.61/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) <=> ! [X1,X2] : ((k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => X1 = X2)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f18,plain,(
% 3.61/0.99    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | (k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.61/0.99    inference(ennf_transformation,[],[f7])).
% 3.61/0.99  
% 3.61/0.99  fof(f19,plain,(
% 3.61/0.99    ! [X0] : ((v2_funct_1(X0) <=> ! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/0.99    inference(flattening,[],[f18])).
% 3.61/0.99  
% 3.61/0.99  fof(f34,plain,(
% 3.61/0.99    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X1,X2] : (X1 = X2 | k1_funct_1(X0,X1) != k1_funct_1(X0,X2) | ~r2_hidden(X2,k1_relat_1(X0)) | ~r2_hidden(X1,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/0.99    inference(nnf_transformation,[],[f19])).
% 3.61/0.99  
% 3.61/0.99  fof(f35,plain,(
% 3.61/0.99    ! [X0] : (((v2_funct_1(X0) | ? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/0.99    inference(rectify,[],[f34])).
% 3.61/0.99  
% 3.61/0.99  fof(f36,plain,(
% 3.61/0.99    ! [X0] : (? [X1,X2] : (X1 != X2 & k1_funct_1(X0,X1) = k1_funct_1(X0,X2) & r2_hidden(X2,k1_relat_1(X0)) & r2_hidden(X1,k1_relat_1(X0))) => (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0))))),
% 3.61/0.99    introduced(choice_axiom,[])).
% 3.61/0.99  
% 3.61/0.99  fof(f37,plain,(
% 3.61/0.99    ! [X0] : (((v2_funct_1(X0) | (sK0(X0) != sK1(X0) & k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) & r2_hidden(sK1(X0),k1_relat_1(X0)) & r2_hidden(sK0(X0),k1_relat_1(X0)))) & (! [X3,X4] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0))) | ~v2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.61/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f35,f36])).
% 3.61/0.99  
% 3.61/0.99  fof(f58,plain,(
% 3.61/0.99    ( ! [X0] : (v2_funct_1(X0) | k1_funct_1(X0,sK0(X0)) = k1_funct_1(X0,sK1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f37])).
% 3.61/0.99  
% 3.61/0.99  fof(f13,conjecture,(
% 3.61/0.99    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f14,negated_conjecture,(
% 3.61/0.99    ~! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => (v2_funct_1(X1) <=> ! [X2,X3] : ((k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => X2 = X3)))),
% 3.61/0.99    inference(negated_conjecture,[],[f13])).
% 3.61/0.99  
% 3.61/0.99  fof(f27,plain,(
% 3.61/0.99    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | (k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)))) & (m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)))),
% 3.61/0.99    inference(ennf_transformation,[],[f14])).
% 3.61/0.99  
% 3.61/0.99  fof(f28,plain,(
% 3.61/0.99    ? [X0,X1] : ((v2_funct_1(X1) <~> ! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.61/0.99    inference(flattening,[],[f27])).
% 3.61/0.99  
% 3.61/0.99  fof(f38,plain,(
% 3.61/0.99    ? [X0,X1] : (((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1))) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.61/0.99    inference(nnf_transformation,[],[f28])).
% 3.61/0.99  
% 3.61/0.99  fof(f39,plain,(
% 3.61/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X2,X3] : (X2 = X3 | k1_funct_1(X1,X2) != k1_funct_1(X1,X3) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.61/0.99    inference(flattening,[],[f38])).
% 3.61/0.99  
% 3.61/0.99  fof(f40,plain,(
% 3.61/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1))),
% 3.61/0.99    inference(rectify,[],[f39])).
% 3.61/0.99  
% 3.61/0.99  fof(f42,plain,(
% 3.61/0.99    ( ! [X0,X1] : (? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (sK4 != sK5 & k1_funct_1(X1,sK4) = k1_funct_1(X1,sK5) & r2_hidden(sK5,X0) & r2_hidden(sK4,X0))) )),
% 3.61/0.99    introduced(choice_axiom,[])).
% 3.61/0.99  
% 3.61/0.99  fof(f41,plain,(
% 3.61/0.99    ? [X0,X1] : ((? [X2,X3] : (X2 != X3 & k1_funct_1(X1,X2) = k1_funct_1(X1,X3) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | ~v2_funct_1(X1)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(X1,X4) != k1_funct_1(X1,X5) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) | v2_funct_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_funct_2(X1,X0,X0) & v1_funct_1(X1)) => ((? [X3,X2] : (X2 != X3 & k1_funct_1(sK3,X2) = k1_funct_1(sK3,X3) & r2_hidden(X3,sK2) & r2_hidden(X2,sK2)) | ~v2_funct_1(sK3)) & (! [X5,X4] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3))),
% 3.61/0.99    introduced(choice_axiom,[])).
% 3.61/0.99  
% 3.61/0.99  fof(f43,plain,(
% 3.61/0.99    ((sK4 != sK5 & k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) & r2_hidden(sK5,sK2) & r2_hidden(sK4,sK2)) | ~v2_funct_1(sK3)) & (! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2)) | v2_funct_1(sK3)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) & v1_funct_2(sK3,sK2,sK2) & v1_funct_1(sK3)),
% 3.61/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f40,f42,f41])).
% 3.61/0.99  
% 3.61/0.99  fof(f66,plain,(
% 3.61/0.99    v1_funct_1(sK3)),
% 3.61/0.99    inference(cnf_transformation,[],[f43])).
% 3.61/0.99  
% 3.61/0.99  fof(f68,plain,(
% 3.61/0.99    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))),
% 3.61/0.99    inference(cnf_transformation,[],[f43])).
% 3.61/0.99  
% 3.61/0.99  fof(f9,axiom,(
% 3.61/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f22,plain,(
% 3.61/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.99    inference(ennf_transformation,[],[f9])).
% 3.61/0.99  
% 3.61/0.99  fof(f62,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f22])).
% 3.61/0.99  
% 3.61/0.99  fof(f12,axiom,(
% 3.61/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ((r2_hidden(X2,X0) & v2_funct_1(X3)) => (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f25,plain,(
% 3.61/0.99    ! [X0,X1,X2,X3] : (((k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1) | (~r2_hidden(X2,X0) | ~v2_funct_1(X3))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 3.61/0.99    inference(ennf_transformation,[],[f12])).
% 3.61/0.99  
% 3.61/0.99  fof(f26,plain,(
% 3.61/0.99    ! [X0,X1,X2,X3] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 3.61/0.99    inference(flattening,[],[f25])).
% 3.61/0.99  
% 3.61/0.99  fof(f65,plain,(
% 3.61/0.99    ( ! [X2,X0,X3,X1] : (k1_funct_1(k2_funct_1(X3),k1_funct_1(X3,X2)) = X2 | k1_xboole_0 = X1 | ~r2_hidden(X2,X0) | ~v2_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f26])).
% 3.61/0.99  
% 3.61/0.99  fof(f67,plain,(
% 3.61/0.99    v1_funct_2(sK3,sK2,sK2)),
% 3.61/0.99    inference(cnf_transformation,[],[f43])).
% 3.61/0.99  
% 3.61/0.99  fof(f70,plain,(
% 3.61/0.99    r2_hidden(sK4,sK2) | ~v2_funct_1(sK3)),
% 3.61/0.99    inference(cnf_transformation,[],[f43])).
% 3.61/0.99  
% 3.61/0.99  fof(f1,axiom,(
% 3.61/0.99    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f29,plain,(
% 3.61/0.99    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/0.99    inference(nnf_transformation,[],[f1])).
% 3.61/0.99  
% 3.61/0.99  fof(f30,plain,(
% 3.61/0.99    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.61/0.99    inference(flattening,[],[f29])).
% 3.61/0.99  
% 3.61/0.99  fof(f44,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 3.61/0.99    inference(cnf_transformation,[],[f30])).
% 3.61/0.99  
% 3.61/0.99  fof(f75,plain,(
% 3.61/0.99    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.61/0.99    inference(equality_resolution,[],[f44])).
% 3.61/0.99  
% 3.61/0.99  fof(f46,plain,(
% 3.61/0.99    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f30])).
% 3.61/0.99  
% 3.61/0.99  fof(f59,plain,(
% 3.61/0.99    ( ! [X0] : (v2_funct_1(X0) | sK0(X0) != sK1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f37])).
% 3.61/0.99  
% 3.61/0.99  fof(f73,plain,(
% 3.61/0.99    sK4 != sK5 | ~v2_funct_1(sK3)),
% 3.61/0.99    inference(cnf_transformation,[],[f43])).
% 3.61/0.99  
% 3.61/0.99  fof(f57,plain,(
% 3.61/0.99    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK1(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f37])).
% 3.61/0.99  
% 3.61/0.99  fof(f56,plain,(
% 3.61/0.99    ( ! [X0] : (v2_funct_1(X0) | r2_hidden(sK0(X0),k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f37])).
% 3.61/0.99  
% 3.61/0.99  fof(f55,plain,(
% 3.61/0.99    ( ! [X4,X0,X3] : (X3 = X4 | k1_funct_1(X0,X3) != k1_funct_1(X0,X4) | ~r2_hidden(X4,k1_relat_1(X0)) | ~r2_hidden(X3,k1_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f37])).
% 3.61/0.99  
% 3.61/0.99  fof(f11,axiom,(
% 3.61/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f24,plain,(
% 3.61/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.99    inference(ennf_transformation,[],[f11])).
% 3.61/0.99  
% 3.61/0.99  fof(f64,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f24])).
% 3.61/0.99  
% 3.61/0.99  fof(f10,axiom,(
% 3.61/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f23,plain,(
% 3.61/0.99    ! [X0,X1,X2] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.61/0.99    inference(ennf_transformation,[],[f10])).
% 3.61/0.99  
% 3.61/0.99  fof(f63,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f23])).
% 3.61/0.99  
% 3.61/0.99  fof(f6,axiom,(
% 3.61/0.99    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f16,plain,(
% 3.61/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.61/0.99    inference(ennf_transformation,[],[f6])).
% 3.61/0.99  
% 3.61/0.99  fof(f17,plain,(
% 3.61/0.99    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.61/0.99    inference(flattening,[],[f16])).
% 3.61/0.99  
% 3.61/0.99  fof(f54,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f17])).
% 3.61/0.99  
% 3.61/0.99  fof(f69,plain,(
% 3.61/0.99    ( ! [X4,X5] : (X4 = X5 | k1_funct_1(sK3,X4) != k1_funct_1(sK3,X5) | ~r2_hidden(X5,sK2) | ~r2_hidden(X4,sK2) | v2_funct_1(sK3)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f43])).
% 3.61/0.99  
% 3.61/0.99  fof(f5,axiom,(
% 3.61/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f33,plain,(
% 3.61/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.61/0.99    inference(nnf_transformation,[],[f5])).
% 3.61/0.99  
% 3.61/0.99  fof(f52,plain,(
% 3.61/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f33])).
% 3.61/0.99  
% 3.61/0.99  fof(f3,axiom,(
% 3.61/0.99    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f15,plain,(
% 3.61/0.99    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.61/0.99    inference(ennf_transformation,[],[f3])).
% 3.61/0.99  
% 3.61/0.99  fof(f50,plain,(
% 3.61/0.99    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f15])).
% 3.61/0.99  
% 3.61/0.99  fof(f53,plain,(
% 3.61/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f33])).
% 3.61/0.99  
% 3.61/0.99  fof(f71,plain,(
% 3.61/0.99    r2_hidden(sK5,sK2) | ~v2_funct_1(sK3)),
% 3.61/0.99    inference(cnf_transformation,[],[f43])).
% 3.61/0.99  
% 3.61/0.99  fof(f72,plain,(
% 3.61/0.99    k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) | ~v2_funct_1(sK3)),
% 3.61/0.99    inference(cnf_transformation,[],[f43])).
% 3.61/0.99  
% 3.61/0.99  fof(f4,axiom,(
% 3.61/0.99    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f51,plain,(
% 3.61/0.99    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.61/0.99    inference(cnf_transformation,[],[f4])).
% 3.61/0.99  
% 3.61/0.99  fof(f2,axiom,(
% 3.61/0.99    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f31,plain,(
% 3.61/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.61/0.99    inference(nnf_transformation,[],[f2])).
% 3.61/0.99  
% 3.61/0.99  fof(f32,plain,(
% 3.61/0.99    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.61/0.99    inference(flattening,[],[f31])).
% 3.61/0.99  
% 3.61/0.99  fof(f48,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X0) )),
% 3.61/0.99    inference(cnf_transformation,[],[f32])).
% 3.61/0.99  
% 3.61/0.99  fof(f77,plain,(
% 3.61/0.99    ( ! [X1] : (k2_zfmisc_1(k1_xboole_0,X1) = k1_xboole_0) )),
% 3.61/0.99    inference(equality_resolution,[],[f48])).
% 3.61/0.99  
% 3.61/0.99  fof(f8,axiom,(
% 3.61/0.99    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((r2_hidden(X0,k1_relat_1(X1)) & v2_funct_1(X1)) => (k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0)))),
% 3.61/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.61/0.99  
% 3.61/0.99  fof(f20,plain,(
% 3.61/0.99    ! [X0,X1] : (((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | (~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1))) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 3.61/0.99    inference(ennf_transformation,[],[f8])).
% 3.61/0.99  
% 3.61/0.99  fof(f21,plain,(
% 3.61/0.99    ! [X0,X1] : ((k1_funct_1(k5_relat_1(X1,k2_funct_1(X1)),X0) = X0 & k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0) | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 3.61/0.99    inference(flattening,[],[f20])).
% 3.61/0.99  
% 3.61/0.99  fof(f60,plain,(
% 3.61/0.99    ( ! [X0,X1] : (k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 | ~r2_hidden(X0,k1_relat_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 3.61/0.99    inference(cnf_transformation,[],[f21])).
% 3.61/0.99  
% 3.61/0.99  cnf(c_12,plain,
% 3.61/0.99      ( ~ v1_relat_1(X0)
% 3.61/0.99      | ~ v1_funct_1(X0)
% 3.61/0.99      | v2_funct_1(X0)
% 3.61/0.99      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f58]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_29,negated_conjecture,
% 3.61/0.99      ( v1_funct_1(sK3) ),
% 3.61/0.99      inference(cnf_transformation,[],[f66]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_420,plain,
% 3.61/0.99      ( ~ v1_relat_1(X0)
% 3.61/0.99      | v2_funct_1(X0)
% 3.61/0.99      | k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 3.61/0.99      | sK3 != X0 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_421,plain,
% 3.61/0.99      ( ~ v1_relat_1(sK3)
% 3.61/0.99      | v2_funct_1(sK3)
% 3.61/0.99      | k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3)) ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_420]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3388,plain,
% 3.61/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 3.61/0.99      | v1_relat_1(sK3) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_27,negated_conjecture,
% 3.61/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) ),
% 3.61/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_32,plain,
% 3.61/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_422,plain,
% 3.61/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 3.61/0.99      | v1_relat_1(sK3) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_18,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3660,plain,
% 3.61/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.61/0.99      | v1_relat_1(sK3) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_18]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3661,plain,
% 3.61/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top
% 3.61/0.99      | v1_relat_1(sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_3660]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4206,plain,
% 3.61/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3388,c_32,c_422,c_3661]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_21,plain,
% 3.61/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.61/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | ~ r2_hidden(X3,X1)
% 3.61/0.99      | ~ v1_funct_1(X0)
% 3.61/0.99      | ~ v2_funct_1(X0)
% 3.61/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 3.61/0.99      | k1_xboole_0 = X2 ),
% 3.61/0.99      inference(cnf_transformation,[],[f65]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_28,negated_conjecture,
% 3.61/0.99      ( v1_funct_2(sK3,sK2,sK2) ),
% 3.61/0.99      inference(cnf_transformation,[],[f67]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_365,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | ~ r2_hidden(X3,X1)
% 3.61/0.99      | ~ v1_funct_1(X0)
% 3.61/0.99      | ~ v2_funct_1(X0)
% 3.61/0.99      | k1_funct_1(k2_funct_1(X0),k1_funct_1(X0,X3)) = X3
% 3.61/0.99      | sK2 != X2
% 3.61/0.99      | sK2 != X1
% 3.61/0.99      | sK3 != X0
% 3.61/0.99      | k1_xboole_0 = X2 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_21,c_28]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_366,plain,
% 3.61/0.99      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2)))
% 3.61/0.99      | ~ r2_hidden(X0,sK2)
% 3.61/0.99      | ~ v1_funct_1(sK3)
% 3.61/0.99      | ~ v2_funct_1(sK3)
% 3.61/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 3.61/0.99      | k1_xboole_0 = sK2 ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_365]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_370,plain,
% 3.61/0.99      ( ~ r2_hidden(X0,sK2)
% 3.61/0.99      | ~ v2_funct_1(sK3)
% 3.61/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 3.61/0.99      | k1_xboole_0 = sK2 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_366,c_29,c_27]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2720,plain,
% 3.61/0.99      ( ~ v2_funct_1(sK3) | sP3_iProver_split | k1_xboole_0 = sK2 ),
% 3.61/0.99      inference(splitting,
% 3.61/0.99                [splitting(split),new_symbols(definition,[])],
% 3.61/0.99                [c_370]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3391,plain,
% 3.61/0.99      ( k1_xboole_0 = sK2
% 3.61/0.99      | v2_funct_1(sK3) != iProver_top
% 3.61/0.99      | sP3_iProver_split = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_2720]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4212,plain,
% 3.61/0.99      ( k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.61/0.99      | sK2 = k1_xboole_0
% 3.61/0.99      | sP3_iProver_split = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4206,c_3391]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_25,negated_conjecture,
% 3.61/0.99      ( r2_hidden(sK4,sK2) | ~ v2_funct_1(sK3) ),
% 3.61/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3396,plain,
% 3.61/0.99      ( r2_hidden(sK4,sK2) = iProver_top | v2_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2719,plain,
% 3.61/0.99      ( ~ r2_hidden(X0,sK2)
% 3.61/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 3.61/0.99      | ~ sP3_iProver_split ),
% 3.61/0.99      inference(splitting,
% 3.61/0.99                [splitting(split),new_symbols(definition,[sP3_iProver_split])],
% 3.61/0.99                [c_370]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3392,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 3.61/0.99      | r2_hidden(X0,sK2) != iProver_top
% 3.61/0.99      | sP3_iProver_split != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_2719]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3958,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 3.61/0.99      | v2_funct_1(sK3) != iProver_top
% 3.61/0.99      | sP3_iProver_split != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3396,c_3392]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4213,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 3.61/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.61/0.99      | sP3_iProver_split != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4206,c_3958]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6081,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 3.61/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.61/0.99      | sK2 = k1_xboole_0 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4212,c_4213]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2,plain,( r1_tarski(X0,X0) ),inference(cnf_transformation,[],[f75]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_90,plain,
% 3.61/0.99      ( r1_tarski(sK3,sK3) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_0,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X0 = X1 ),
% 3.61/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_94,plain,
% 3.61/0.99      ( ~ r1_tarski(sK3,sK3) | sK3 = sK3 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11,plain,
% 3.61/0.99      ( ~ v1_relat_1(X0)
% 3.61/0.99      | ~ v1_funct_1(X0)
% 3.61/0.99      | v2_funct_1(X0)
% 3.61/0.99      | sK1(X0) != sK0(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_433,plain,
% 3.61/0.99      ( ~ v1_relat_1(X0) | v2_funct_1(X0) | sK1(X0) != sK0(X0) | sK3 != X0 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_434,plain,
% 3.61/0.99      ( ~ v1_relat_1(sK3) | v2_funct_1(sK3) | sK1(sK3) != sK0(sK3) ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_433]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_22,negated_conjecture,
% 3.61/0.99      ( ~ v2_funct_1(sK3) | sK4 != sK5 ),
% 3.61/0.99      inference(cnf_transformation,[],[f73]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_798,plain,
% 3.61/0.99      ( ~ v1_relat_1(sK3) | sK1(sK3) != sK0(sK3) | sK5 != sK4 ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_434,c_22]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_923,plain,
% 3.61/0.99      ( ~ v1_relat_1(sK3)
% 3.61/0.99      | k1_funct_1(sK3,sK0(sK3)) = k1_funct_1(sK3,sK1(sK3))
% 3.61/0.99      | sK5 != sK4 ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_421,c_22]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_13,plain,
% 3.61/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 3.61/0.99      | ~ v1_relat_1(X0)
% 3.61/0.99      | ~ v1_funct_1(X0)
% 3.61/0.99      | v2_funct_1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f57]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_407,plain,
% 3.61/0.99      ( r2_hidden(sK1(X0),k1_relat_1(X0))
% 3.61/0.99      | ~ v1_relat_1(X0)
% 3.61/0.99      | v2_funct_1(X0)
% 3.61/0.99      | sK3 != X0 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_408,plain,
% 3.61/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 3.61/0.99      | ~ v1_relat_1(sK3)
% 3.61/0.99      | v2_funct_1(sK3) ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_407]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1048,plain,
% 3.61/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) | ~ v1_relat_1(sK3) | sK5 != sK4 ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_408,c_22]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_14,plain,
% 3.61/0.99      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 3.61/0.99      | ~ v1_relat_1(X0)
% 3.61/0.99      | ~ v1_funct_1(X0)
% 3.61/0.99      | v2_funct_1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f56]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_394,plain,
% 3.61/0.99      ( r2_hidden(sK0(X0),k1_relat_1(X0))
% 3.61/0.99      | ~ v1_relat_1(X0)
% 3.61/0.99      | v2_funct_1(X0)
% 3.61/0.99      | sK3 != X0 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_395,plain,
% 3.61/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 3.61/0.99      | ~ v1_relat_1(sK3)
% 3.61/0.99      | v2_funct_1(sK3) ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_394]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_1173,plain,
% 3.61/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) | ~ v1_relat_1(sK3) | sK5 != sK4 ),
% 3.61/0.99      inference(resolution,[status(thm)],[c_395,c_22]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2730,plain,( X0 != X1 | sK1(X0) = sK1(X1) ),theory(equality) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2742,plain,
% 3.61/0.99      ( sK1(sK3) = sK1(sK3) | sK3 != sK3 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_2730]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_15,plain,
% 3.61/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.61/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 3.61/0.99      | ~ v1_relat_1(X1)
% 3.61/0.99      | ~ v1_funct_1(X1)
% 3.61/0.99      | ~ v2_funct_1(X1)
% 3.61/0.99      | X0 = X2
% 3.61/0.99      | k1_funct_1(X1,X0) != k1_funct_1(X1,X2) ),
% 3.61/0.99      inference(cnf_transformation,[],[f55]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_482,plain,
% 3.61/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.61/0.99      | ~ r2_hidden(X2,k1_relat_1(X1))
% 3.61/0.99      | ~ v1_relat_1(X1)
% 3.61/0.99      | ~ v2_funct_1(X1)
% 3.61/0.99      | X2 = X0
% 3.61/0.99      | k1_funct_1(X1,X2) != k1_funct_1(X1,X0)
% 3.61/0.99      | sK3 != X1 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_483,plain,
% 3.61/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.61/0.99      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 3.61/0.99      | ~ v1_relat_1(sK3)
% 3.61/0.99      | ~ v2_funct_1(sK3)
% 3.61/0.99      | X1 = X0
% 3.61/0.99      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_482]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2714,plain,
% 3.61/0.99      ( ~ v1_relat_1(sK3) | ~ v2_funct_1(sK3) | sP0_iProver_split ),
% 3.61/0.99      inference(splitting,
% 3.61/0.99                [splitting(split),new_symbols(definition,[])],
% 3.61/0.99                [c_483]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2723,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3759,plain,
% 3.61/0.99      ( sK1(sK3) != X0 | sK1(sK3) = sK0(sK3) | sK0(sK3) != X0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_2723]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3884,plain,
% 3.61/0.99      ( sK1(sK3) != sK1(sK3) | sK1(sK3) = sK0(sK3) | sK0(sK3) != sK1(sK3) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_3759]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2713,plain,
% 3.61/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.61/0.99      | ~ r2_hidden(X1,k1_relat_1(sK3))
% 3.61/0.99      | X1 = X0
% 3.61/0.99      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0)
% 3.61/0.99      | ~ sP0_iProver_split ),
% 3.61/0.99      inference(splitting,
% 3.61/0.99                [splitting(split),new_symbols(definition,[sP0_iProver_split])],
% 3.61/0.99                [c_483]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4756,plain,
% 3.61/0.99      ( ~ r2_hidden(sK1(X0),k1_relat_1(sK3))
% 3.61/0.99      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 3.61/0.99      | ~ sP0_iProver_split
% 3.61/0.99      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(X0))
% 3.61/0.99      | sK0(sK3) = sK1(X0) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_2713]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4758,plain,
% 3.61/0.99      ( ~ r2_hidden(sK1(sK3),k1_relat_1(sK3))
% 3.61/0.99      | ~ r2_hidden(sK0(sK3),k1_relat_1(sK3))
% 3.61/0.99      | ~ sP0_iProver_split
% 3.61/0.99      | k1_funct_1(sK3,sK0(sK3)) != k1_funct_1(sK3,sK1(sK3))
% 3.61/0.99      | sK0(sK3) = sK1(sK3) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_4756]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3390,plain,
% 3.61/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 3.61/0.99      | v1_relat_1(sK3) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_396,plain,
% 3.61/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 3.61/0.99      | v1_relat_1(sK3) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_395]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4658,plain,
% 3.61/0.99      ( r2_hidden(sK0(sK3),k1_relat_1(sK3)) = iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3390,c_32,c_396,c_3661]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3394,plain,
% 3.61/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_20,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f64]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3400,plain,
% 3.61/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.61/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4942,plain,
% 3.61/0.99      ( k1_relset_1(sK2,sK2,sK3) = k1_relat_1(sK3) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3394,c_3400]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_19,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.61/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f63]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3401,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.61/0.99      | m1_subset_1(k1_relset_1(X1,X2,X0),k1_zfmisc_1(X1)) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5485,plain,
% 3.61/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top
% 3.61/0.99      | m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK2,sK2))) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4942,c_3401]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5744,plain,
% 3.61/0.99      ( m1_subset_1(k1_relat_1(sK3),k1_zfmisc_1(sK2)) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,[status(thm)],[c_5485,c_32]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10,plain,
% 3.61/0.99      ( m1_subset_1(X0,X1)
% 3.61/0.99      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.61/0.99      | ~ r2_hidden(X0,X2) ),
% 3.61/0.99      inference(cnf_transformation,[],[f54]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3403,plain,
% 3.61/0.99      ( m1_subset_1(X0,X1) = iProver_top
% 3.61/0.99      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.61/0.99      | r2_hidden(X0,X2) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5750,plain,
% 3.61/0.99      ( m1_subset_1(X0,sK2) = iProver_top
% 3.61/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_5744,c_3403]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8439,plain,
% 3.61/0.99      ( m1_subset_1(sK0(sK3),sK2) = iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4658,c_5750]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_30,plain,
% 3.61/0.99      ( v1_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_67,plain,
% 3.61/0.99      ( k1_funct_1(X0,sK1(X0)) = k1_funct_1(X0,sK0(X0))
% 3.61/0.99      | v1_relat_1(X0) != iProver_top
% 3.61/0.99      | v1_funct_1(X0) != iProver_top
% 3.61/0.99      | v2_funct_1(X0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_69,plain,
% 3.61/0.99      ( k1_funct_1(sK3,sK1(sK3)) = k1_funct_1(sK3,sK0(sK3))
% 3.61/0.99      | v1_relat_1(sK3) != iProver_top
% 3.61/0.99      | v1_funct_1(sK3) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_67]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_70,plain,
% 3.61/0.99      ( sK1(X0) != sK0(X0)
% 3.61/0.99      | v1_relat_1(X0) != iProver_top
% 3.61/0.99      | v1_funct_1(X0) != iProver_top
% 3.61/0.99      | v2_funct_1(X0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_72,plain,
% 3.61/0.99      ( sK1(sK3) != sK0(sK3)
% 3.61/0.99      | v1_relat_1(sK3) != iProver_top
% 3.61/0.99      | v1_funct_1(sK3) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_70]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_26,negated_conjecture,
% 3.61/0.99      ( ~ r2_hidden(X0,sK2)
% 3.61/0.99      | ~ r2_hidden(X1,sK2)
% 3.61/0.99      | v2_funct_1(sK3)
% 3.61/0.99      | X1 = X0
% 3.61/0.99      | k1_funct_1(sK3,X1) != k1_funct_1(sK3,X0) ),
% 3.61/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3756,plain,
% 3.61/0.99      ( ~ r2_hidden(sK1(sK3),sK2)
% 3.61/0.99      | ~ r2_hidden(sK0(sK3),sK2)
% 3.61/0.99      | v2_funct_1(sK3)
% 3.61/0.99      | k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 3.61/0.99      | sK1(sK3) = sK0(sK3) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_26]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3757,plain,
% 3.61/0.99      ( k1_funct_1(sK3,sK1(sK3)) != k1_funct_1(sK3,sK0(sK3))
% 3.61/0.99      | sK1(sK3) = sK0(sK3)
% 3.61/0.99      | r2_hidden(sK1(sK3),sK2) != iProver_top
% 3.61/0.99      | r2_hidden(sK0(sK3),sK2) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_3756]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f52]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3404,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.61/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5749,plain,
% 3.61/0.99      ( r1_tarski(k1_relat_1(sK3),sK2) = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_5744,c_3404]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3389,plain,
% 3.61/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 3.61/0.99      | v1_relat_1(sK3) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_409,plain,
% 3.61/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 3.61/0.99      | v1_relat_1(sK3) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_408]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4523,plain,
% 3.61/0.99      ( r2_hidden(sK1(sK3),k1_relat_1(sK3)) = iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_3389,c_32,c_409,c_3661]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_6,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.61/0.99      | ~ r2_hidden(X2,X0)
% 3.61/0.99      | r2_hidden(X2,X1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f50]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.61/0.99      inference(cnf_transformation,[],[f53]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_214,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.61/0.99      inference(prop_impl,[status(thm)],[c_8]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_215,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_214]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_272,plain,
% 3.61/0.99      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.61/0.99      inference(bin_hyper_res,[status(thm)],[c_6,c_215]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3393,plain,
% 3.61/0.99      ( r2_hidden(X0,X1) != iProver_top
% 3.61/0.99      | r2_hidden(X0,X2) = iProver_top
% 3.61/0.99      | r1_tarski(X1,X2) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_272]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4786,plain,
% 3.61/0.99      ( r2_hidden(sK1(sK3),X0) = iProver_top
% 3.61/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4523,c_3393]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8309,plain,
% 3.61/0.99      ( r2_hidden(sK1(sK3),sK2) = iProver_top | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_5749,c_4786]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4785,plain,
% 3.61/0.99      ( r2_hidden(sK0(sK3),X0) = iProver_top
% 3.61/0.99      | r1_tarski(k1_relat_1(sK3),X0) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4658,c_3393]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8310,plain,
% 3.61/0.99      ( r2_hidden(sK0(sK3),sK2) = iProver_top | v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_5749,c_4785]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8452,plain,
% 3.61/0.99      ( v2_funct_1(sK3) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_8439,c_30,c_32,c_69,c_72,c_3661,c_3757,c_8309,c_8310]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8454,plain,
% 3.61/0.99      ( v2_funct_1(sK3) ),
% 3.61/0.99      inference(predicate_to_equality_rev,[status(thm)],[c_8452]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8457,plain,
% 3.61/0.99      ( sK2 = k1_xboole_0 | sP3_iProver_split = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_8452,c_3391]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_24,negated_conjecture,
% 3.61/0.99      ( r2_hidden(sK5,sK2) | ~ v2_funct_1(sK3) ),
% 3.61/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3397,plain,
% 3.61/0.99      ( r2_hidden(sK5,sK2) = iProver_top | v2_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3957,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 3.61/0.99      | v2_funct_1(sK3) != iProver_top
% 3.61/0.99      | sP3_iProver_split != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3397,c_3392]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8459,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK5)) = sK5
% 3.61/0.99      | sP3_iProver_split != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_8452,c_3957]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_23,negated_conjecture,
% 3.61/0.99      ( ~ v2_funct_1(sK3) | k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5) ),
% 3.61/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3398,plain,
% 3.61/0.99      ( k1_funct_1(sK3,sK4) = k1_funct_1(sK3,sK5)
% 3.61/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8463,plain,
% 3.61/0.99      ( k1_funct_1(sK3,sK5) = k1_funct_1(sK3,sK4) ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_8452,c_3398]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8472,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 3.61/0.99      | sP3_iProver_split != iProver_top ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_8459,c_8463]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9292,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK5
% 3.61/0.99      | sK2 = k1_xboole_0 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_8457,c_8472]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_8458,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 3.61/0.99      | sP3_iProver_split != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_8452,c_3958]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9293,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,sK4)) = sK4
% 3.61/0.99      | sK2 = k1_xboole_0 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_8457,c_8458]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9867,plain,
% 3.61/0.99      ( sK2 = k1_xboole_0 | sK5 = sK4 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_9292,c_9293]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9869,plain,
% 3.61/0.99      ( sK2 = k1_xboole_0 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_6081,c_27,c_90,c_94,c_798,c_923,c_1048,c_1173,c_2742,
% 3.61/0.99                 c_2714,c_3660,c_3884,c_4758,c_8454,c_9867]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9890,plain,
% 3.61/0.99      ( r2_hidden(sK5,k1_xboole_0) = iProver_top
% 3.61/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_9869,c_3397]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10250,plain,
% 3.61/0.99      ( r2_hidden(sK5,k1_xboole_0) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_9890,c_30,c_32,c_69,c_72,c_3661,c_3757,c_8309,c_8310]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10255,plain,
% 3.61/0.99      ( r2_hidden(sK5,X0) = iProver_top
% 3.61/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_10250,c_3393]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7,plain,
% 3.61/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.61/0.99      inference(cnf_transformation,[],[f51]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3406,plain,
% 3.61/0.99      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4320,plain,
% 3.61/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3406,c_3404]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4783,plain,
% 3.61/0.99      ( r2_hidden(sK5,X0) = iProver_top
% 3.61/0.99      | r1_tarski(sK2,X0) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3397,c_3393]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9884,plain,
% 3.61/0.99      ( r2_hidden(sK5,X0) = iProver_top
% 3.61/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_9869,c_4783]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11598,plain,
% 3.61/0.99      ( r2_hidden(sK5,X0) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_10255,c_30,c_32,c_69,c_72,c_3661,c_3757,c_4320,c_8309,
% 3.61/0.99                 c_8310,c_9884]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4321,plain,
% 3.61/0.99      ( r1_tarski(sK3,k2_zfmisc_1(sK2,sK2)) = iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3394,c_3404]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3408,plain,
% 3.61/0.99      ( X0 = X1
% 3.61/0.99      | r1_tarski(X0,X1) != iProver_top
% 3.61/0.99      | r1_tarski(X1,X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5648,plain,
% 3.61/0.99      ( k2_zfmisc_1(sK2,sK2) = sK3
% 3.61/0.99      | r1_tarski(k2_zfmisc_1(sK2,sK2),sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_4321,c_3408]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9880,plain,
% 3.61/0.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = sK3
% 3.61/0.99      | r1_tarski(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),sK3) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_9869,c_5648]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4,plain,
% 3.61/0.99      ( k2_zfmisc_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9934,plain,
% 3.61/0.99      ( sK3 = k1_xboole_0 | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_9880,c_4]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4327,plain,
% 3.61/0.99      ( r1_tarski(k1_xboole_0,sK3) = iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_4320]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5232,plain,
% 3.61/0.99      ( ~ r1_tarski(X0,k1_xboole_0)
% 3.61/0.99      | ~ r1_tarski(k1_xboole_0,X0)
% 3.61/0.99      | X0 = k1_xboole_0 ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5233,plain,
% 3.61/0.99      ( X0 = k1_xboole_0
% 3.61/0.99      | r1_tarski(X0,k1_xboole_0) != iProver_top
% 3.61/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_5232]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_5235,plain,
% 3.61/0.99      ( sK3 = k1_xboole_0
% 3.61/0.99      | r1_tarski(sK3,k1_xboole_0) != iProver_top
% 3.61/0.99      | r1_tarski(k1_xboole_0,sK3) != iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_5233]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7458,plain,
% 3.61/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0))
% 3.61/0.99      | r1_tarski(X0,k1_xboole_0) ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_9]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7459,plain,
% 3.61/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.61/0.99      | r1_tarski(X0,k1_xboole_0) = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_7458]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_7461,plain,
% 3.61/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.61/0.99      | r1_tarski(sK3,k1_xboole_0) = iProver_top ),
% 3.61/0.99      inference(instantiation,[status(thm)],[c_7459]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9892,plain,
% 3.61/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_9869,c_3394]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9894,plain,
% 3.61/0.99      ( m1_subset_1(sK3,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_9892,c_4]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11032,plain,
% 3.61/0.99      ( sK3 = k1_xboole_0 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_9934,c_4327,c_5235,c_7461,c_9894]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_17,plain,
% 3.61/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.61/0.99      | ~ v1_relat_1(X1)
% 3.61/0.99      | ~ v1_funct_1(X1)
% 3.61/0.99      | ~ v2_funct_1(X1)
% 3.61/0.99      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0 ),
% 3.61/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_446,plain,
% 3.61/0.99      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.61/0.99      | ~ v1_relat_1(X1)
% 3.61/0.99      | ~ v2_funct_1(X1)
% 3.61/0.99      | k1_funct_1(k2_funct_1(X1),k1_funct_1(X1,X0)) = X0
% 3.61/0.99      | sK3 != X1 ),
% 3.61/0.99      inference(resolution_lifted,[status(thm)],[c_17,c_29]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_447,plain,
% 3.61/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.61/0.99      | ~ v1_relat_1(sK3)
% 3.61/0.99      | ~ v2_funct_1(sK3)
% 3.61/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0 ),
% 3.61/0.99      inference(unflattening,[status(thm)],[c_446]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2717,plain,
% 3.61/0.99      ( ~ r2_hidden(X0,k1_relat_1(sK3))
% 3.61/0.99      | k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 3.61/0.99      | ~ sP2_iProver_split ),
% 3.61/0.99      inference(splitting,
% 3.61/0.99                [splitting(split),new_symbols(definition,[sP2_iProver_split])],
% 3.61/0.99                [c_447]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3386,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(sK3),k1_funct_1(sK3,X0)) = X0
% 3.61/0.99      | r2_hidden(X0,k1_relat_1(sK3)) != iProver_top
% 3.61/0.99      | sP2_iProver_split != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_2717]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11073,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) = X0
% 3.61/0.99      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.61/0.99      | sP2_iProver_split != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_11032,c_3386]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2718,plain,
% 3.61/0.99      ( ~ v1_relat_1(sK3) | ~ v2_funct_1(sK3) | sP2_iProver_split ),
% 3.61/0.99      inference(splitting,
% 3.61/0.99                [splitting(split),new_symbols(definition,[])],
% 3.61/0.99                [c_447]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_2756,plain,
% 3.61/0.99      ( v1_relat_1(sK3) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) != iProver_top
% 3.61/0.99      | sP2_iProver_split = iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_2718]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_12248,plain,
% 3.61/0.99      ( r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top
% 3.61/0.99      | k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) = X0 ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_11073,c_30,c_32,c_69,c_72,c_2756,c_3661,c_3757,c_8309,
% 3.61/0.99                 c_8310]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_12249,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,X0)) = X0
% 3.61/0.99      | r2_hidden(X0,k1_relat_1(k1_xboole_0)) != iProver_top ),
% 3.61/0.99      inference(renaming,[status(thm)],[c_12248]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_12256,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK5)) = sK5 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_11598,c_12249]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11044,plain,
% 3.61/0.99      ( k1_funct_1(k1_xboole_0,sK5) = k1_funct_1(k1_xboole_0,sK4) ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_11032,c_8463]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_12261,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK4)) = sK5 ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_12256,c_11044]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9891,plain,
% 3.61/0.99      ( r2_hidden(sK4,k1_xboole_0) = iProver_top
% 3.61/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_9869,c_3396]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10260,plain,
% 3.61/0.99      ( r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_9891,c_30,c_32,c_69,c_72,c_3661,c_3757,c_8309,c_8310]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_10265,plain,
% 3.61/0.99      ( r2_hidden(sK4,X0) = iProver_top
% 3.61/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_10260,c_3393]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_4784,plain,
% 3.61/0.99      ( r2_hidden(sK4,X0) = iProver_top
% 3.61/0.99      | r1_tarski(sK2,X0) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_3396,c_3393]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_9883,plain,
% 3.61/0.99      ( r2_hidden(sK4,X0) = iProver_top
% 3.61/0.99      | r1_tarski(k1_xboole_0,X0) != iProver_top
% 3.61/0.99      | v2_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_9869,c_4784]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11713,plain,
% 3.61/0.99      ( r2_hidden(sK4,X0) = iProver_top ),
% 3.61/0.99      inference(global_propositional_subsumption,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_10265,c_30,c_32,c_69,c_72,c_3661,c_3757,c_4320,c_8309,
% 3.61/0.99                 c_8310,c_9883]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_12257,plain,
% 3.61/0.99      ( k1_funct_1(k2_funct_1(k1_xboole_0),k1_funct_1(k1_xboole_0,sK4)) = sK4 ),
% 3.61/0.99      inference(superposition,[status(thm)],[c_11713,c_12249]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_13821,plain,
% 3.61/0.99      ( sK5 = sK4 ),
% 3.61/0.99      inference(light_normalisation,[status(thm)],[c_12261,c_12257]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11045,plain,
% 3.61/0.99      ( v2_funct_1(k1_xboole_0) = iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_11032,c_8452]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_3399,plain,
% 3.61/0.99      ( sK4 != sK5 | v2_funct_1(sK3) != iProver_top ),
% 3.61/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11081,plain,
% 3.61/0.99      ( sK5 != sK4 | v2_funct_1(k1_xboole_0) != iProver_top ),
% 3.61/0.99      inference(demodulation,[status(thm)],[c_11032,c_3399]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_11210,plain,
% 3.61/0.99      ( sK5 != sK4 ),
% 3.61/0.99      inference(backward_subsumption_resolution,
% 3.61/0.99                [status(thm)],
% 3.61/0.99                [c_11045,c_11081]) ).
% 3.61/0.99  
% 3.61/0.99  cnf(c_13823,plain,
% 3.61/0.99      ( $false ),
% 3.61/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_13821,c_11210]) ).
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.61/0.99  
% 3.61/0.99  ------                               Statistics
% 3.61/0.99  
% 3.61/0.99  ------ General
% 3.61/0.99  
% 3.61/0.99  abstr_ref_over_cycles:                  0
% 3.61/0.99  abstr_ref_under_cycles:                 0
% 3.61/0.99  gc_basic_clause_elim:                   0
% 3.61/0.99  forced_gc_time:                         0
% 3.61/0.99  parsing_time:                           0.009
% 3.61/0.99  unif_index_cands_time:                  0.
% 3.61/0.99  unif_index_add_time:                    0.
% 3.61/0.99  orderings_time:                         0.
% 3.61/0.99  out_proof_time:                         0.019
% 3.61/0.99  total_time:                             0.447
% 3.61/0.99  num_of_symbols:                         56
% 3.61/0.99  num_of_terms:                           10995
% 3.61/0.99  
% 3.61/0.99  ------ Preprocessing
% 3.61/0.99  
% 3.61/0.99  num_of_splits:                          4
% 3.61/0.99  num_of_split_atoms:                     4
% 3.61/0.99  num_of_reused_defs:                     0
% 3.61/0.99  num_eq_ax_congr_red:                    21
% 3.61/0.99  num_of_sem_filtered_clauses:            1
% 3.61/0.99  num_of_subtypes:                        0
% 3.61/0.99  monotx_restored_types:                  0
% 3.61/0.99  sat_num_of_epr_types:                   0
% 3.61/0.99  sat_num_of_non_cyclic_types:            0
% 3.61/0.99  sat_guarded_non_collapsed_types:        0
% 3.61/0.99  num_pure_diseq_elim:                    0
% 3.61/0.99  simp_replaced_by:                       0
% 3.61/0.99  res_preprocessed:                       147
% 3.61/0.99  prep_upred:                             0
% 3.61/0.99  prep_unflattend:                        24
% 3.61/0.99  smt_new_axioms:                         0
% 3.61/0.99  pred_elim_cands:                        5
% 3.61/0.99  pred_elim:                              2
% 3.61/0.99  pred_elim_cl:                           2
% 3.61/0.99  pred_elim_cycles:                       6
% 3.61/0.99  merged_defs:                            8
% 3.61/0.99  merged_defs_ncl:                        0
% 3.61/0.99  bin_hyper_res:                          9
% 3.61/0.99  prep_cycles:                            4
% 3.61/0.99  pred_elim_time:                         0.046
% 3.61/0.99  splitting_time:                         0.
% 3.61/0.99  sem_filter_time:                        0.
% 3.61/0.99  monotx_time:                            0.001
% 3.61/0.99  subtype_inf_time:                       0.
% 3.61/0.99  
% 3.61/0.99  ------ Problem properties
% 3.61/0.99  
% 3.61/0.99  clauses:                                31
% 3.61/0.99  conjectures:                            6
% 3.61/0.99  epr:                                    10
% 3.61/0.99  horn:                                   25
% 3.61/0.99  ground:                                 13
% 3.61/0.99  unary:                                  5
% 3.61/0.99  binary:                                 9
% 3.61/0.99  lits:                                   78
% 3.61/0.99  lits_eq:                                19
% 3.61/0.99  fd_pure:                                0
% 3.61/0.99  fd_pseudo:                              0
% 3.61/0.99  fd_cond:                                1
% 3.61/0.99  fd_pseudo_cond:                         3
% 3.61/0.99  ac_symbols:                             0
% 3.61/0.99  
% 3.61/0.99  ------ Propositional Solver
% 3.61/0.99  
% 3.61/0.99  prop_solver_calls:                      31
% 3.61/0.99  prop_fast_solver_calls:                 1658
% 3.61/0.99  smt_solver_calls:                       0
% 3.61/0.99  smt_fast_solver_calls:                  0
% 3.61/0.99  prop_num_of_clauses:                    3983
% 3.61/0.99  prop_preprocess_simplified:             9564
% 3.61/0.99  prop_fo_subsumed:                       34
% 3.61/0.99  prop_solver_time:                       0.
% 3.61/0.99  smt_solver_time:                        0.
% 3.61/0.99  smt_fast_solver_time:                   0.
% 3.61/0.99  prop_fast_solver_time:                  0.
% 3.61/0.99  prop_unsat_core_time:                   0.
% 3.61/0.99  
% 3.61/0.99  ------ QBF
% 3.61/0.99  
% 3.61/0.99  qbf_q_res:                              0
% 3.61/0.99  qbf_num_tautologies:                    0
% 3.61/0.99  qbf_prep_cycles:                        0
% 3.61/0.99  
% 3.61/0.99  ------ BMC1
% 3.61/0.99  
% 3.61/0.99  bmc1_current_bound:                     -1
% 3.61/0.99  bmc1_last_solved_bound:                 -1
% 3.61/0.99  bmc1_unsat_core_size:                   -1
% 3.61/0.99  bmc1_unsat_core_parents_size:           -1
% 3.61/0.99  bmc1_merge_next_fun:                    0
% 3.61/0.99  bmc1_unsat_core_clauses_time:           0.
% 3.61/0.99  
% 3.61/0.99  ------ Instantiation
% 3.61/0.99  
% 3.61/0.99  inst_num_of_clauses:                    1137
% 3.61/0.99  inst_num_in_passive:                    168
% 3.61/0.99  inst_num_in_active:                     645
% 3.61/0.99  inst_num_in_unprocessed:                325
% 3.61/0.99  inst_num_of_loops:                      800
% 3.61/0.99  inst_num_of_learning_restarts:          0
% 3.61/0.99  inst_num_moves_active_passive:          150
% 3.61/0.99  inst_lit_activity:                      0
% 3.61/0.99  inst_lit_activity_moves:                0
% 3.61/0.99  inst_num_tautologies:                   0
% 3.61/0.99  inst_num_prop_implied:                  0
% 3.61/0.99  inst_num_existing_simplified:           0
% 3.61/0.99  inst_num_eq_res_simplified:             0
% 3.61/0.99  inst_num_child_elim:                    0
% 3.61/0.99  inst_num_of_dismatching_blockings:      753
% 3.61/0.99  inst_num_of_non_proper_insts:           1739
% 3.61/0.99  inst_num_of_duplicates:                 0
% 3.61/0.99  inst_inst_num_from_inst_to_res:         0
% 3.61/0.99  inst_dismatching_checking_time:         0.
% 3.61/0.99  
% 3.61/0.99  ------ Resolution
% 3.61/0.99  
% 3.61/0.99  res_num_of_clauses:                     0
% 3.61/0.99  res_num_in_passive:                     0
% 3.61/0.99  res_num_in_active:                      0
% 3.61/0.99  res_num_of_loops:                       151
% 3.61/0.99  res_forward_subset_subsumed:            193
% 3.61/0.99  res_backward_subset_subsumed:           6
% 3.61/0.99  res_forward_subsumed:                   0
% 3.61/0.99  res_backward_subsumed:                  0
% 3.61/0.99  res_forward_subsumption_resolution:     0
% 3.61/0.99  res_backward_subsumption_resolution:    0
% 3.61/0.99  res_clause_to_clause_subsumption:       2349
% 3.61/0.99  res_orphan_elimination:                 0
% 3.61/0.99  res_tautology_del:                      158
% 3.61/0.99  res_num_eq_res_simplified:              0
% 3.61/0.99  res_num_sel_changes:                    0
% 3.61/0.99  res_moves_from_active_to_pass:          0
% 3.61/0.99  
% 3.61/0.99  ------ Superposition
% 3.61/0.99  
% 3.61/0.99  sup_time_total:                         0.
% 3.61/0.99  sup_time_generating:                    0.
% 3.61/0.99  sup_time_sim_full:                      0.
% 3.61/0.99  sup_time_sim_immed:                     0.
% 3.61/0.99  
% 3.61/0.99  sup_num_of_clauses:                     244
% 3.61/0.99  sup_num_in_active:                      77
% 3.61/0.99  sup_num_in_passive:                     167
% 3.61/0.99  sup_num_of_loops:                       159
% 3.61/0.99  sup_fw_superposition:                   207
% 3.61/0.99  sup_bw_superposition:                   163
% 3.61/0.99  sup_immediate_simplified:               487
% 3.61/0.99  sup_given_eliminated:                   0
% 3.61/0.99  comparisons_done:                       0
% 3.61/0.99  comparisons_avoided:                    60
% 3.61/0.99  
% 3.61/0.99  ------ Simplifications
% 3.61/0.99  
% 3.61/0.99  
% 3.61/0.99  sim_fw_subset_subsumed:                 66
% 3.61/0.99  sim_bw_subset_subsumed:                 7
% 3.61/0.99  sim_fw_subsumed:                        2
% 3.61/0.99  sim_bw_subsumed:                        20
% 3.61/0.99  sim_fw_subsumption_res:                 1
% 3.61/0.99  sim_bw_subsumption_res:                 2
% 3.61/0.99  sim_tautology_del:                      4
% 3.61/0.99  sim_eq_tautology_del:                   19
% 3.61/0.99  sim_eq_res_simp:                        0
% 3.61/0.99  sim_fw_demodulated:                     44
% 3.61/0.99  sim_bw_demodulated:                     428
% 3.61/0.99  sim_light_normalised:                   11
% 3.61/0.99  sim_joinable_taut:                      0
% 3.61/0.99  sim_joinable_simp:                      0
% 3.61/0.99  sim_ac_normalised:                      0
% 3.61/0.99  sim_smt_subsumption:                    0
% 3.61/0.99  
%------------------------------------------------------------------------------
