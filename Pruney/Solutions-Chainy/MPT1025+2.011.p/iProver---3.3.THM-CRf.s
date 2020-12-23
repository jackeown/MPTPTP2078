%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:02 EST 2020

% Result     : Theorem 3.70s
% Output     : CNFRefutation 3.70s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 873 expanded)
%              Number of clauses        :   93 ( 269 expanded)
%              Number of leaves         :   19 ( 188 expanded)
%              Depth                    :   19
%              Number of atoms          :  611 (4000 expanded)
%              Number of equality atoms :  166 ( 751 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f15,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ( m1_subset_1(X5,X0)
               => ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2) ) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f17,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ( m1_subset_1(X5,X0)
                 => ~ ( k1_funct_1(X3,X5) = X4
                      & r2_hidden(X5,X2) ) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f16])).

fof(f34,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f35,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f34])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK8
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f57,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ m1_subset_1(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ m1_subset_1(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f35,f58,f57])).

fof(f91,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f89,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f59])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f90,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f59])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X3] :
              ( r2_hidden(X3,X1)
              & r2_hidden(k4_tarski(X3,X0),X2)
              & r2_hidden(X3,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ? [X4] :
              ( r2_hidden(X4,X1)
              & r2_hidden(k4_tarski(X4,X0),X2)
              & r2_hidden(X4,k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(rectify,[],[f47])).

fof(f49,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK2(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2)
            & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f69,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK1(X0,X1),X1)
        & r2_hidden(sK1(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK1(X0,X1),X1)
          & r2_hidden(sK1(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f62,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).

fof(f60,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f94,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f77])).

fof(f88,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f59])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f54,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X6,X4),X3)
                              & m1_subset_1(X6,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK3(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK3(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ( r2_hidden(sK3(X1,X2,X3,X4),X1)
                            & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
                            & m1_subset_1(sK3(X1,X2,X3,X4),X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).

fof(f86,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK3(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f85,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f81,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f20])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f84,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( m1_subset_1(sK3(X1,X2,X3,X4),X2)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,negated_conjecture,
    ( ~ m1_subset_1(X0,sK4)
    | ~ r2_hidden(X0,sK6)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_17675,plain,
    ( ~ m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4)
    | ~ r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6)
    | k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) != sK8 ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_30,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1360,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1368,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2546,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1360,c_1368])).

cnf(c_29,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1361,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_2685,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2546,c_1361])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1372,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_19,plain,
    ( v4_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_10,plain,
    ( ~ v4_relat_1(X0,X1)
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_350,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_19,c_10])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_354,plain,
    ( r1_tarski(k1_relat_1(X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_350,c_18])).

cnf(c_355,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k1_relat_1(X0),X1) ),
    inference(renaming,[status(thm)],[c_354])).

cnf(c_1359,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_355])).

cnf(c_1800,plain,
    ( r1_tarski(k1_relat_1(sK7),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_1359])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1379,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2554,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_1800,c_1379])).

cnf(c_3599,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK2(X0,X1,sK7),sK4) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_2554])).

cnf(c_33,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1627,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_18])).

cnf(c_1628,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1627])).

cnf(c_9187,plain,
    ( r2_hidden(sK2(X0,X1,sK7),sK4) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3599,c_33,c_1628])).

cnf(c_9188,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK2(X0,X1,sK7),sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_9187])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1382,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_9196,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_9188,c_1382])).

cnf(c_9580,plain,
    ( v1_xboole_0(sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2685,c_9196])).

cnf(c_9593,plain,
    ( ~ v1_xboole_0(sK4) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_9580])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1374,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_3524,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1374,c_1382])).

cnf(c_8627,plain,
    ( v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2685,c_3524])).

cnf(c_8680,plain,
    ( ~ v1_relat_1(sK7)
    | ~ v1_xboole_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_8627])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_386,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_31])).

cnf(c_387,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK7))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_386])).

cnf(c_1357,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_388,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_387])).

cnf(c_1710,plain,
    ( r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1357,c_33,c_388,c_1628])).

cnf(c_1711,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_1710])).

cnf(c_1731,plain,
    ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1711,c_1382])).

cnf(c_3600,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_relat_1(sK7) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1372,c_1731])).

cnf(c_6752,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_xboole_0(sK7) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3600,c_33,c_1628])).

cnf(c_6764,plain,
    ( v1_xboole_0(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2685,c_6752])).

cnf(c_6771,plain,
    ( ~ v1_xboole_0(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_6764])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK3(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_2729,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK5)))
    | ~ m1_subset_1(sK8,sK5)
    | r2_hidden(sK3(X2,X1,X0,sK8),X2)
    | ~ r2_hidden(sK8,k7_relset_1(X1,sK5,X0,X2))
    | v1_xboole_0(X1)
    | v1_xboole_0(X2)
    | v1_xboole_0(sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_5697,plain,
    ( ~ m1_subset_1(sK8,sK5)
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6)
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_2729])).

cnf(c_26,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1364,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3132,plain,
    ( m1_subset_1(X0,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_1364])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1370,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3276,plain,
    ( v1_xboole_0(sK5) != iProver_top
    | v1_xboole_0(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1360,c_1370])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1369,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2692,plain,
    ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2546,c_1369])).

cnf(c_2938,plain,
    ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2692,c_33])).

cnf(c_8,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1376,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3297,plain,
    ( m1_subset_1(X0,sK5) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2938,c_1376])).

cnf(c_3879,plain,
    ( v1_xboole_0(X1) = iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3132,c_33,c_1628,c_3276,c_3297,c_3600])).

cnf(c_3880,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(renaming,[status(thm)],[c_3879])).

cnf(c_16,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_401,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK7 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_31])).

cnf(c_402,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_401])).

cnf(c_1356,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_403,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_402])).

cnf(c_1652,plain,
    ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
    | k1_funct_1(sK7,X0) = X1 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1356,c_33,c_403,c_1628])).

cnf(c_1653,plain,
    ( k1_funct_1(sK7,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_1652])).

cnf(c_3891,plain,
    ( k1_funct_1(sK7,sK3(X0,sK4,sK7,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_xboole_0(X0) = iProver_top
    | v1_xboole_0(sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_3880,c_1653])).

cnf(c_3931,plain,
    ( k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2685,c_3891])).

cnf(c_3290,plain,
    ( ~ v1_xboole_0(sK5)
    | v1_xboole_0(sK7) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3276])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | m1_subset_1(sK3(X4,X3,X2,X0),X3)
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1363,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | m1_subset_1(sK3(X4,X3,X2,X0),X3) = iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2364,plain,
    ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
    | m1_subset_1(sK8,sK5) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1361,c_1363])).

cnf(c_34,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_1642,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(X0))
    | m1_subset_1(sK8,X0)
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_1791,plain,
    ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | m1_subset_1(sK8,sK5)
    | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(instantiation,[status(thm)],[c_1642])).

cnf(c_1793,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) != iProver_top
    | m1_subset_1(sK8,sK5) = iProver_top
    | r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1791])).

cnf(c_1660,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,X0),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1792,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_1660])).

cnf(c_1795,plain,
    ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) = iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1792])).

cnf(c_2782,plain,
    ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
    | v1_xboole_0(sK5) = iProver_top
    | v1_xboole_0(sK4) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2364,c_33,c_34,c_1793,c_1795])).

cnf(c_2784,plain,
    ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4)
    | v1_xboole_0(sK5)
    | v1_xboole_0(sK4)
    | v1_xboole_0(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_2782])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_17675,c_9593,c_9580,c_8680,c_8627,c_6771,c_5697,c_3931,c_3290,c_2784,c_1792,c_1791,c_1628,c_1627,c_29,c_33,c_30])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:03:19 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.70/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.70/1.00  
% 3.70/1.00  ------  iProver source info
% 3.70/1.00  
% 3.70/1.00  git: date: 2020-06-30 10:37:57 +0100
% 3.70/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.70/1.00  git: non_committed_changes: false
% 3.70/1.00  git: last_make_outside_of_git: false
% 3.70/1.00  
% 3.70/1.00  ------ 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options
% 3.70/1.00  
% 3.70/1.00  --out_options                           all
% 3.70/1.00  --tptp_safe_out                         true
% 3.70/1.00  --problem_path                          ""
% 3.70/1.00  --include_path                          ""
% 3.70/1.00  --clausifier                            res/vclausify_rel
% 3.70/1.00  --clausifier_options                    --mode clausify
% 3.70/1.00  --stdin                                 false
% 3.70/1.00  --stats_out                             all
% 3.70/1.00  
% 3.70/1.00  ------ General Options
% 3.70/1.00  
% 3.70/1.00  --fof                                   false
% 3.70/1.00  --time_out_real                         305.
% 3.70/1.00  --time_out_virtual                      -1.
% 3.70/1.00  --symbol_type_check                     false
% 3.70/1.00  --clausify_out                          false
% 3.70/1.00  --sig_cnt_out                           false
% 3.70/1.00  --trig_cnt_out                          false
% 3.70/1.00  --trig_cnt_out_tolerance                1.
% 3.70/1.00  --trig_cnt_out_sk_spl                   false
% 3.70/1.00  --abstr_cl_out                          false
% 3.70/1.00  
% 3.70/1.00  ------ Global Options
% 3.70/1.00  
% 3.70/1.00  --schedule                              default
% 3.70/1.00  --add_important_lit                     false
% 3.70/1.00  --prop_solver_per_cl                    1000
% 3.70/1.00  --min_unsat_core                        false
% 3.70/1.00  --soft_assumptions                      false
% 3.70/1.00  --soft_lemma_size                       3
% 3.70/1.00  --prop_impl_unit_size                   0
% 3.70/1.00  --prop_impl_unit                        []
% 3.70/1.00  --share_sel_clauses                     true
% 3.70/1.00  --reset_solvers                         false
% 3.70/1.00  --bc_imp_inh                            [conj_cone]
% 3.70/1.00  --conj_cone_tolerance                   3.
% 3.70/1.00  --extra_neg_conj                        none
% 3.70/1.00  --large_theory_mode                     true
% 3.70/1.00  --prolific_symb_bound                   200
% 3.70/1.00  --lt_threshold                          2000
% 3.70/1.00  --clause_weak_htbl                      true
% 3.70/1.00  --gc_record_bc_elim                     false
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing Options
% 3.70/1.00  
% 3.70/1.00  --preprocessing_flag                    true
% 3.70/1.00  --time_out_prep_mult                    0.1
% 3.70/1.00  --splitting_mode                        input
% 3.70/1.00  --splitting_grd                         true
% 3.70/1.00  --splitting_cvd                         false
% 3.70/1.00  --splitting_cvd_svl                     false
% 3.70/1.00  --splitting_nvd                         32
% 3.70/1.00  --sub_typing                            true
% 3.70/1.00  --prep_gs_sim                           true
% 3.70/1.00  --prep_unflatten                        true
% 3.70/1.00  --prep_res_sim                          true
% 3.70/1.00  --prep_upred                            true
% 3.70/1.00  --prep_sem_filter                       exhaustive
% 3.70/1.00  --prep_sem_filter_out                   false
% 3.70/1.00  --pred_elim                             true
% 3.70/1.00  --res_sim_input                         true
% 3.70/1.00  --eq_ax_congr_red                       true
% 3.70/1.00  --pure_diseq_elim                       true
% 3.70/1.00  --brand_transform                       false
% 3.70/1.00  --non_eq_to_eq                          false
% 3.70/1.00  --prep_def_merge                        true
% 3.70/1.00  --prep_def_merge_prop_impl              false
% 3.70/1.00  --prep_def_merge_mbd                    true
% 3.70/1.00  --prep_def_merge_tr_red                 false
% 3.70/1.00  --prep_def_merge_tr_cl                  false
% 3.70/1.00  --smt_preprocessing                     true
% 3.70/1.00  --smt_ac_axioms                         fast
% 3.70/1.00  --preprocessed_out                      false
% 3.70/1.00  --preprocessed_stats                    false
% 3.70/1.00  
% 3.70/1.00  ------ Abstraction refinement Options
% 3.70/1.00  
% 3.70/1.00  --abstr_ref                             []
% 3.70/1.00  --abstr_ref_prep                        false
% 3.70/1.00  --abstr_ref_until_sat                   false
% 3.70/1.00  --abstr_ref_sig_restrict                funpre
% 3.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.00  --abstr_ref_under                       []
% 3.70/1.00  
% 3.70/1.00  ------ SAT Options
% 3.70/1.00  
% 3.70/1.00  --sat_mode                              false
% 3.70/1.00  --sat_fm_restart_options                ""
% 3.70/1.00  --sat_gr_def                            false
% 3.70/1.00  --sat_epr_types                         true
% 3.70/1.00  --sat_non_cyclic_types                  false
% 3.70/1.00  --sat_finite_models                     false
% 3.70/1.00  --sat_fm_lemmas                         false
% 3.70/1.00  --sat_fm_prep                           false
% 3.70/1.00  --sat_fm_uc_incr                        true
% 3.70/1.00  --sat_out_model                         small
% 3.70/1.00  --sat_out_clauses                       false
% 3.70/1.00  
% 3.70/1.00  ------ QBF Options
% 3.70/1.00  
% 3.70/1.00  --qbf_mode                              false
% 3.70/1.00  --qbf_elim_univ                         false
% 3.70/1.00  --qbf_dom_inst                          none
% 3.70/1.00  --qbf_dom_pre_inst                      false
% 3.70/1.00  --qbf_sk_in                             false
% 3.70/1.00  --qbf_pred_elim                         true
% 3.70/1.00  --qbf_split                             512
% 3.70/1.00  
% 3.70/1.00  ------ BMC1 Options
% 3.70/1.00  
% 3.70/1.00  --bmc1_incremental                      false
% 3.70/1.00  --bmc1_axioms                           reachable_all
% 3.70/1.00  --bmc1_min_bound                        0
% 3.70/1.00  --bmc1_max_bound                        -1
% 3.70/1.00  --bmc1_max_bound_default                -1
% 3.70/1.00  --bmc1_symbol_reachability              true
% 3.70/1.00  --bmc1_property_lemmas                  false
% 3.70/1.00  --bmc1_k_induction                      false
% 3.70/1.00  --bmc1_non_equiv_states                 false
% 3.70/1.00  --bmc1_deadlock                         false
% 3.70/1.00  --bmc1_ucm                              false
% 3.70/1.00  --bmc1_add_unsat_core                   none
% 3.70/1.00  --bmc1_unsat_core_children              false
% 3.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.00  --bmc1_out_stat                         full
% 3.70/1.00  --bmc1_ground_init                      false
% 3.70/1.00  --bmc1_pre_inst_next_state              false
% 3.70/1.00  --bmc1_pre_inst_state                   false
% 3.70/1.00  --bmc1_pre_inst_reach_state             false
% 3.70/1.00  --bmc1_out_unsat_core                   false
% 3.70/1.00  --bmc1_aig_witness_out                  false
% 3.70/1.00  --bmc1_verbose                          false
% 3.70/1.00  --bmc1_dump_clauses_tptp                false
% 3.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.00  --bmc1_dump_file                        -
% 3.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.00  --bmc1_ucm_extend_mode                  1
% 3.70/1.00  --bmc1_ucm_init_mode                    2
% 3.70/1.00  --bmc1_ucm_cone_mode                    none
% 3.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.00  --bmc1_ucm_relax_model                  4
% 3.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.00  --bmc1_ucm_layered_model                none
% 3.70/1.00  --bmc1_ucm_max_lemma_size               10
% 3.70/1.00  
% 3.70/1.00  ------ AIG Options
% 3.70/1.00  
% 3.70/1.00  --aig_mode                              false
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation Options
% 3.70/1.00  
% 3.70/1.00  --instantiation_flag                    true
% 3.70/1.00  --inst_sos_flag                         false
% 3.70/1.00  --inst_sos_phase                        true
% 3.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel_side                     num_symb
% 3.70/1.00  --inst_solver_per_active                1400
% 3.70/1.00  --inst_solver_calls_frac                1.
% 3.70/1.00  --inst_passive_queue_type               priority_queues
% 3.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.00  --inst_passive_queues_freq              [25;2]
% 3.70/1.00  --inst_dismatching                      true
% 3.70/1.00  --inst_eager_unprocessed_to_passive     true
% 3.70/1.00  --inst_prop_sim_given                   true
% 3.70/1.00  --inst_prop_sim_new                     false
% 3.70/1.00  --inst_subs_new                         false
% 3.70/1.00  --inst_eq_res_simp                      false
% 3.70/1.00  --inst_subs_given                       false
% 3.70/1.00  --inst_orphan_elimination               true
% 3.70/1.00  --inst_learning_loop_flag               true
% 3.70/1.00  --inst_learning_start                   3000
% 3.70/1.00  --inst_learning_factor                  2
% 3.70/1.00  --inst_start_prop_sim_after_learn       3
% 3.70/1.00  --inst_sel_renew                        solver
% 3.70/1.00  --inst_lit_activity_flag                true
% 3.70/1.00  --inst_restr_to_given                   false
% 3.70/1.00  --inst_activity_threshold               500
% 3.70/1.00  --inst_out_proof                        true
% 3.70/1.00  
% 3.70/1.00  ------ Resolution Options
% 3.70/1.00  
% 3.70/1.00  --resolution_flag                       true
% 3.70/1.00  --res_lit_sel                           adaptive
% 3.70/1.00  --res_lit_sel_side                      none
% 3.70/1.00  --res_ordering                          kbo
% 3.70/1.00  --res_to_prop_solver                    active
% 3.70/1.00  --res_prop_simpl_new                    false
% 3.70/1.00  --res_prop_simpl_given                  true
% 3.70/1.00  --res_passive_queue_type                priority_queues
% 3.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.00  --res_passive_queues_freq               [15;5]
% 3.70/1.00  --res_forward_subs                      full
% 3.70/1.00  --res_backward_subs                     full
% 3.70/1.00  --res_forward_subs_resolution           true
% 3.70/1.00  --res_backward_subs_resolution          true
% 3.70/1.00  --res_orphan_elimination                true
% 3.70/1.00  --res_time_limit                        2.
% 3.70/1.00  --res_out_proof                         true
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Options
% 3.70/1.00  
% 3.70/1.00  --superposition_flag                    true
% 3.70/1.00  --sup_passive_queue_type                priority_queues
% 3.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.00  --demod_completeness_check              fast
% 3.70/1.00  --demod_use_ground                      true
% 3.70/1.00  --sup_to_prop_solver                    passive
% 3.70/1.00  --sup_prop_simpl_new                    true
% 3.70/1.00  --sup_prop_simpl_given                  true
% 3.70/1.00  --sup_fun_splitting                     false
% 3.70/1.00  --sup_smt_interval                      50000
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Simplification Setup
% 3.70/1.00  
% 3.70/1.00  --sup_indices_passive                   []
% 3.70/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_full_bw                           [BwDemod]
% 3.70/1.00  --sup_immed_triv                        [TrivRules]
% 3.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_immed_bw_main                     []
% 3.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.00  
% 3.70/1.00  ------ Combination Options
% 3.70/1.00  
% 3.70/1.00  --comb_res_mult                         3
% 3.70/1.00  --comb_sup_mult                         2
% 3.70/1.00  --comb_inst_mult                        10
% 3.70/1.00  
% 3.70/1.00  ------ Debug Options
% 3.70/1.00  
% 3.70/1.00  --dbg_backtrace                         false
% 3.70/1.00  --dbg_dump_prop_clauses                 false
% 3.70/1.00  --dbg_dump_prop_clauses_file            -
% 3.70/1.00  --dbg_out_stat                          false
% 3.70/1.00  ------ Parsing...
% 3.70/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.70/1.00  ------ Proving...
% 3.70/1.00  ------ Problem Properties 
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  clauses                                 28
% 3.70/1.00  conjectures                             3
% 3.70/1.00  EPR                                     4
% 3.70/1.00  Horn                                    22
% 3.70/1.00  unary                                   3
% 3.70/1.00  binary                                  8
% 3.70/1.00  lits                                    90
% 3.70/1.00  lits eq                                 4
% 3.70/1.00  fd_pure                                 0
% 3.70/1.00  fd_pseudo                               0
% 3.70/1.00  fd_cond                                 0
% 3.70/1.00  fd_pseudo_cond                          2
% 3.70/1.00  AC symbols                              0
% 3.70/1.00  
% 3.70/1.00  ------ Schedule dynamic 5 is on 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  ------ 
% 3.70/1.00  Current options:
% 3.70/1.00  ------ 
% 3.70/1.00  
% 3.70/1.00  ------ Input Options
% 3.70/1.00  
% 3.70/1.00  --out_options                           all
% 3.70/1.00  --tptp_safe_out                         true
% 3.70/1.00  --problem_path                          ""
% 3.70/1.00  --include_path                          ""
% 3.70/1.00  --clausifier                            res/vclausify_rel
% 3.70/1.00  --clausifier_options                    --mode clausify
% 3.70/1.00  --stdin                                 false
% 3.70/1.00  --stats_out                             all
% 3.70/1.00  
% 3.70/1.00  ------ General Options
% 3.70/1.00  
% 3.70/1.00  --fof                                   false
% 3.70/1.00  --time_out_real                         305.
% 3.70/1.00  --time_out_virtual                      -1.
% 3.70/1.00  --symbol_type_check                     false
% 3.70/1.00  --clausify_out                          false
% 3.70/1.00  --sig_cnt_out                           false
% 3.70/1.00  --trig_cnt_out                          false
% 3.70/1.00  --trig_cnt_out_tolerance                1.
% 3.70/1.00  --trig_cnt_out_sk_spl                   false
% 3.70/1.00  --abstr_cl_out                          false
% 3.70/1.00  
% 3.70/1.00  ------ Global Options
% 3.70/1.00  
% 3.70/1.00  --schedule                              default
% 3.70/1.00  --add_important_lit                     false
% 3.70/1.00  --prop_solver_per_cl                    1000
% 3.70/1.00  --min_unsat_core                        false
% 3.70/1.00  --soft_assumptions                      false
% 3.70/1.00  --soft_lemma_size                       3
% 3.70/1.00  --prop_impl_unit_size                   0
% 3.70/1.00  --prop_impl_unit                        []
% 3.70/1.00  --share_sel_clauses                     true
% 3.70/1.00  --reset_solvers                         false
% 3.70/1.00  --bc_imp_inh                            [conj_cone]
% 3.70/1.00  --conj_cone_tolerance                   3.
% 3.70/1.00  --extra_neg_conj                        none
% 3.70/1.00  --large_theory_mode                     true
% 3.70/1.00  --prolific_symb_bound                   200
% 3.70/1.00  --lt_threshold                          2000
% 3.70/1.00  --clause_weak_htbl                      true
% 3.70/1.00  --gc_record_bc_elim                     false
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing Options
% 3.70/1.00  
% 3.70/1.00  --preprocessing_flag                    true
% 3.70/1.00  --time_out_prep_mult                    0.1
% 3.70/1.00  --splitting_mode                        input
% 3.70/1.00  --splitting_grd                         true
% 3.70/1.00  --splitting_cvd                         false
% 3.70/1.00  --splitting_cvd_svl                     false
% 3.70/1.00  --splitting_nvd                         32
% 3.70/1.00  --sub_typing                            true
% 3.70/1.00  --prep_gs_sim                           true
% 3.70/1.00  --prep_unflatten                        true
% 3.70/1.00  --prep_res_sim                          true
% 3.70/1.00  --prep_upred                            true
% 3.70/1.00  --prep_sem_filter                       exhaustive
% 3.70/1.00  --prep_sem_filter_out                   false
% 3.70/1.00  --pred_elim                             true
% 3.70/1.00  --res_sim_input                         true
% 3.70/1.00  --eq_ax_congr_red                       true
% 3.70/1.00  --pure_diseq_elim                       true
% 3.70/1.00  --brand_transform                       false
% 3.70/1.00  --non_eq_to_eq                          false
% 3.70/1.00  --prep_def_merge                        true
% 3.70/1.00  --prep_def_merge_prop_impl              false
% 3.70/1.00  --prep_def_merge_mbd                    true
% 3.70/1.00  --prep_def_merge_tr_red                 false
% 3.70/1.00  --prep_def_merge_tr_cl                  false
% 3.70/1.00  --smt_preprocessing                     true
% 3.70/1.00  --smt_ac_axioms                         fast
% 3.70/1.00  --preprocessed_out                      false
% 3.70/1.00  --preprocessed_stats                    false
% 3.70/1.00  
% 3.70/1.00  ------ Abstraction refinement Options
% 3.70/1.00  
% 3.70/1.00  --abstr_ref                             []
% 3.70/1.00  --abstr_ref_prep                        false
% 3.70/1.00  --abstr_ref_until_sat                   false
% 3.70/1.00  --abstr_ref_sig_restrict                funpre
% 3.70/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 3.70/1.00  --abstr_ref_under                       []
% 3.70/1.00  
% 3.70/1.00  ------ SAT Options
% 3.70/1.00  
% 3.70/1.00  --sat_mode                              false
% 3.70/1.00  --sat_fm_restart_options                ""
% 3.70/1.00  --sat_gr_def                            false
% 3.70/1.00  --sat_epr_types                         true
% 3.70/1.00  --sat_non_cyclic_types                  false
% 3.70/1.00  --sat_finite_models                     false
% 3.70/1.00  --sat_fm_lemmas                         false
% 3.70/1.00  --sat_fm_prep                           false
% 3.70/1.00  --sat_fm_uc_incr                        true
% 3.70/1.00  --sat_out_model                         small
% 3.70/1.00  --sat_out_clauses                       false
% 3.70/1.00  
% 3.70/1.00  ------ QBF Options
% 3.70/1.00  
% 3.70/1.00  --qbf_mode                              false
% 3.70/1.00  --qbf_elim_univ                         false
% 3.70/1.00  --qbf_dom_inst                          none
% 3.70/1.00  --qbf_dom_pre_inst                      false
% 3.70/1.00  --qbf_sk_in                             false
% 3.70/1.00  --qbf_pred_elim                         true
% 3.70/1.00  --qbf_split                             512
% 3.70/1.00  
% 3.70/1.00  ------ BMC1 Options
% 3.70/1.00  
% 3.70/1.00  --bmc1_incremental                      false
% 3.70/1.00  --bmc1_axioms                           reachable_all
% 3.70/1.00  --bmc1_min_bound                        0
% 3.70/1.00  --bmc1_max_bound                        -1
% 3.70/1.00  --bmc1_max_bound_default                -1
% 3.70/1.00  --bmc1_symbol_reachability              true
% 3.70/1.00  --bmc1_property_lemmas                  false
% 3.70/1.00  --bmc1_k_induction                      false
% 3.70/1.00  --bmc1_non_equiv_states                 false
% 3.70/1.00  --bmc1_deadlock                         false
% 3.70/1.00  --bmc1_ucm                              false
% 3.70/1.00  --bmc1_add_unsat_core                   none
% 3.70/1.00  --bmc1_unsat_core_children              false
% 3.70/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 3.70/1.00  --bmc1_out_stat                         full
% 3.70/1.00  --bmc1_ground_init                      false
% 3.70/1.00  --bmc1_pre_inst_next_state              false
% 3.70/1.00  --bmc1_pre_inst_state                   false
% 3.70/1.00  --bmc1_pre_inst_reach_state             false
% 3.70/1.00  --bmc1_out_unsat_core                   false
% 3.70/1.00  --bmc1_aig_witness_out                  false
% 3.70/1.00  --bmc1_verbose                          false
% 3.70/1.00  --bmc1_dump_clauses_tptp                false
% 3.70/1.00  --bmc1_dump_unsat_core_tptp             false
% 3.70/1.00  --bmc1_dump_file                        -
% 3.70/1.00  --bmc1_ucm_expand_uc_limit              128
% 3.70/1.00  --bmc1_ucm_n_expand_iterations          6
% 3.70/1.00  --bmc1_ucm_extend_mode                  1
% 3.70/1.00  --bmc1_ucm_init_mode                    2
% 3.70/1.00  --bmc1_ucm_cone_mode                    none
% 3.70/1.00  --bmc1_ucm_reduced_relation_type        0
% 3.70/1.00  --bmc1_ucm_relax_model                  4
% 3.70/1.00  --bmc1_ucm_full_tr_after_sat            true
% 3.70/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 3.70/1.00  --bmc1_ucm_layered_model                none
% 3.70/1.00  --bmc1_ucm_max_lemma_size               10
% 3.70/1.00  
% 3.70/1.00  ------ AIG Options
% 3.70/1.00  
% 3.70/1.00  --aig_mode                              false
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation Options
% 3.70/1.00  
% 3.70/1.00  --instantiation_flag                    true
% 3.70/1.00  --inst_sos_flag                         false
% 3.70/1.00  --inst_sos_phase                        true
% 3.70/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.70/1.00  --inst_lit_sel_side                     none
% 3.70/1.00  --inst_solver_per_active                1400
% 3.70/1.00  --inst_solver_calls_frac                1.
% 3.70/1.00  --inst_passive_queue_type               priority_queues
% 3.70/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.70/1.00  --inst_passive_queues_freq              [25;2]
% 3.70/1.00  --inst_dismatching                      true
% 3.70/1.00  --inst_eager_unprocessed_to_passive     true
% 3.70/1.00  --inst_prop_sim_given                   true
% 3.70/1.00  --inst_prop_sim_new                     false
% 3.70/1.00  --inst_subs_new                         false
% 3.70/1.00  --inst_eq_res_simp                      false
% 3.70/1.00  --inst_subs_given                       false
% 3.70/1.00  --inst_orphan_elimination               true
% 3.70/1.00  --inst_learning_loop_flag               true
% 3.70/1.00  --inst_learning_start                   3000
% 3.70/1.00  --inst_learning_factor                  2
% 3.70/1.00  --inst_start_prop_sim_after_learn       3
% 3.70/1.00  --inst_sel_renew                        solver
% 3.70/1.00  --inst_lit_activity_flag                true
% 3.70/1.00  --inst_restr_to_given                   false
% 3.70/1.00  --inst_activity_threshold               500
% 3.70/1.00  --inst_out_proof                        true
% 3.70/1.00  
% 3.70/1.00  ------ Resolution Options
% 3.70/1.00  
% 3.70/1.00  --resolution_flag                       false
% 3.70/1.00  --res_lit_sel                           adaptive
% 3.70/1.00  --res_lit_sel_side                      none
% 3.70/1.00  --res_ordering                          kbo
% 3.70/1.00  --res_to_prop_solver                    active
% 3.70/1.00  --res_prop_simpl_new                    false
% 3.70/1.00  --res_prop_simpl_given                  true
% 3.70/1.00  --res_passive_queue_type                priority_queues
% 3.70/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.70/1.00  --res_passive_queues_freq               [15;5]
% 3.70/1.00  --res_forward_subs                      full
% 3.70/1.00  --res_backward_subs                     full
% 3.70/1.00  --res_forward_subs_resolution           true
% 3.70/1.00  --res_backward_subs_resolution          true
% 3.70/1.00  --res_orphan_elimination                true
% 3.70/1.00  --res_time_limit                        2.
% 3.70/1.00  --res_out_proof                         true
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Options
% 3.70/1.00  
% 3.70/1.00  --superposition_flag                    true
% 3.70/1.00  --sup_passive_queue_type                priority_queues
% 3.70/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.70/1.00  --sup_passive_queues_freq               [8;1;4]
% 3.70/1.00  --demod_completeness_check              fast
% 3.70/1.00  --demod_use_ground                      true
% 3.70/1.00  --sup_to_prop_solver                    passive
% 3.70/1.00  --sup_prop_simpl_new                    true
% 3.70/1.00  --sup_prop_simpl_given                  true
% 3.70/1.00  --sup_fun_splitting                     false
% 3.70/1.00  --sup_smt_interval                      50000
% 3.70/1.00  
% 3.70/1.00  ------ Superposition Simplification Setup
% 3.70/1.00  
% 3.70/1.00  --sup_indices_passive                   []
% 3.70/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.70/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 3.70/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_full_bw                           [BwDemod]
% 3.70/1.00  --sup_immed_triv                        [TrivRules]
% 3.70/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.70/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_immed_bw_main                     []
% 3.70/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 3.70/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.70/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.70/1.00  
% 3.70/1.00  ------ Combination Options
% 3.70/1.00  
% 3.70/1.00  --comb_res_mult                         3
% 3.70/1.00  --comb_sup_mult                         2
% 3.70/1.00  --comb_inst_mult                        10
% 3.70/1.00  
% 3.70/1.00  ------ Debug Options
% 3.70/1.00  
% 3.70/1.00  --dbg_backtrace                         false
% 3.70/1.00  --dbg_dump_prop_clauses                 false
% 3.70/1.00  --dbg_dump_prop_clauses_file            -
% 3.70/1.00  --dbg_out_stat                          false
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  ------ Proving...
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  % SZS status Theorem for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  fof(f15,conjecture,(
% 3.70/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f16,negated_conjecture,(
% 3.70/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.70/1.00    inference(negated_conjecture,[],[f15])).
% 3.70/1.00  
% 3.70/1.00  fof(f17,plain,(
% 3.70/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.70/1.00    inference(pure_predicate_removal,[],[f16])).
% 3.70/1.00  
% 3.70/1.00  fof(f34,plain,(
% 3.70/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 3.70/1.00    inference(ennf_transformation,[],[f17])).
% 3.70/1.00  
% 3.70/1.00  fof(f35,plain,(
% 3.70/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 3.70/1.00    inference(flattening,[],[f34])).
% 3.70/1.00  
% 3.70/1.00  fof(f58,plain,(
% 3.70/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f57,plain,(
% 3.70/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_1(sK7))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f59,plain,(
% 3.70/1.00    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_1(sK7)),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f35,f58,f57])).
% 3.70/1.00  
% 3.70/1.00  fof(f91,plain,(
% 3.70/1.00    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f59])).
% 3.70/1.00  
% 3.70/1.00  fof(f89,plain,(
% 3.70/1.00    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.70/1.00    inference(cnf_transformation,[],[f59])).
% 3.70/1.00  
% 3.70/1.00  fof(f12,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f30,plain,(
% 3.70/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(ennf_transformation,[],[f12])).
% 3.70/1.00  
% 3.70/1.00  fof(f82,plain,(
% 3.70/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f30])).
% 3.70/1.00  
% 3.70/1.00  fof(f90,plain,(
% 3.70/1.00    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 3.70/1.00    inference(cnf_transformation,[],[f59])).
% 3.70/1.00  
% 3.70/1.00  fof(f6,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f23,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.70/1.00    inference(ennf_transformation,[],[f6])).
% 3.70/1.00  
% 3.70/1.00  fof(f47,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.70/1.00    inference(nnf_transformation,[],[f23])).
% 3.70/1.00  
% 3.70/1.00  fof(f48,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.70/1.00    inference(rectify,[],[f47])).
% 3.70/1.00  
% 3.70/1.00  fof(f49,plain,(
% 3.70/1.00    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f50,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK2(X0,X1,X2),X0),X2) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f48,f49])).
% 3.70/1.00  
% 3.70/1.00  fof(f71,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f50])).
% 3.70/1.00  
% 3.70/1.00  fof(f9,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f18,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 3.70/1.00    inference(pure_predicate_removal,[],[f9])).
% 3.70/1.00  
% 3.70/1.00  fof(f27,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(ennf_transformation,[],[f18])).
% 3.70/1.00  
% 3.70/1.00  fof(f79,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f27])).
% 3.70/1.00  
% 3.70/1.00  fof(f5,axiom,(
% 3.70/1.00    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f22,plain,(
% 3.70/1.00    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(ennf_transformation,[],[f5])).
% 3.70/1.00  
% 3.70/1.00  fof(f46,plain,(
% 3.70/1.00    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.70/1.00    inference(nnf_transformation,[],[f22])).
% 3.70/1.00  
% 3.70/1.00  fof(f69,plain,(
% 3.70/1.00    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f46])).
% 3.70/1.00  
% 3.70/1.00  fof(f8,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f26,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(ennf_transformation,[],[f8])).
% 3.70/1.00  
% 3.70/1.00  fof(f78,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f26])).
% 3.70/1.00  
% 3.70/1.00  fof(f2,axiom,(
% 3.70/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f19,plain,(
% 3.70/1.00    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.70/1.00    inference(ennf_transformation,[],[f2])).
% 3.70/1.00  
% 3.70/1.00  fof(f40,plain,(
% 3.70/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.70/1.00    inference(nnf_transformation,[],[f19])).
% 3.70/1.00  
% 3.70/1.00  fof(f41,plain,(
% 3.70/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.70/1.00    inference(rectify,[],[f40])).
% 3.70/1.00  
% 3.70/1.00  fof(f42,plain,(
% 3.70/1.00    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0)))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f43,plain,(
% 3.70/1.00    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK1(X0,X1),X1) & r2_hidden(sK1(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 3.70/1.00  
% 3.70/1.00  fof(f62,plain,(
% 3.70/1.00    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f43])).
% 3.70/1.00  
% 3.70/1.00  fof(f1,axiom,(
% 3.70/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f36,plain,(
% 3.70/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.70/1.00    inference(nnf_transformation,[],[f1])).
% 3.70/1.00  
% 3.70/1.00  fof(f37,plain,(
% 3.70/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.70/1.00    inference(rectify,[],[f36])).
% 3.70/1.00  
% 3.70/1.00  fof(f38,plain,(
% 3.70/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f39,plain,(
% 3.70/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f37,f38])).
% 3.70/1.00  
% 3.70/1.00  fof(f60,plain,(
% 3.70/1.00    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f39])).
% 3.70/1.00  
% 3.70/1.00  fof(f73,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (r2_hidden(sK2(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f50])).
% 3.70/1.00  
% 3.70/1.00  fof(f7,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f24,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.70/1.00    inference(ennf_transformation,[],[f7])).
% 3.70/1.00  
% 3.70/1.00  fof(f25,plain,(
% 3.70/1.00    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.70/1.00    inference(flattening,[],[f24])).
% 3.70/1.00  
% 3.70/1.00  fof(f51,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.70/1.00    inference(nnf_transformation,[],[f25])).
% 3.70/1.00  
% 3.70/1.00  fof(f52,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.70/1.00    inference(flattening,[],[f51])).
% 3.70/1.00  
% 3.70/1.00  fof(f77,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f52])).
% 3.70/1.00  
% 3.70/1.00  fof(f94,plain,(
% 3.70/1.00    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(equality_resolution,[],[f77])).
% 3.70/1.00  
% 3.70/1.00  fof(f88,plain,(
% 3.70/1.00    v1_funct_1(sK7)),
% 3.70/1.00    inference(cnf_transformation,[],[f59])).
% 3.70/1.00  
% 3.70/1.00  fof(f14,axiom,(
% 3.70/1.00    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f33,plain,(
% 3.70/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.70/1.00    inference(ennf_transformation,[],[f14])).
% 3.70/1.00  
% 3.70/1.00  fof(f53,plain,(
% 3.70/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.70/1.00    inference(nnf_transformation,[],[f33])).
% 3.70/1.00  
% 3.70/1.00  fof(f54,plain,(
% 3.70/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.70/1.00    inference(rectify,[],[f53])).
% 3.70/1.00  
% 3.70/1.00  fof(f55,plain,(
% 3.70/1.00    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK3(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK3(X1,X2,X3,X4),X2)))),
% 3.70/1.00    introduced(choice_axiom,[])).
% 3.70/1.00  
% 3.70/1.00  fof(f56,plain,(
% 3.70/1.00    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK3(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK3(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 3.70/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f54,f55])).
% 3.70/1.00  
% 3.70/1.00  fof(f86,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK3(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f56])).
% 3.70/1.00  
% 3.70/1.00  fof(f85,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK3(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f56])).
% 3.70/1.00  
% 3.70/1.00  fof(f10,axiom,(
% 3.70/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f28,plain,(
% 3.70/1.00    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.70/1.00    inference(ennf_transformation,[],[f10])).
% 3.70/1.00  
% 3.70/1.00  fof(f80,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f28])).
% 3.70/1.00  
% 3.70/1.00  fof(f11,axiom,(
% 3.70/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f29,plain,(
% 3.70/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.70/1.00    inference(ennf_transformation,[],[f11])).
% 3.70/1.00  
% 3.70/1.00  fof(f81,plain,(
% 3.70/1.00    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.70/1.00    inference(cnf_transformation,[],[f29])).
% 3.70/1.00  
% 3.70/1.00  fof(f4,axiom,(
% 3.70/1.00    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 3.70/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.70/1.00  
% 3.70/1.00  fof(f20,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 3.70/1.00    inference(ennf_transformation,[],[f4])).
% 3.70/1.00  
% 3.70/1.00  fof(f21,plain,(
% 3.70/1.00    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.70/1.00    inference(flattening,[],[f20])).
% 3.70/1.00  
% 3.70/1.00  fof(f68,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f21])).
% 3.70/1.00  
% 3.70/1.00  fof(f76,plain,(
% 3.70/1.00    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f52])).
% 3.70/1.00  
% 3.70/1.00  fof(f84,plain,(
% 3.70/1.00    ( ! [X4,X2,X0,X3,X1] : (m1_subset_1(sK3(X1,X2,X3,X4),X2) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 3.70/1.00    inference(cnf_transformation,[],[f56])).
% 3.70/1.00  
% 3.70/1.00  cnf(c_28,negated_conjecture,
% 3.70/1.00      ( ~ m1_subset_1(X0,sK4)
% 3.70/1.00      | ~ r2_hidden(X0,sK6)
% 3.70/1.00      | k1_funct_1(sK7,X0) != sK8 ),
% 3.70/1.00      inference(cnf_transformation,[],[f91]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_17675,plain,
% 3.70/1.00      ( ~ m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4)
% 3.70/1.00      | ~ r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6)
% 3.70/1.00      | k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) != sK8 ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_28]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_30,negated_conjecture,
% 3.70/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.70/1.00      inference(cnf_transformation,[],[f89]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1360,plain,
% 3.70/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_22,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.70/1.00      inference(cnf_transformation,[],[f82]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1368,plain,
% 3.70/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.70/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2546,plain,
% 3.70/1.00      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1360,c_1368]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_29,negated_conjecture,
% 3.70/1.00      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f90]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1361,plain,
% 3.70/1.00      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2685,plain,
% 3.70/1.00      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 3.70/1.00      inference(demodulation,[status(thm)],[c_2546,c_1361]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_14,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.70/1.00      | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1))
% 3.70/1.00      | ~ v1_relat_1(X1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f71]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1372,plain,
% 3.70/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.70/1.00      | r2_hidden(sK2(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.70/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_19,plain,
% 3.70/1.00      ( v4_relat_1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.70/1.00      inference(cnf_transformation,[],[f79]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_10,plain,
% 3.70/1.00      ( ~ v4_relat_1(X0,X1)
% 3.70/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f69]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_350,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | r1_tarski(k1_relat_1(X0),X1)
% 3.70/1.00      | ~ v1_relat_1(X0) ),
% 3.70/1.00      inference(resolution,[status(thm)],[c_19,c_10]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_18,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | v1_relat_1(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f78]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_354,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(X0),X1)
% 3.70/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_350,c_18]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_355,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | r1_tarski(k1_relat_1(X0),X1) ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_354]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1359,plain,
% 3.70/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.70/1.00      | r1_tarski(k1_relat_1(X0),X1) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_355]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1800,plain,
% 3.70/1.00      ( r1_tarski(k1_relat_1(sK7),sK4) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1360,c_1359]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_4,plain,
% 3.70/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f62]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1379,plain,
% 3.70/1.00      ( r1_tarski(X0,X1) != iProver_top
% 3.70/1.00      | r2_hidden(X2,X0) != iProver_top
% 3.70/1.00      | r2_hidden(X2,X1) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2554,plain,
% 3.70/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.70/1.00      | r2_hidden(X0,sK4) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1800,c_1379]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3599,plain,
% 3.70/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.70/1.00      | r2_hidden(sK2(X0,X1,sK7),sK4) = iProver_top
% 3.70/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1372,c_2554]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_33,plain,
% 3.70/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1627,plain,
% 3.70/1.00      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.70/1.00      | v1_relat_1(sK7) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_18]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1628,plain,
% 3.70/1.00      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.70/1.00      | v1_relat_1(sK7) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1627]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9187,plain,
% 3.70/1.00      ( r2_hidden(sK2(X0,X1,sK7),sK4) = iProver_top
% 3.70/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_3599,c_33,c_1628]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9188,plain,
% 3.70/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.70/1.00      | r2_hidden(sK2(X0,X1,sK7),sK4) = iProver_top ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_9187]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f60]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1382,plain,
% 3.70/1.00      ( r2_hidden(X0,X1) != iProver_top
% 3.70/1.00      | v1_xboole_0(X1) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9196,plain,
% 3.70/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.70/1.00      | v1_xboole_0(sK4) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_9188,c_1382]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9580,plain,
% 3.70/1.00      ( v1_xboole_0(sK4) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2685,c_9196]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_9593,plain,
% 3.70/1.00      ( ~ v1_xboole_0(sK4) ),
% 3.70/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_9580]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_12,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.70/1.00      | r2_hidden(sK2(X0,X2,X1),X2)
% 3.70/1.00      | ~ v1_relat_1(X1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f73]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1374,plain,
% 3.70/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.70/1.00      | r2_hidden(sK2(X0,X2,X1),X2) = iProver_top
% 3.70/1.00      | v1_relat_1(X1) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3524,plain,
% 3.70/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.70/1.00      | v1_relat_1(X1) != iProver_top
% 3.70/1.00      | v1_xboole_0(X2) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1374,c_1382]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_8627,plain,
% 3.70/1.00      ( v1_relat_1(sK7) != iProver_top
% 3.70/1.00      | v1_xboole_0(sK6) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2685,c_3524]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_8680,plain,
% 3.70/1.00      ( ~ v1_relat_1(sK7) | ~ v1_xboole_0(sK6) ),
% 3.70/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_8627]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_15,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.70/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.70/1.00      | ~ v1_funct_1(X1)
% 3.70/1.00      | ~ v1_relat_1(X1) ),
% 3.70/1.00      inference(cnf_transformation,[],[f94]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_31,negated_conjecture,
% 3.70/1.00      ( v1_funct_1(sK7) ),
% 3.70/1.00      inference(cnf_transformation,[],[f88]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_386,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.70/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.70/1.00      | ~ v1_relat_1(X1)
% 3.70/1.00      | sK7 != X1 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_15,c_31]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_387,plain,
% 3.70/1.00      ( ~ r2_hidden(X0,k1_relat_1(sK7))
% 3.70/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7)
% 3.70/1.00      | ~ v1_relat_1(sK7) ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_386]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1357,plain,
% 3.70/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.70/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 3.70/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_388,plain,
% 3.70/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.70/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 3.70/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_387]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1710,plain,
% 3.70/1.00      ( r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top
% 3.70/1.00      | r2_hidden(X0,k1_relat_1(sK7)) != iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_1357,c_33,c_388,c_1628]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1711,plain,
% 3.70/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.70/1.00      | r2_hidden(k4_tarski(X0,k1_funct_1(sK7,X0)),sK7) = iProver_top ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_1710]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1731,plain,
% 3.70/1.00      ( r2_hidden(X0,k1_relat_1(sK7)) != iProver_top
% 3.70/1.00      | v1_xboole_0(sK7) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1711,c_1382]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3600,plain,
% 3.70/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.70/1.00      | v1_relat_1(sK7) != iProver_top
% 3.70/1.00      | v1_xboole_0(sK7) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1372,c_1731]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6752,plain,
% 3.70/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.70/1.00      | v1_xboole_0(sK7) != iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_3600,c_33,c_1628]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6764,plain,
% 3.70/1.00      ( v1_xboole_0(sK7) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2685,c_6752]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_6771,plain,
% 3.70/1.00      ( ~ v1_xboole_0(sK7) ),
% 3.70/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_6764]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_25,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.70/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.70/1.00      | r2_hidden(sK3(X4,X3,X2,X0),X4)
% 3.70/1.00      | v1_xboole_0(X1)
% 3.70/1.00      | v1_xboole_0(X3)
% 3.70/1.00      | v1_xboole_0(X4) ),
% 3.70/1.00      inference(cnf_transformation,[],[f86]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2729,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK5)))
% 3.70/1.00      | ~ m1_subset_1(sK8,sK5)
% 3.70/1.00      | r2_hidden(sK3(X2,X1,X0,sK8),X2)
% 3.70/1.00      | ~ r2_hidden(sK8,k7_relset_1(X1,sK5,X0,X2))
% 3.70/1.00      | v1_xboole_0(X1)
% 3.70/1.00      | v1_xboole_0(X2)
% 3.70/1.00      | v1_xboole_0(sK5) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_5697,plain,
% 3.70/1.00      ( ~ m1_subset_1(sK8,sK5)
% 3.70/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.70/1.00      | r2_hidden(sK3(sK6,sK4,sK7,sK8),sK6)
% 3.70/1.00      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
% 3.70/1.00      | v1_xboole_0(sK5)
% 3.70/1.00      | v1_xboole_0(sK4)
% 3.70/1.00      | v1_xboole_0(sK6) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_2729]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_26,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.70/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.70/1.00      | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2)
% 3.70/1.00      | v1_xboole_0(X1)
% 3.70/1.00      | v1_xboole_0(X3)
% 3.70/1.00      | v1_xboole_0(X4) ),
% 3.70/1.00      inference(cnf_transformation,[],[f85]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1364,plain,
% 3.70/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.70/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.70/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.70/1.00      | r2_hidden(k4_tarski(sK3(X4,X3,X2,X0),X0),X2) = iProver_top
% 3.70/1.00      | v1_xboole_0(X1) = iProver_top
% 3.70/1.00      | v1_xboole_0(X3) = iProver_top
% 3.70/1.00      | v1_xboole_0(X4) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3132,plain,
% 3.70/1.00      ( m1_subset_1(X0,sK5) != iProver_top
% 3.70/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.70/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.70/1.00      | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
% 3.70/1.00      | v1_xboole_0(X1) = iProver_top
% 3.70/1.00      | v1_xboole_0(sK5) = iProver_top
% 3.70/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2546,c_1364]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_20,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | ~ v1_xboole_0(X2)
% 3.70/1.00      | v1_xboole_0(X0) ),
% 3.70/1.00      inference(cnf_transformation,[],[f80]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1370,plain,
% 3.70/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.70/1.00      | v1_xboole_0(X2) != iProver_top
% 3.70/1.00      | v1_xboole_0(X0) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3276,plain,
% 3.70/1.00      ( v1_xboole_0(sK5) != iProver_top
% 3.70/1.00      | v1_xboole_0(sK7) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1360,c_1370]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_21,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.70/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.70/1.00      inference(cnf_transformation,[],[f81]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1369,plain,
% 3.70/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.70/1.00      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2692,plain,
% 3.70/1.00      ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top
% 3.70/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2546,c_1369]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2938,plain,
% 3.70/1.00      ( m1_subset_1(k9_relat_1(sK7,X0),k1_zfmisc_1(sK5)) = iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_2692,c_33]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_8,plain,
% 3.70/1.00      ( m1_subset_1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 3.70/1.00      | ~ r2_hidden(X0,X2) ),
% 3.70/1.00      inference(cnf_transformation,[],[f68]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1376,plain,
% 3.70/1.00      ( m1_subset_1(X0,X1) = iProver_top
% 3.70/1.00      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 3.70/1.00      | r2_hidden(X0,X2) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3297,plain,
% 3.70/1.00      ( m1_subset_1(X0,sK5) = iProver_top
% 3.70/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2938,c_1376]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3879,plain,
% 3.70/1.00      ( v1_xboole_0(X1) = iProver_top
% 3.70/1.00      | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
% 3.70/1.00      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.70/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_3132,c_33,c_1628,c_3276,c_3297,c_3600]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3880,plain,
% 3.70/1.00      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.70/1.00      | r2_hidden(k4_tarski(sK3(X1,sK4,sK7,X0),X0),sK7) = iProver_top
% 3.70/1.00      | v1_xboole_0(X1) = iProver_top
% 3.70/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_3879]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_16,plain,
% 3.70/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.70/1.00      | ~ v1_funct_1(X2)
% 3.70/1.00      | ~ v1_relat_1(X2)
% 3.70/1.00      | k1_funct_1(X2,X0) = X1 ),
% 3.70/1.00      inference(cnf_transformation,[],[f76]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_401,plain,
% 3.70/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.70/1.00      | ~ v1_relat_1(X2)
% 3.70/1.00      | k1_funct_1(X2,X0) = X1
% 3.70/1.00      | sK7 != X2 ),
% 3.70/1.00      inference(resolution_lifted,[status(thm)],[c_16,c_31]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_402,plain,
% 3.70/1.00      ( ~ r2_hidden(k4_tarski(X0,X1),sK7)
% 3.70/1.00      | ~ v1_relat_1(sK7)
% 3.70/1.00      | k1_funct_1(sK7,X0) = X1 ),
% 3.70/1.00      inference(unflattening,[status(thm)],[c_401]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1356,plain,
% 3.70/1.00      ( k1_funct_1(sK7,X0) = X1
% 3.70/1.00      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.70/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_403,plain,
% 3.70/1.00      ( k1_funct_1(sK7,X0) = X1
% 3.70/1.00      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.70/1.00      | v1_relat_1(sK7) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_402]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1652,plain,
% 3.70/1.00      ( r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top
% 3.70/1.00      | k1_funct_1(sK7,X0) = X1 ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_1356,c_33,c_403,c_1628]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1653,plain,
% 3.70/1.00      ( k1_funct_1(sK7,X0) = X1
% 3.70/1.00      | r2_hidden(k4_tarski(X0,X1),sK7) != iProver_top ),
% 3.70/1.00      inference(renaming,[status(thm)],[c_1652]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3891,plain,
% 3.70/1.00      ( k1_funct_1(sK7,sK3(X0,sK4,sK7,X1)) = X1
% 3.70/1.00      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 3.70/1.00      | v1_xboole_0(X0) = iProver_top
% 3.70/1.00      | v1_xboole_0(sK4) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_3880,c_1653]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3931,plain,
% 3.70/1.00      ( k1_funct_1(sK7,sK3(sK6,sK4,sK7,sK8)) = sK8
% 3.70/1.00      | v1_xboole_0(sK4) = iProver_top
% 3.70/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_2685,c_3891]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_3290,plain,
% 3.70/1.00      ( ~ v1_xboole_0(sK5) | v1_xboole_0(sK7) ),
% 3.70/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_3276]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_27,plain,
% 3.70/1.00      ( ~ m1_subset_1(X0,X1)
% 3.70/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 3.70/1.00      | m1_subset_1(sK3(X4,X3,X2,X0),X3)
% 3.70/1.00      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 3.70/1.00      | v1_xboole_0(X1)
% 3.70/1.00      | v1_xboole_0(X3)
% 3.70/1.00      | v1_xboole_0(X4) ),
% 3.70/1.00      inference(cnf_transformation,[],[f84]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1363,plain,
% 3.70/1.00      ( m1_subset_1(X0,X1) != iProver_top
% 3.70/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 3.70/1.00      | m1_subset_1(sK3(X4,X3,X2,X0),X3) = iProver_top
% 3.70/1.00      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 3.70/1.00      | v1_xboole_0(X1) = iProver_top
% 3.70/1.00      | v1_xboole_0(X3) = iProver_top
% 3.70/1.00      | v1_xboole_0(X4) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2364,plain,
% 3.70/1.00      ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
% 3.70/1.00      | m1_subset_1(sK8,sK5) != iProver_top
% 3.70/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.70/1.00      | v1_xboole_0(sK5) = iProver_top
% 3.70/1.00      | v1_xboole_0(sK4) = iProver_top
% 3.70/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 3.70/1.00      inference(superposition,[status(thm)],[c_1361,c_1363]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_34,plain,
% 3.70/1.00      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1642,plain,
% 3.70/1.00      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(X0))
% 3.70/1.00      | m1_subset_1(sK8,X0)
% 3.70/1.00      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_8]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1791,plain,
% 3.70/1.00      ( ~ m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 3.70/1.00      | m1_subset_1(sK8,sK5)
% 3.70/1.00      | ~ r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1642]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1793,plain,
% 3.70/1.00      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) != iProver_top
% 3.70/1.00      | m1_subset_1(sK8,sK5) = iProver_top
% 3.70/1.00      | r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1791]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1660,plain,
% 3.70/1.00      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,X0),k1_zfmisc_1(sK5))
% 3.70/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_21]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1792,plain,
% 3.70/1.00      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5))
% 3.70/1.00      | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.70/1.00      inference(instantiation,[status(thm)],[c_1660]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_1795,plain,
% 3.70/1.00      ( m1_subset_1(k7_relset_1(sK4,sK5,sK7,sK6),k1_zfmisc_1(sK5)) = iProver_top
% 3.70/1.00      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 3.70/1.00      inference(predicate_to_equality,[status(thm)],[c_1792]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2782,plain,
% 3.70/1.00      ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4) = iProver_top
% 3.70/1.00      | v1_xboole_0(sK5) = iProver_top
% 3.70/1.00      | v1_xboole_0(sK4) = iProver_top
% 3.70/1.00      | v1_xboole_0(sK6) = iProver_top ),
% 3.70/1.00      inference(global_propositional_subsumption,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_2364,c_33,c_34,c_1793,c_1795]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(c_2784,plain,
% 3.70/1.00      ( m1_subset_1(sK3(sK6,sK4,sK7,sK8),sK4)
% 3.70/1.00      | v1_xboole_0(sK5)
% 3.70/1.00      | v1_xboole_0(sK4)
% 3.70/1.00      | v1_xboole_0(sK6) ),
% 3.70/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_2782]) ).
% 3.70/1.00  
% 3.70/1.00  cnf(contradiction,plain,
% 3.70/1.00      ( $false ),
% 3.70/1.00      inference(minisat,
% 3.70/1.00                [status(thm)],
% 3.70/1.00                [c_17675,c_9593,c_9580,c_8680,c_8627,c_6771,c_5697,
% 3.70/1.00                 c_3931,c_3290,c_2784,c_1792,c_1791,c_1628,c_1627,c_29,
% 3.70/1.00                 c_33,c_30]) ).
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 3.70/1.00  
% 3.70/1.00  ------                               Statistics
% 3.70/1.00  
% 3.70/1.00  ------ General
% 3.70/1.00  
% 3.70/1.00  abstr_ref_over_cycles:                  0
% 3.70/1.00  abstr_ref_under_cycles:                 0
% 3.70/1.00  gc_basic_clause_elim:                   0
% 3.70/1.00  forced_gc_time:                         0
% 3.70/1.00  parsing_time:                           0.011
% 3.70/1.00  unif_index_cands_time:                  0.
% 3.70/1.00  unif_index_add_time:                    0.
% 3.70/1.00  orderings_time:                         0.
% 3.70/1.00  out_proof_time:                         0.01
% 3.70/1.00  total_time:                             0.502
% 3.70/1.00  num_of_symbols:                         54
% 3.70/1.00  num_of_terms:                           16602
% 3.70/1.00  
% 3.70/1.00  ------ Preprocessing
% 3.70/1.00  
% 3.70/1.00  num_of_splits:                          0
% 3.70/1.00  num_of_split_atoms:                     0
% 3.70/1.00  num_of_reused_defs:                     0
% 3.70/1.00  num_eq_ax_congr_red:                    49
% 3.70/1.00  num_of_sem_filtered_clauses:            1
% 3.70/1.00  num_of_subtypes:                        0
% 3.70/1.00  monotx_restored_types:                  0
% 3.70/1.00  sat_num_of_epr_types:                   0
% 3.70/1.00  sat_num_of_non_cyclic_types:            0
% 3.70/1.00  sat_guarded_non_collapsed_types:        0
% 3.70/1.00  num_pure_diseq_elim:                    0
% 3.70/1.00  simp_replaced_by:                       0
% 3.70/1.00  res_preprocessed:                       140
% 3.70/1.00  prep_upred:                             0
% 3.70/1.00  prep_unflattend:                        17
% 3.70/1.00  smt_new_axioms:                         0
% 3.70/1.00  pred_elim_cands:                        5
% 3.70/1.00  pred_elim:                              2
% 3.70/1.00  pred_elim_cl:                           3
% 3.70/1.00  pred_elim_cycles:                       4
% 3.70/1.00  merged_defs:                            0
% 3.70/1.00  merged_defs_ncl:                        0
% 3.70/1.00  bin_hyper_res:                          0
% 3.70/1.00  prep_cycles:                            4
% 3.70/1.00  pred_elim_time:                         0.007
% 3.70/1.00  splitting_time:                         0.
% 3.70/1.00  sem_filter_time:                        0.
% 3.70/1.00  monotx_time:                            0.
% 3.70/1.00  subtype_inf_time:                       0.
% 3.70/1.00  
% 3.70/1.00  ------ Problem properties
% 3.70/1.00  
% 3.70/1.00  clauses:                                28
% 3.70/1.00  conjectures:                            3
% 3.70/1.00  epr:                                    4
% 3.70/1.00  horn:                                   22
% 3.70/1.00  ground:                                 2
% 3.70/1.00  unary:                                  3
% 3.70/1.00  binary:                                 8
% 3.70/1.00  lits:                                   90
% 3.70/1.00  lits_eq:                                4
% 3.70/1.00  fd_pure:                                0
% 3.70/1.00  fd_pseudo:                              0
% 3.70/1.00  fd_cond:                                0
% 3.70/1.00  fd_pseudo_cond:                         2
% 3.70/1.00  ac_symbols:                             0
% 3.70/1.00  
% 3.70/1.00  ------ Propositional Solver
% 3.70/1.00  
% 3.70/1.00  prop_solver_calls:                      29
% 3.70/1.00  prop_fast_solver_calls:                 1529
% 3.70/1.00  smt_solver_calls:                       0
% 3.70/1.00  smt_fast_solver_calls:                  0
% 3.70/1.00  prop_num_of_clauses:                    5744
% 3.70/1.00  prop_preprocess_simplified:             14220
% 3.70/1.00  prop_fo_subsumed:                       53
% 3.70/1.00  prop_solver_time:                       0.
% 3.70/1.00  smt_solver_time:                        0.
% 3.70/1.00  smt_fast_solver_time:                   0.
% 3.70/1.00  prop_fast_solver_time:                  0.
% 3.70/1.00  prop_unsat_core_time:                   0.
% 3.70/1.00  
% 3.70/1.00  ------ QBF
% 3.70/1.00  
% 3.70/1.00  qbf_q_res:                              0
% 3.70/1.00  qbf_num_tautologies:                    0
% 3.70/1.00  qbf_prep_cycles:                        0
% 3.70/1.00  
% 3.70/1.00  ------ BMC1
% 3.70/1.00  
% 3.70/1.00  bmc1_current_bound:                     -1
% 3.70/1.00  bmc1_last_solved_bound:                 -1
% 3.70/1.00  bmc1_unsat_core_size:                   -1
% 3.70/1.00  bmc1_unsat_core_parents_size:           -1
% 3.70/1.00  bmc1_merge_next_fun:                    0
% 3.70/1.00  bmc1_unsat_core_clauses_time:           0.
% 3.70/1.00  
% 3.70/1.00  ------ Instantiation
% 3.70/1.00  
% 3.70/1.00  inst_num_of_clauses:                    1500
% 3.70/1.00  inst_num_in_passive:                    882
% 3.70/1.00  inst_num_in_active:                     608
% 3.70/1.00  inst_num_in_unprocessed:                11
% 3.70/1.00  inst_num_of_loops:                      752
% 3.70/1.00  inst_num_of_learning_restarts:          0
% 3.70/1.00  inst_num_moves_active_passive:          140
% 3.70/1.00  inst_lit_activity:                      0
% 3.70/1.00  inst_lit_activity_moves:                0
% 3.70/1.00  inst_num_tautologies:                   0
% 3.70/1.00  inst_num_prop_implied:                  0
% 3.70/1.00  inst_num_existing_simplified:           0
% 3.70/1.00  inst_num_eq_res_simplified:             0
% 3.70/1.00  inst_num_child_elim:                    0
% 3.70/1.00  inst_num_of_dismatching_blockings:      673
% 3.70/1.00  inst_num_of_non_proper_insts:           1522
% 3.70/1.00  inst_num_of_duplicates:                 0
% 3.70/1.00  inst_inst_num_from_inst_to_res:         0
% 3.70/1.00  inst_dismatching_checking_time:         0.
% 3.70/1.00  
% 3.70/1.00  ------ Resolution
% 3.70/1.00  
% 3.70/1.00  res_num_of_clauses:                     0
% 3.70/1.00  res_num_in_passive:                     0
% 3.70/1.00  res_num_in_active:                      0
% 3.70/1.00  res_num_of_loops:                       144
% 3.70/1.00  res_forward_subset_subsumed:            171
% 3.70/1.00  res_backward_subset_subsumed:           8
% 3.70/1.00  res_forward_subsumed:                   0
% 3.70/1.00  res_backward_subsumed:                  0
% 3.70/1.00  res_forward_subsumption_resolution:     0
% 3.70/1.00  res_backward_subsumption_resolution:    0
% 3.70/1.00  res_clause_to_clause_subsumption:       1921
% 3.70/1.00  res_orphan_elimination:                 0
% 3.70/1.00  res_tautology_del:                      117
% 3.70/1.00  res_num_eq_res_simplified:              0
% 3.70/1.00  res_num_sel_changes:                    0
% 3.70/1.00  res_moves_from_active_to_pass:          0
% 3.70/1.00  
% 3.70/1.00  ------ Superposition
% 3.70/1.00  
% 3.70/1.00  sup_time_total:                         0.
% 3.70/1.00  sup_time_generating:                    0.
% 3.70/1.00  sup_time_sim_full:                      0.
% 3.70/1.00  sup_time_sim_immed:                     0.
% 3.70/1.00  
% 3.70/1.00  sup_num_of_clauses:                     396
% 3.70/1.00  sup_num_in_active:                      146
% 3.70/1.00  sup_num_in_passive:                     250
% 3.70/1.00  sup_num_of_loops:                       150
% 3.70/1.00  sup_fw_superposition:                   281
% 3.70/1.00  sup_bw_superposition:                   239
% 3.70/1.00  sup_immediate_simplified:               121
% 3.70/1.00  sup_given_eliminated:                   2
% 3.70/1.00  comparisons_done:                       0
% 3.70/1.00  comparisons_avoided:                    0
% 3.70/1.00  
% 3.70/1.00  ------ Simplifications
% 3.70/1.00  
% 3.70/1.00  
% 3.70/1.00  sim_fw_subset_subsumed:                 46
% 3.70/1.00  sim_bw_subset_subsumed:                 3
% 3.70/1.00  sim_fw_subsumed:                        16
% 3.70/1.00  sim_bw_subsumed:                        26
% 3.70/1.00  sim_fw_subsumption_res:                 15
% 3.70/1.00  sim_bw_subsumption_res:                 2
% 3.70/1.00  sim_tautology_del:                      12
% 3.70/1.00  sim_eq_tautology_del:                   5
% 3.70/1.00  sim_eq_res_simp:                        0
% 3.70/1.00  sim_fw_demodulated:                     0
% 3.70/1.00  sim_bw_demodulated:                     2
% 3.70/1.00  sim_light_normalised:                   24
% 3.70/1.00  sim_joinable_taut:                      0
% 3.70/1.00  sim_joinable_simp:                      0
% 3.70/1.00  sim_ac_normalised:                      0
% 3.70/1.00  sim_smt_subsumption:                    0
% 3.70/1.00  
%------------------------------------------------------------------------------
