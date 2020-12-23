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
% DateTime   : Thu Dec  3 12:08:00 EST 2020

% Result     : Theorem 3.95s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :  188 (1161 expanded)
%              Number of clauses        :  111 ( 396 expanded)
%              Number of leaves         :   20 ( 260 expanded)
%              Depth                    :   22
%              Number of atoms          :  581 (5445 expanded)
%              Number of equality atoms :  253 (1316 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f30,plain,(
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

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f48,plain,(
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
    inference(nnf_transformation,[],[f31])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f16,conjecture,(
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

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f32,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f33,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f32])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK7
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ m1_subset_1(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK6,X5) != X4
              | ~ r2_hidden(X5,sK5)
              | ~ m1_subset_1(X5,sK3) )
          & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ! [X5] :
        ( k1_funct_1(sK6,X5) != sK7
        | ~ r2_hidden(X5,sK5)
        | ~ m1_subset_1(X5,sK3) )
    & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f33,f50,f49])).

fof(f85,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f51])).

fof(f86,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f51])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f42,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK1(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
            & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f61,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f59,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f77,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f87,plain,(
    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f51])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f26])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f84,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f51])).

fof(f88,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) != sK7
      | ~ r2_hidden(X5,sK5)
      | ~ m1_subset_1(X5,sK3) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f35,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).

fof(f53,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f11,axiom,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
         => k1_xboole_0 = k1_funct_1(X1,X2) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
    ? [X1] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(X1,X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(X1) = X0
      & v1_funct_1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f44,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2] :
              ( k1_xboole_0 = k1_funct_1(X1,X2)
              | ~ r2_hidden(X2,X0) )
          & k1_relat_1(X1) = X0
          & v1_funct_1(X1)
          & v1_relat_1(X1) )
     => ( ! [X2] :
            ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
            | ~ r2_hidden(X2,X0) )
        & k1_relat_1(sK2(X0)) = X0
        & v1_funct_1(sK2(X0))
        & v1_relat_1(sK2(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X2] :
          ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
          | ~ r2_hidden(X2,X0) )
      & k1_relat_1(sK2(X0)) = X0
      & v1_funct_1(sK2(X0))
      & v1_relat_1(sK2(X0)) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f44])).

fof(f72,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = k1_funct_1(sK2(X0),X2)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f91,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f75])).

fof(f52,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f60,plain,(
    ! [X0] :
      ( v1_relat_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k1_xboole_0 != k2_zfmisc_1(X0,X1) ) ) ),
    inference(flattening,[],[f38])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k2_zfmisc_1(X0,X1)
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f89,plain,(
    ! [X0] : k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0) ),
    inference(equality_resolution,[],[f57])).

fof(f70,plain,(
    ! [X0] : v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f69,plain,(
    ! [X0] : v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f45])).

fof(f71,plain,(
    ! [X0] : k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f45])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

cnf(c_31,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f78])).

cnf(c_35,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_584,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK3 != X1
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_31,c_35])).

cnf(c_585,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_584])).

cnf(c_34,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_587,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_585,c_34])).

cnf(c_1796,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1800,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3149,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1796,c_1800])).

cnf(c_3389,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_587,c_3149])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1805,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3771,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK6),sK3) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3389,c_1805])).

cnf(c_39,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2057,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_9])).

cnf(c_2194,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2057])).

cnf(c_2195,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2194])).

cnf(c_10,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_4026,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_4027,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4026])).

cnf(c_4072,plain,
    ( r2_hidden(sK1(X0,X1,sK6),sK3) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3771,c_39,c_2195,c_4027])).

cnf(c_4073,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK6),sK3) = iProver_top ),
    inference(renaming,[status(thm)],[c_4072])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1812,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_4083,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK1(X0,X1,sK6),sK3) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4073,c_1812])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1799,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_2525,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1796,c_1799])).

cnf(c_33,negated_conjecture,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1797,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_2816,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2525,c_1797])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1806,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_22,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_36,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_503,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_22,c_36])).

cnf(c_504,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_503])).

cnf(c_1790,plain,
    ( k1_funct_1(sK6,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_504])).

cnf(c_4328,plain,
    ( k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1806,c_1790])).

cnf(c_5125,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4328,c_39,c_2195,c_4027])).

cnf(c_5126,plain,
    ( k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_5125])).

cnf(c_5136,plain,
    ( k1_funct_1(sK6,sK1(sK7,sK5,sK6)) = sK7 ),
    inference(superposition,[status(thm)],[c_2816,c_5126])).

cnf(c_32,negated_conjecture,
    ( ~ m1_subset_1(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,X0) != sK7 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1798,plain,
    ( k1_funct_1(sK6,X0) != sK7
    | m1_subset_1(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_5168,plain,
    ( m1_subset_1(sK1(sK7,sK5,sK6),sK3) != iProver_top
    | r2_hidden(sK1(sK7,sK5,sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_5136,c_1798])).

cnf(c_14268,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK1(sK7,sK5,sK6),sK5) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4083,c_5168])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f65])).

cnf(c_13572,plain,
    ( r2_hidden(sK1(sK7,sK5,sK6),sK5)
    | ~ r2_hidden(sK7,k9_relat_1(sK6,sK5))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_13573,plain,
    ( r2_hidden(sK1(sK7,sK5,sK6),sK5) = iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13572])).

cnf(c_14530,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14268,c_39,c_2195,c_2816,c_4027,c_13573])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1816,plain,
    ( r2_hidden(sK0(X0),X0) = iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1813,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_4539,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) = iProver_top
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1796,c_1813])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_funct_1(sK2(X1),X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1802,plain,
    ( k1_funct_1(sK2(X0),X1) = k1_xboole_0
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4803,plain,
    ( k1_funct_1(sK2(k2_zfmisc_1(sK3,sK4)),X0) = k1_xboole_0
    | r2_hidden(X0,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4539,c_1802])).

cnf(c_4992,plain,
    ( k1_funct_1(sK2(k2_zfmisc_1(sK3,sK4)),sK0(sK6)) = k1_xboole_0
    | v1_xboole_0(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1816,c_4803])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_488,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_36])).

cnf(c_489,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_488])).

cnf(c_1791,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_489])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1815,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2631,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1791,c_1815])).

cnf(c_8,plain,
    ( v1_relat_1(X0)
    | ~ v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2118,plain,
    ( v1_relat_1(sK6)
    | ~ v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_2119,plain,
    ( v1_relat_1(sK6) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2118])).

cnf(c_3136,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2631,c_2119])).

cnf(c_3394,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,sK3) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3389,c_3136])).

cnf(c_4085,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_4073,c_3394])).

cnf(c_3776,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_relat_1(sK6) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1805,c_3136])).

cnf(c_4227,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4085,c_39,c_2195,c_3776,c_4027])).

cnf(c_4236,plain,
    ( v1_xboole_0(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2816,c_4227])).

cnf(c_7411,plain,
    ( k1_funct_1(sK2(k2_zfmisc_1(sK3,sK4)),sK0(sK6)) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4992,c_4236])).

cnf(c_14557,plain,
    ( k1_funct_1(sK2(k2_zfmisc_1(sK3,k1_xboole_0)),sK0(sK6)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14530,c_7411])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f89])).

cnf(c_14637,plain,
    ( k1_funct_1(sK2(k1_xboole_0),sK0(sK6)) = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_14557,c_3])).

cnf(c_19,plain,
    ( v1_funct_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_439,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK2(X2) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_21])).

cnf(c_440,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK2(X1)))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK2(X1),X0)),sK2(X1))
    | ~ v1_relat_1(sK2(X1)) ),
    inference(unflattening,[status(thm)],[c_439])).

cnf(c_20,plain,
    ( v1_relat_1(sK2(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_450,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK2(X1)))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK2(X1),X0)),sK2(X1)) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_440,c_20])).

cnf(c_1794,plain,
    ( r2_hidden(X0,k1_relat_1(sK2(X1))) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK2(X1),X0)),sK2(X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_450])).

cnf(c_18,plain,
    ( k1_relat_1(sK2(X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1904,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK2(X1),X0)),sK2(X1)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1794,c_18])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_1808,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_5213,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK2(X1))) != iProver_top
    | r2_hidden(k1_funct_1(sK2(X1),X0),k9_relat_1(sK2(X1),X2)) = iProver_top
    | v1_relat_1(sK2(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1904,c_1808])).

cnf(c_5239,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(k1_funct_1(sK2(X1),X0),k9_relat_1(sK2(X1),X2)) = iProver_top
    | v1_relat_1(sK2(X1)) != iProver_top ),
    inference(demodulation,[status(thm)],[c_5213,c_18])).

cnf(c_1801,plain,
    ( v1_relat_1(sK2(X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_5418,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r2_hidden(k1_funct_1(sK2(X1),X0),k9_relat_1(sK2(X1),X2)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_5239,c_1801])).

cnf(c_15075,plain,
    ( r2_hidden(sK0(sK6),X0) != iProver_top
    | r2_hidden(sK0(sK6),k1_xboole_0) != iProver_top
    | r2_hidden(k1_xboole_0,k9_relat_1(sK2(k1_xboole_0),X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14637,c_5418])).

cnf(c_15093,plain,
    ( r2_hidden(sK0(sK6),k1_xboole_0) != iProver_top
    | r2_hidden(k1_xboole_0,k9_relat_1(sK2(k1_xboole_0),k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_15075])).

cnf(c_14573,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14530,c_1796])).

cnf(c_14575,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_14573,c_3])).

cnf(c_3770,plain,
    ( r2_hidden(X0,k9_relat_1(sK2(X1),X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,sK2(X1)),X1) = iProver_top
    | v1_relat_1(sK2(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_18,c_1805])).

cnf(c_5337,plain,
    ( r2_hidden(X0,k9_relat_1(sK2(X1),X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,sK2(X1)),X1) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3770,c_1801])).

cnf(c_5342,plain,
    ( r2_hidden(X0,k9_relat_1(sK2(X1),X2)) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_5337,c_1815])).

cnf(c_5393,plain,
    ( r2_hidden(k1_xboole_0,k9_relat_1(sK2(k1_xboole_0),k1_xboole_0)) != iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5342])).

cnf(c_4050,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | r2_hidden(sK0(sK6),X0)
    | ~ r2_hidden(sK0(sK6),sK6) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_4051,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
    | r2_hidden(sK0(sK6),X0) = iProver_top
    | r2_hidden(sK0(sK6),sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4050])).

cnf(c_4053,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
    | r2_hidden(sK0(sK6),sK6) != iProver_top
    | r2_hidden(sK0(sK6),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_4051])).

cnf(c_2186,plain,
    ( r2_hidden(sK0(sK6),sK6)
    | v1_xboole_0(sK6) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_2187,plain,
    ( r2_hidden(sK0(sK6),sK6) = iProver_top
    | v1_xboole_0(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2186])).

cnf(c_2,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_118,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15093,c_14575,c_5393,c_4236,c_4053,c_2187,c_118])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:04:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.95/1.02  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.95/1.02  
% 3.95/1.02  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.95/1.02  
% 3.95/1.02  ------  iProver source info
% 3.95/1.02  
% 3.95/1.02  git: date: 2020-06-30 10:37:57 +0100
% 3.95/1.02  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.95/1.02  git: non_committed_changes: false
% 3.95/1.02  git: last_make_outside_of_git: false
% 3.95/1.02  
% 3.95/1.02  ------ 
% 3.95/1.02  
% 3.95/1.02  ------ Input Options
% 3.95/1.02  
% 3.95/1.02  --out_options                           all
% 3.95/1.02  --tptp_safe_out                         true
% 3.95/1.02  --problem_path                          ""
% 3.95/1.02  --include_path                          ""
% 3.95/1.02  --clausifier                            res/vclausify_rel
% 3.95/1.02  --clausifier_options                    --mode clausify
% 3.95/1.02  --stdin                                 false
% 3.95/1.02  --stats_out                             all
% 3.95/1.02  
% 3.95/1.02  ------ General Options
% 3.95/1.02  
% 3.95/1.02  --fof                                   false
% 3.95/1.02  --time_out_real                         305.
% 3.95/1.02  --time_out_virtual                      -1.
% 3.95/1.02  --symbol_type_check                     false
% 3.95/1.02  --clausify_out                          false
% 3.95/1.02  --sig_cnt_out                           false
% 3.95/1.02  --trig_cnt_out                          false
% 3.95/1.02  --trig_cnt_out_tolerance                1.
% 3.95/1.02  --trig_cnt_out_sk_spl                   false
% 3.95/1.02  --abstr_cl_out                          false
% 3.95/1.02  
% 3.95/1.02  ------ Global Options
% 3.95/1.02  
% 3.95/1.02  --schedule                              default
% 3.95/1.02  --add_important_lit                     false
% 3.95/1.02  --prop_solver_per_cl                    1000
% 3.95/1.02  --min_unsat_core                        false
% 3.95/1.02  --soft_assumptions                      false
% 3.95/1.02  --soft_lemma_size                       3
% 3.95/1.02  --prop_impl_unit_size                   0
% 3.95/1.02  --prop_impl_unit                        []
% 3.95/1.02  --share_sel_clauses                     true
% 3.95/1.02  --reset_solvers                         false
% 3.95/1.02  --bc_imp_inh                            [conj_cone]
% 3.95/1.02  --conj_cone_tolerance                   3.
% 3.95/1.02  --extra_neg_conj                        none
% 3.95/1.02  --large_theory_mode                     true
% 3.95/1.02  --prolific_symb_bound                   200
% 3.95/1.02  --lt_threshold                          2000
% 3.95/1.02  --clause_weak_htbl                      true
% 3.95/1.02  --gc_record_bc_elim                     false
% 3.95/1.02  
% 3.95/1.02  ------ Preprocessing Options
% 3.95/1.02  
% 3.95/1.02  --preprocessing_flag                    true
% 3.95/1.02  --time_out_prep_mult                    0.1
% 3.95/1.02  --splitting_mode                        input
% 3.95/1.02  --splitting_grd                         true
% 3.95/1.02  --splitting_cvd                         false
% 3.95/1.02  --splitting_cvd_svl                     false
% 3.95/1.02  --splitting_nvd                         32
% 3.95/1.02  --sub_typing                            true
% 3.95/1.02  --prep_gs_sim                           true
% 3.95/1.02  --prep_unflatten                        true
% 3.95/1.02  --prep_res_sim                          true
% 3.95/1.02  --prep_upred                            true
% 3.95/1.02  --prep_sem_filter                       exhaustive
% 3.95/1.02  --prep_sem_filter_out                   false
% 3.95/1.02  --pred_elim                             true
% 3.95/1.02  --res_sim_input                         true
% 3.95/1.02  --eq_ax_congr_red                       true
% 3.95/1.02  --pure_diseq_elim                       true
% 3.95/1.02  --brand_transform                       false
% 3.95/1.02  --non_eq_to_eq                          false
% 3.95/1.02  --prep_def_merge                        true
% 3.95/1.02  --prep_def_merge_prop_impl              false
% 3.95/1.02  --prep_def_merge_mbd                    true
% 3.95/1.02  --prep_def_merge_tr_red                 false
% 3.95/1.02  --prep_def_merge_tr_cl                  false
% 3.95/1.02  --smt_preprocessing                     true
% 3.95/1.02  --smt_ac_axioms                         fast
% 3.95/1.02  --preprocessed_out                      false
% 3.95/1.02  --preprocessed_stats                    false
% 3.95/1.02  
% 3.95/1.02  ------ Abstraction refinement Options
% 3.95/1.02  
% 3.95/1.02  --abstr_ref                             []
% 3.95/1.02  --abstr_ref_prep                        false
% 3.95/1.02  --abstr_ref_until_sat                   false
% 3.95/1.02  --abstr_ref_sig_restrict                funpre
% 3.95/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.95/1.02  --abstr_ref_under                       []
% 3.95/1.02  
% 3.95/1.02  ------ SAT Options
% 3.95/1.02  
% 3.95/1.02  --sat_mode                              false
% 3.95/1.02  --sat_fm_restart_options                ""
% 3.95/1.02  --sat_gr_def                            false
% 3.95/1.02  --sat_epr_types                         true
% 3.95/1.02  --sat_non_cyclic_types                  false
% 3.95/1.02  --sat_finite_models                     false
% 3.95/1.02  --sat_fm_lemmas                         false
% 3.95/1.02  --sat_fm_prep                           false
% 3.95/1.02  --sat_fm_uc_incr                        true
% 3.95/1.02  --sat_out_model                         small
% 3.95/1.02  --sat_out_clauses                       false
% 3.95/1.02  
% 3.95/1.02  ------ QBF Options
% 3.95/1.02  
% 3.95/1.02  --qbf_mode                              false
% 3.95/1.02  --qbf_elim_univ                         false
% 3.95/1.02  --qbf_dom_inst                          none
% 3.95/1.02  --qbf_dom_pre_inst                      false
% 3.95/1.02  --qbf_sk_in                             false
% 3.95/1.02  --qbf_pred_elim                         true
% 3.95/1.02  --qbf_split                             512
% 3.95/1.02  
% 3.95/1.02  ------ BMC1 Options
% 3.95/1.02  
% 3.95/1.02  --bmc1_incremental                      false
% 3.95/1.02  --bmc1_axioms                           reachable_all
% 3.95/1.02  --bmc1_min_bound                        0
% 3.95/1.02  --bmc1_max_bound                        -1
% 3.95/1.02  --bmc1_max_bound_default                -1
% 3.95/1.02  --bmc1_symbol_reachability              true
% 3.95/1.02  --bmc1_property_lemmas                  false
% 3.95/1.02  --bmc1_k_induction                      false
% 3.95/1.02  --bmc1_non_equiv_states                 false
% 3.95/1.02  --bmc1_deadlock                         false
% 3.95/1.02  --bmc1_ucm                              false
% 3.95/1.02  --bmc1_add_unsat_core                   none
% 3.95/1.02  --bmc1_unsat_core_children              false
% 3.95/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.95/1.02  --bmc1_out_stat                         full
% 3.95/1.02  --bmc1_ground_init                      false
% 3.95/1.02  --bmc1_pre_inst_next_state              false
% 3.95/1.02  --bmc1_pre_inst_state                   false
% 3.95/1.02  --bmc1_pre_inst_reach_state             false
% 3.95/1.02  --bmc1_out_unsat_core                   false
% 3.95/1.02  --bmc1_aig_witness_out                  false
% 3.95/1.02  --bmc1_verbose                          false
% 3.95/1.02  --bmc1_dump_clauses_tptp                false
% 3.95/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.95/1.02  --bmc1_dump_file                        -
% 3.95/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.95/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.95/1.02  --bmc1_ucm_extend_mode                  1
% 3.95/1.02  --bmc1_ucm_init_mode                    2
% 3.95/1.02  --bmc1_ucm_cone_mode                    none
% 3.95/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.95/1.02  --bmc1_ucm_relax_model                  4
% 3.95/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.95/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.95/1.02  --bmc1_ucm_layered_model                none
% 3.95/1.02  --bmc1_ucm_max_lemma_size               10
% 3.95/1.02  
% 3.95/1.02  ------ AIG Options
% 3.95/1.02  
% 3.95/1.02  --aig_mode                              false
% 3.95/1.02  
% 3.95/1.02  ------ Instantiation Options
% 3.95/1.02  
% 3.95/1.02  --instantiation_flag                    true
% 3.95/1.02  --inst_sos_flag                         false
% 3.95/1.02  --inst_sos_phase                        true
% 3.95/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.95/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.95/1.02  --inst_lit_sel_side                     num_symb
% 3.95/1.02  --inst_solver_per_active                1400
% 3.95/1.02  --inst_solver_calls_frac                1.
% 3.95/1.02  --inst_passive_queue_type               priority_queues
% 3.95/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.95/1.02  --inst_passive_queues_freq              [25;2]
% 3.95/1.02  --inst_dismatching                      true
% 3.95/1.02  --inst_eager_unprocessed_to_passive     true
% 3.95/1.02  --inst_prop_sim_given                   true
% 3.95/1.02  --inst_prop_sim_new                     false
% 3.95/1.02  --inst_subs_new                         false
% 3.95/1.02  --inst_eq_res_simp                      false
% 3.95/1.02  --inst_subs_given                       false
% 3.95/1.02  --inst_orphan_elimination               true
% 3.95/1.02  --inst_learning_loop_flag               true
% 3.95/1.02  --inst_learning_start                   3000
% 3.95/1.02  --inst_learning_factor                  2
% 3.95/1.02  --inst_start_prop_sim_after_learn       3
% 3.95/1.02  --inst_sel_renew                        solver
% 3.95/1.02  --inst_lit_activity_flag                true
% 3.95/1.02  --inst_restr_to_given                   false
% 3.95/1.02  --inst_activity_threshold               500
% 3.95/1.02  --inst_out_proof                        true
% 3.95/1.02  
% 3.95/1.02  ------ Resolution Options
% 3.95/1.02  
% 3.95/1.02  --resolution_flag                       true
% 3.95/1.02  --res_lit_sel                           adaptive
% 3.95/1.02  --res_lit_sel_side                      none
% 3.95/1.02  --res_ordering                          kbo
% 3.95/1.02  --res_to_prop_solver                    active
% 3.95/1.02  --res_prop_simpl_new                    false
% 3.95/1.02  --res_prop_simpl_given                  true
% 3.95/1.02  --res_passive_queue_type                priority_queues
% 3.95/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.95/1.02  --res_passive_queues_freq               [15;5]
% 3.95/1.02  --res_forward_subs                      full
% 3.95/1.02  --res_backward_subs                     full
% 3.95/1.02  --res_forward_subs_resolution           true
% 3.95/1.02  --res_backward_subs_resolution          true
% 3.95/1.02  --res_orphan_elimination                true
% 3.95/1.02  --res_time_limit                        2.
% 3.95/1.02  --res_out_proof                         true
% 3.95/1.02  
% 3.95/1.02  ------ Superposition Options
% 3.95/1.02  
% 3.95/1.02  --superposition_flag                    true
% 3.95/1.02  --sup_passive_queue_type                priority_queues
% 3.95/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.95/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.95/1.02  --demod_completeness_check              fast
% 3.95/1.02  --demod_use_ground                      true
% 3.95/1.02  --sup_to_prop_solver                    passive
% 3.95/1.02  --sup_prop_simpl_new                    true
% 3.95/1.02  --sup_prop_simpl_given                  true
% 3.95/1.02  --sup_fun_splitting                     false
% 3.95/1.02  --sup_smt_interval                      50000
% 3.95/1.02  
% 3.95/1.02  ------ Superposition Simplification Setup
% 3.95/1.02  
% 3.95/1.02  --sup_indices_passive                   []
% 3.95/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.95/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/1.02  --sup_full_bw                           [BwDemod]
% 3.95/1.02  --sup_immed_triv                        [TrivRules]
% 3.95/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/1.02  --sup_immed_bw_main                     []
% 3.95/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.95/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.95/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.95/1.02  
% 3.95/1.02  ------ Combination Options
% 3.95/1.02  
% 3.95/1.02  --comb_res_mult                         3
% 3.95/1.02  --comb_sup_mult                         2
% 3.95/1.02  --comb_inst_mult                        10
% 3.95/1.02  
% 3.95/1.02  ------ Debug Options
% 3.95/1.02  
% 3.95/1.02  --dbg_backtrace                         false
% 3.95/1.02  --dbg_dump_prop_clauses                 false
% 3.95/1.02  --dbg_dump_prop_clauses_file            -
% 3.95/1.02  --dbg_out_stat                          false
% 3.95/1.02  ------ Parsing...
% 3.95/1.02  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.95/1.02  
% 3.95/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.95/1.02  
% 3.95/1.02  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.95/1.02  
% 3.95/1.02  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.95/1.02  ------ Proving...
% 3.95/1.02  ------ Problem Properties 
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  clauses                                 34
% 3.95/1.02  conjectures                             3
% 3.95/1.02  EPR                                     4
% 3.95/1.02  Horn                                    30
% 3.95/1.02  unary                                   8
% 3.95/1.02  binary                                  11
% 3.95/1.02  lits                                    78
% 3.95/1.02  lits eq                                 23
% 3.95/1.02  fd_pure                                 0
% 3.95/1.02  fd_pseudo                               0
% 3.95/1.02  fd_cond                                 3
% 3.95/1.02  fd_pseudo_cond                          2
% 3.95/1.02  AC symbols                              0
% 3.95/1.02  
% 3.95/1.02  ------ Schedule dynamic 5 is on 
% 3.95/1.02  
% 3.95/1.02  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  ------ 
% 3.95/1.02  Current options:
% 3.95/1.02  ------ 
% 3.95/1.02  
% 3.95/1.02  ------ Input Options
% 3.95/1.02  
% 3.95/1.02  --out_options                           all
% 3.95/1.02  --tptp_safe_out                         true
% 3.95/1.02  --problem_path                          ""
% 3.95/1.02  --include_path                          ""
% 3.95/1.02  --clausifier                            res/vclausify_rel
% 3.95/1.02  --clausifier_options                    --mode clausify
% 3.95/1.02  --stdin                                 false
% 3.95/1.02  --stats_out                             all
% 3.95/1.02  
% 3.95/1.02  ------ General Options
% 3.95/1.02  
% 3.95/1.02  --fof                                   false
% 3.95/1.02  --time_out_real                         305.
% 3.95/1.02  --time_out_virtual                      -1.
% 3.95/1.02  --symbol_type_check                     false
% 3.95/1.02  --clausify_out                          false
% 3.95/1.02  --sig_cnt_out                           false
% 3.95/1.02  --trig_cnt_out                          false
% 3.95/1.02  --trig_cnt_out_tolerance                1.
% 3.95/1.02  --trig_cnt_out_sk_spl                   false
% 3.95/1.02  --abstr_cl_out                          false
% 3.95/1.02  
% 3.95/1.02  ------ Global Options
% 3.95/1.02  
% 3.95/1.02  --schedule                              default
% 3.95/1.02  --add_important_lit                     false
% 3.95/1.02  --prop_solver_per_cl                    1000
% 3.95/1.02  --min_unsat_core                        false
% 3.95/1.02  --soft_assumptions                      false
% 3.95/1.02  --soft_lemma_size                       3
% 3.95/1.02  --prop_impl_unit_size                   0
% 3.95/1.02  --prop_impl_unit                        []
% 3.95/1.02  --share_sel_clauses                     true
% 3.95/1.02  --reset_solvers                         false
% 3.95/1.02  --bc_imp_inh                            [conj_cone]
% 3.95/1.02  --conj_cone_tolerance                   3.
% 3.95/1.02  --extra_neg_conj                        none
% 3.95/1.02  --large_theory_mode                     true
% 3.95/1.02  --prolific_symb_bound                   200
% 3.95/1.02  --lt_threshold                          2000
% 3.95/1.02  --clause_weak_htbl                      true
% 3.95/1.02  --gc_record_bc_elim                     false
% 3.95/1.02  
% 3.95/1.02  ------ Preprocessing Options
% 3.95/1.02  
% 3.95/1.02  --preprocessing_flag                    true
% 3.95/1.02  --time_out_prep_mult                    0.1
% 3.95/1.02  --splitting_mode                        input
% 3.95/1.02  --splitting_grd                         true
% 3.95/1.02  --splitting_cvd                         false
% 3.95/1.02  --splitting_cvd_svl                     false
% 3.95/1.02  --splitting_nvd                         32
% 3.95/1.02  --sub_typing                            true
% 3.95/1.02  --prep_gs_sim                           true
% 3.95/1.02  --prep_unflatten                        true
% 3.95/1.02  --prep_res_sim                          true
% 3.95/1.02  --prep_upred                            true
% 3.95/1.02  --prep_sem_filter                       exhaustive
% 3.95/1.02  --prep_sem_filter_out                   false
% 3.95/1.02  --pred_elim                             true
% 3.95/1.02  --res_sim_input                         true
% 3.95/1.02  --eq_ax_congr_red                       true
% 3.95/1.02  --pure_diseq_elim                       true
% 3.95/1.02  --brand_transform                       false
% 3.95/1.02  --non_eq_to_eq                          false
% 3.95/1.02  --prep_def_merge                        true
% 3.95/1.02  --prep_def_merge_prop_impl              false
% 3.95/1.02  --prep_def_merge_mbd                    true
% 3.95/1.02  --prep_def_merge_tr_red                 false
% 3.95/1.02  --prep_def_merge_tr_cl                  false
% 3.95/1.02  --smt_preprocessing                     true
% 3.95/1.02  --smt_ac_axioms                         fast
% 3.95/1.02  --preprocessed_out                      false
% 3.95/1.02  --preprocessed_stats                    false
% 3.95/1.02  
% 3.95/1.02  ------ Abstraction refinement Options
% 3.95/1.02  
% 3.95/1.02  --abstr_ref                             []
% 3.95/1.02  --abstr_ref_prep                        false
% 3.95/1.02  --abstr_ref_until_sat                   false
% 3.95/1.02  --abstr_ref_sig_restrict                funpre
% 3.95/1.02  --abstr_ref_af_restrict_to_split_sk     false
% 3.95/1.02  --abstr_ref_under                       []
% 3.95/1.02  
% 3.95/1.02  ------ SAT Options
% 3.95/1.02  
% 3.95/1.02  --sat_mode                              false
% 3.95/1.02  --sat_fm_restart_options                ""
% 3.95/1.02  --sat_gr_def                            false
% 3.95/1.02  --sat_epr_types                         true
% 3.95/1.02  --sat_non_cyclic_types                  false
% 3.95/1.02  --sat_finite_models                     false
% 3.95/1.02  --sat_fm_lemmas                         false
% 3.95/1.02  --sat_fm_prep                           false
% 3.95/1.02  --sat_fm_uc_incr                        true
% 3.95/1.02  --sat_out_model                         small
% 3.95/1.02  --sat_out_clauses                       false
% 3.95/1.02  
% 3.95/1.02  ------ QBF Options
% 3.95/1.02  
% 3.95/1.02  --qbf_mode                              false
% 3.95/1.02  --qbf_elim_univ                         false
% 3.95/1.02  --qbf_dom_inst                          none
% 3.95/1.02  --qbf_dom_pre_inst                      false
% 3.95/1.02  --qbf_sk_in                             false
% 3.95/1.02  --qbf_pred_elim                         true
% 3.95/1.02  --qbf_split                             512
% 3.95/1.02  
% 3.95/1.02  ------ BMC1 Options
% 3.95/1.02  
% 3.95/1.02  --bmc1_incremental                      false
% 3.95/1.02  --bmc1_axioms                           reachable_all
% 3.95/1.02  --bmc1_min_bound                        0
% 3.95/1.02  --bmc1_max_bound                        -1
% 3.95/1.02  --bmc1_max_bound_default                -1
% 3.95/1.02  --bmc1_symbol_reachability              true
% 3.95/1.02  --bmc1_property_lemmas                  false
% 3.95/1.02  --bmc1_k_induction                      false
% 3.95/1.02  --bmc1_non_equiv_states                 false
% 3.95/1.02  --bmc1_deadlock                         false
% 3.95/1.02  --bmc1_ucm                              false
% 3.95/1.02  --bmc1_add_unsat_core                   none
% 3.95/1.02  --bmc1_unsat_core_children              false
% 3.95/1.02  --bmc1_unsat_core_extrapolate_axioms    false
% 3.95/1.02  --bmc1_out_stat                         full
% 3.95/1.02  --bmc1_ground_init                      false
% 3.95/1.02  --bmc1_pre_inst_next_state              false
% 3.95/1.02  --bmc1_pre_inst_state                   false
% 3.95/1.02  --bmc1_pre_inst_reach_state             false
% 3.95/1.02  --bmc1_out_unsat_core                   false
% 3.95/1.02  --bmc1_aig_witness_out                  false
% 3.95/1.02  --bmc1_verbose                          false
% 3.95/1.02  --bmc1_dump_clauses_tptp                false
% 3.95/1.02  --bmc1_dump_unsat_core_tptp             false
% 3.95/1.02  --bmc1_dump_file                        -
% 3.95/1.02  --bmc1_ucm_expand_uc_limit              128
% 3.95/1.02  --bmc1_ucm_n_expand_iterations          6
% 3.95/1.02  --bmc1_ucm_extend_mode                  1
% 3.95/1.02  --bmc1_ucm_init_mode                    2
% 3.95/1.02  --bmc1_ucm_cone_mode                    none
% 3.95/1.02  --bmc1_ucm_reduced_relation_type        0
% 3.95/1.02  --bmc1_ucm_relax_model                  4
% 3.95/1.02  --bmc1_ucm_full_tr_after_sat            true
% 3.95/1.02  --bmc1_ucm_expand_neg_assumptions       false
% 3.95/1.02  --bmc1_ucm_layered_model                none
% 3.95/1.02  --bmc1_ucm_max_lemma_size               10
% 3.95/1.02  
% 3.95/1.02  ------ AIG Options
% 3.95/1.02  
% 3.95/1.02  --aig_mode                              false
% 3.95/1.02  
% 3.95/1.02  ------ Instantiation Options
% 3.95/1.02  
% 3.95/1.02  --instantiation_flag                    true
% 3.95/1.02  --inst_sos_flag                         false
% 3.95/1.02  --inst_sos_phase                        true
% 3.95/1.02  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.95/1.02  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.95/1.02  --inst_lit_sel_side                     none
% 3.95/1.02  --inst_solver_per_active                1400
% 3.95/1.02  --inst_solver_calls_frac                1.
% 3.95/1.02  --inst_passive_queue_type               priority_queues
% 3.95/1.02  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.95/1.02  --inst_passive_queues_freq              [25;2]
% 3.95/1.02  --inst_dismatching                      true
% 3.95/1.02  --inst_eager_unprocessed_to_passive     true
% 3.95/1.02  --inst_prop_sim_given                   true
% 3.95/1.02  --inst_prop_sim_new                     false
% 3.95/1.02  --inst_subs_new                         false
% 3.95/1.02  --inst_eq_res_simp                      false
% 3.95/1.02  --inst_subs_given                       false
% 3.95/1.02  --inst_orphan_elimination               true
% 3.95/1.02  --inst_learning_loop_flag               true
% 3.95/1.02  --inst_learning_start                   3000
% 3.95/1.02  --inst_learning_factor                  2
% 3.95/1.02  --inst_start_prop_sim_after_learn       3
% 3.95/1.02  --inst_sel_renew                        solver
% 3.95/1.02  --inst_lit_activity_flag                true
% 3.95/1.02  --inst_restr_to_given                   false
% 3.95/1.02  --inst_activity_threshold               500
% 3.95/1.02  --inst_out_proof                        true
% 3.95/1.02  
% 3.95/1.02  ------ Resolution Options
% 3.95/1.02  
% 3.95/1.02  --resolution_flag                       false
% 3.95/1.02  --res_lit_sel                           adaptive
% 3.95/1.02  --res_lit_sel_side                      none
% 3.95/1.02  --res_ordering                          kbo
% 3.95/1.02  --res_to_prop_solver                    active
% 3.95/1.02  --res_prop_simpl_new                    false
% 3.95/1.02  --res_prop_simpl_given                  true
% 3.95/1.02  --res_passive_queue_type                priority_queues
% 3.95/1.02  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.95/1.02  --res_passive_queues_freq               [15;5]
% 3.95/1.02  --res_forward_subs                      full
% 3.95/1.02  --res_backward_subs                     full
% 3.95/1.02  --res_forward_subs_resolution           true
% 3.95/1.02  --res_backward_subs_resolution          true
% 3.95/1.02  --res_orphan_elimination                true
% 3.95/1.02  --res_time_limit                        2.
% 3.95/1.02  --res_out_proof                         true
% 3.95/1.02  
% 3.95/1.02  ------ Superposition Options
% 3.95/1.02  
% 3.95/1.02  --superposition_flag                    true
% 3.95/1.02  --sup_passive_queue_type                priority_queues
% 3.95/1.02  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.95/1.02  --sup_passive_queues_freq               [8;1;4]
% 3.95/1.02  --demod_completeness_check              fast
% 3.95/1.02  --demod_use_ground                      true
% 3.95/1.02  --sup_to_prop_solver                    passive
% 3.95/1.02  --sup_prop_simpl_new                    true
% 3.95/1.02  --sup_prop_simpl_given                  true
% 3.95/1.02  --sup_fun_splitting                     false
% 3.95/1.02  --sup_smt_interval                      50000
% 3.95/1.02  
% 3.95/1.02  ------ Superposition Simplification Setup
% 3.95/1.02  
% 3.95/1.02  --sup_indices_passive                   []
% 3.95/1.02  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.02  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.02  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.95/1.02  --sup_full_triv                         [TrivRules;PropSubs]
% 3.95/1.02  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/1.02  --sup_full_bw                           [BwDemod]
% 3.95/1.02  --sup_immed_triv                        [TrivRules]
% 3.95/1.02  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.95/1.02  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/1.02  --sup_immed_bw_main                     []
% 3.95/1.02  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.95/1.02  --sup_input_triv                        [Unflattening;TrivRules]
% 3.95/1.02  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.95/1.02  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.95/1.02  
% 3.95/1.02  ------ Combination Options
% 3.95/1.02  
% 3.95/1.02  --comb_res_mult                         3
% 3.95/1.02  --comb_sup_mult                         2
% 3.95/1.02  --comb_inst_mult                        10
% 3.95/1.02  
% 3.95/1.02  ------ Debug Options
% 3.95/1.02  
% 3.95/1.02  --dbg_backtrace                         false
% 3.95/1.02  --dbg_dump_prop_clauses                 false
% 3.95/1.02  --dbg_dump_prop_clauses_file            -
% 3.95/1.02  --dbg_out_stat                          false
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  ------ Proving...
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  % SZS status Theorem for theBenchmark.p
% 3.95/1.02  
% 3.95/1.02  % SZS output start CNFRefutation for theBenchmark.p
% 3.95/1.02  
% 3.95/1.02  fof(f15,axiom,(
% 3.95/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f30,plain,(
% 3.95/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/1.02    inference(ennf_transformation,[],[f15])).
% 3.95/1.02  
% 3.95/1.02  fof(f31,plain,(
% 3.95/1.02    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/1.02    inference(flattening,[],[f30])).
% 3.95/1.02  
% 3.95/1.02  fof(f48,plain,(
% 3.95/1.02    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/1.02    inference(nnf_transformation,[],[f31])).
% 3.95/1.02  
% 3.95/1.02  fof(f78,plain,(
% 3.95/1.02    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.95/1.02    inference(cnf_transformation,[],[f48])).
% 3.95/1.02  
% 3.95/1.02  fof(f16,conjecture,(
% 3.95/1.02    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f17,negated_conjecture,(
% 3.95/1.02    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.95/1.02    inference(negated_conjecture,[],[f16])).
% 3.95/1.02  
% 3.95/1.02  fof(f32,plain,(
% 3.95/1.02    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.95/1.02    inference(ennf_transformation,[],[f17])).
% 3.95/1.02  
% 3.95/1.02  fof(f33,plain,(
% 3.95/1.02    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.95/1.02    inference(flattening,[],[f32])).
% 3.95/1.02  
% 3.95/1.02  fof(f50,plain,(
% 3.95/1.02    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK7 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.95/1.02    introduced(choice_axiom,[])).
% 3.95/1.02  
% 3.95/1.02  fof(f49,plain,(
% 3.95/1.02    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK6,X5) != X4 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 3.95/1.02    introduced(choice_axiom,[])).
% 3.95/1.02  
% 3.95/1.02  fof(f51,plain,(
% 3.95/1.02    (! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 3.95/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f33,f50,f49])).
% 3.95/1.02  
% 3.95/1.02  fof(f85,plain,(
% 3.95/1.02    v1_funct_2(sK6,sK3,sK4)),
% 3.95/1.02    inference(cnf_transformation,[],[f51])).
% 3.95/1.02  
% 3.95/1.02  fof(f86,plain,(
% 3.95/1.02    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.95/1.02    inference(cnf_transformation,[],[f51])).
% 3.95/1.02  
% 3.95/1.02  fof(f13,axiom,(
% 3.95/1.02    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f28,plain,(
% 3.95/1.02    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/1.02    inference(ennf_transformation,[],[f13])).
% 3.95/1.02  
% 3.95/1.02  fof(f76,plain,(
% 3.95/1.02    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.95/1.02    inference(cnf_transformation,[],[f28])).
% 3.95/1.02  
% 3.95/1.02  fof(f9,axiom,(
% 3.95/1.02    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f22,plain,(
% 3.95/1.02    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.95/1.02    inference(ennf_transformation,[],[f9])).
% 3.95/1.02  
% 3.95/1.02  fof(f40,plain,(
% 3.95/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.95/1.02    inference(nnf_transformation,[],[f22])).
% 3.95/1.02  
% 3.95/1.02  fof(f41,plain,(
% 3.95/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.95/1.02    inference(rectify,[],[f40])).
% 3.95/1.02  
% 3.95/1.02  fof(f42,plain,(
% 3.95/1.02    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.95/1.02    introduced(choice_axiom,[])).
% 3.95/1.02  
% 3.95/1.02  fof(f43,plain,(
% 3.95/1.02    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.95/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f41,f42])).
% 3.95/1.02  
% 3.95/1.02  fof(f63,plain,(
% 3.95/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f43])).
% 3.95/1.02  
% 3.95/1.02  fof(f7,axiom,(
% 3.95/1.02    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f21,plain,(
% 3.95/1.02    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.95/1.02    inference(ennf_transformation,[],[f7])).
% 3.95/1.02  
% 3.95/1.02  fof(f61,plain,(
% 3.95/1.02    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f21])).
% 3.95/1.02  
% 3.95/1.02  fof(f8,axiom,(
% 3.95/1.02    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f62,plain,(
% 3.95/1.02    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.95/1.02    inference(cnf_transformation,[],[f8])).
% 3.95/1.02  
% 3.95/1.02  fof(f5,axiom,(
% 3.95/1.02    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f19,plain,(
% 3.95/1.02    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.95/1.02    inference(ennf_transformation,[],[f5])).
% 3.95/1.02  
% 3.95/1.02  fof(f59,plain,(
% 3.95/1.02    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f19])).
% 3.95/1.02  
% 3.95/1.02  fof(f14,axiom,(
% 3.95/1.02    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f29,plain,(
% 3.95/1.02    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.95/1.02    inference(ennf_transformation,[],[f14])).
% 3.95/1.02  
% 3.95/1.02  fof(f77,plain,(
% 3.95/1.02    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.95/1.02    inference(cnf_transformation,[],[f29])).
% 3.95/1.02  
% 3.95/1.02  fof(f87,plain,(
% 3.95/1.02    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))),
% 3.95/1.02    inference(cnf_transformation,[],[f51])).
% 3.95/1.02  
% 3.95/1.02  fof(f64,plain,(
% 3.95/1.02    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f43])).
% 3.95/1.02  
% 3.95/1.02  fof(f12,axiom,(
% 3.95/1.02    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f26,plain,(
% 3.95/1.02    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.95/1.02    inference(ennf_transformation,[],[f12])).
% 3.95/1.02  
% 3.95/1.02  fof(f27,plain,(
% 3.95/1.02    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.95/1.02    inference(flattening,[],[f26])).
% 3.95/1.02  
% 3.95/1.02  fof(f46,plain,(
% 3.95/1.02    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.95/1.02    inference(nnf_transformation,[],[f27])).
% 3.95/1.02  
% 3.95/1.02  fof(f47,plain,(
% 3.95/1.02    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.95/1.02    inference(flattening,[],[f46])).
% 3.95/1.02  
% 3.95/1.02  fof(f74,plain,(
% 3.95/1.02    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f47])).
% 3.95/1.02  
% 3.95/1.02  fof(f84,plain,(
% 3.95/1.02    v1_funct_1(sK6)),
% 3.95/1.02    inference(cnf_transformation,[],[f51])).
% 3.95/1.02  
% 3.95/1.02  fof(f88,plain,(
% 3.95/1.02    ( ! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~m1_subset_1(X5,sK3)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f51])).
% 3.95/1.02  
% 3.95/1.02  fof(f65,plain,(
% 3.95/1.02    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f43])).
% 3.95/1.02  
% 3.95/1.02  fof(f1,axiom,(
% 3.95/1.02    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f34,plain,(
% 3.95/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.95/1.02    inference(nnf_transformation,[],[f1])).
% 3.95/1.02  
% 3.95/1.02  fof(f35,plain,(
% 3.95/1.02    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.95/1.02    inference(rectify,[],[f34])).
% 3.95/1.02  
% 3.95/1.02  fof(f36,plain,(
% 3.95/1.02    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.95/1.02    introduced(choice_axiom,[])).
% 3.95/1.02  
% 3.95/1.02  fof(f37,plain,(
% 3.95/1.02    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.95/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f35,f36])).
% 3.95/1.02  
% 3.95/1.02  fof(f53,plain,(
% 3.95/1.02    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f37])).
% 3.95/1.02  
% 3.95/1.02  fof(f4,axiom,(
% 3.95/1.02    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f18,plain,(
% 3.95/1.02    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.95/1.02    inference(ennf_transformation,[],[f4])).
% 3.95/1.02  
% 3.95/1.02  fof(f58,plain,(
% 3.95/1.02    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.95/1.02    inference(cnf_transformation,[],[f18])).
% 3.95/1.02  
% 3.95/1.02  fof(f11,axiom,(
% 3.95/1.02    ! [X0] : ? [X1] : (! [X2] : (r2_hidden(X2,X0) => k1_xboole_0 = k1_funct_1(X1,X2)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f25,plain,(
% 3.95/1.02    ! [X0] : ? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1))),
% 3.95/1.02    inference(ennf_transformation,[],[f11])).
% 3.95/1.02  
% 3.95/1.02  fof(f44,plain,(
% 3.95/1.02    ! [X0] : (? [X1] : (! [X2] : (k1_xboole_0 = k1_funct_1(X1,X2) | ~r2_hidden(X2,X0)) & k1_relat_1(X1) = X0 & v1_funct_1(X1) & v1_relat_1(X1)) => (! [X2] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0))))),
% 3.95/1.02    introduced(choice_axiom,[])).
% 3.95/1.02  
% 3.95/1.02  fof(f45,plain,(
% 3.95/1.02    ! [X0] : (! [X2] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) & k1_relat_1(sK2(X0)) = X0 & v1_funct_1(sK2(X0)) & v1_relat_1(sK2(X0)))),
% 3.95/1.02    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f25,f44])).
% 3.95/1.02  
% 3.95/1.02  fof(f72,plain,(
% 3.95/1.02    ( ! [X2,X0] : (k1_xboole_0 = k1_funct_1(sK2(X0),X2) | ~r2_hidden(X2,X0)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f45])).
% 3.95/1.02  
% 3.95/1.02  fof(f75,plain,(
% 3.95/1.02    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f47])).
% 3.95/1.02  
% 3.95/1.02  fof(f91,plain,(
% 3.95/1.02    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.95/1.02    inference(equality_resolution,[],[f75])).
% 3.95/1.02  
% 3.95/1.02  fof(f52,plain,(
% 3.95/1.02    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f37])).
% 3.95/1.02  
% 3.95/1.02  fof(f6,axiom,(
% 3.95/1.02    ! [X0] : (v1_xboole_0(X0) => v1_relat_1(X0))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f20,plain,(
% 3.95/1.02    ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0))),
% 3.95/1.02    inference(ennf_transformation,[],[f6])).
% 3.95/1.02  
% 3.95/1.02  fof(f60,plain,(
% 3.95/1.02    ( ! [X0] : (v1_relat_1(X0) | ~v1_xboole_0(X0)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f20])).
% 3.95/1.02  
% 3.95/1.02  fof(f3,axiom,(
% 3.95/1.02    ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f38,plain,(
% 3.95/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.95/1.02    inference(nnf_transformation,[],[f3])).
% 3.95/1.02  
% 3.95/1.02  fof(f39,plain,(
% 3.95/1.02    ! [X0,X1] : ((k1_xboole_0 = k2_zfmisc_1(X0,X1) | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k1_xboole_0 != k2_zfmisc_1(X0,X1)))),
% 3.95/1.02    inference(flattening,[],[f38])).
% 3.95/1.02  
% 3.95/1.02  fof(f57,plain,(
% 3.95/1.02    ( ! [X0,X1] : (k1_xboole_0 = k2_zfmisc_1(X0,X1) | k1_xboole_0 != X1) )),
% 3.95/1.02    inference(cnf_transformation,[],[f39])).
% 3.95/1.02  
% 3.95/1.02  fof(f89,plain,(
% 3.95/1.02    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(X0,k1_xboole_0)) )),
% 3.95/1.02    inference(equality_resolution,[],[f57])).
% 3.95/1.02  
% 3.95/1.02  fof(f70,plain,(
% 3.95/1.02    ( ! [X0] : (v1_funct_1(sK2(X0))) )),
% 3.95/1.02    inference(cnf_transformation,[],[f45])).
% 3.95/1.02  
% 3.95/1.02  fof(f69,plain,(
% 3.95/1.02    ( ! [X0] : (v1_relat_1(sK2(X0))) )),
% 3.95/1.02    inference(cnf_transformation,[],[f45])).
% 3.95/1.02  
% 3.95/1.02  fof(f71,plain,(
% 3.95/1.02    ( ! [X0] : (k1_relat_1(sK2(X0)) = X0) )),
% 3.95/1.02    inference(cnf_transformation,[],[f45])).
% 3.95/1.02  
% 3.95/1.02  fof(f66,plain,(
% 3.95/1.02    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 3.95/1.02    inference(cnf_transformation,[],[f43])).
% 3.95/1.02  
% 3.95/1.02  fof(f2,axiom,(
% 3.95/1.02    v1_xboole_0(k1_xboole_0)),
% 3.95/1.02    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.95/1.02  
% 3.95/1.02  fof(f54,plain,(
% 3.95/1.02    v1_xboole_0(k1_xboole_0)),
% 3.95/1.02    inference(cnf_transformation,[],[f2])).
% 3.95/1.02  
% 3.95/1.02  cnf(c_31,plain,
% 3.95/1.02      ( ~ v1_funct_2(X0,X1,X2)
% 3.95/1.02      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.95/1.02      | k1_xboole_0 = X2 ),
% 3.95/1.02      inference(cnf_transformation,[],[f78]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_35,negated_conjecture,
% 3.95/1.02      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.95/1.02      inference(cnf_transformation,[],[f85]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_584,plain,
% 3.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/1.02      | k1_relset_1(X1,X2,X0) = X1
% 3.95/1.02      | sK4 != X2
% 3.95/1.02      | sK3 != X1
% 3.95/1.02      | sK6 != X0
% 3.95/1.02      | k1_xboole_0 = X2 ),
% 3.95/1.02      inference(resolution_lifted,[status(thm)],[c_31,c_35]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_585,plain,
% 3.95/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.95/1.02      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.95/1.02      | k1_xboole_0 = sK4 ),
% 3.95/1.02      inference(unflattening,[status(thm)],[c_584]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_34,negated_conjecture,
% 3.95/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.95/1.02      inference(cnf_transformation,[],[f86]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_587,plain,
% 3.95/1.02      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 3.95/1.02      inference(global_propositional_subsumption,
% 3.95/1.02                [status(thm)],
% 3.95/1.02                [c_585,c_34]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1796,plain,
% 3.95/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_24,plain,
% 3.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/1.02      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.95/1.02      inference(cnf_transformation,[],[f76]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1800,plain,
% 3.95/1.02      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.95/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_3149,plain,
% 3.95/1.02      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_1796,c_1800]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_3389,plain,
% 3.95/1.02      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_587,c_3149]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_14,plain,
% 3.95/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.95/1.02      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 3.95/1.02      | ~ v1_relat_1(X1) ),
% 3.95/1.02      inference(cnf_transformation,[],[f63]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1805,plain,
% 3.95/1.02      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.95/1.02      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.95/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_3771,plain,
% 3.95/1.02      ( sK4 = k1_xboole_0
% 3.95/1.02      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.95/1.02      | r2_hidden(sK1(X0,X1,sK6),sK3) = iProver_top
% 3.95/1.02      | v1_relat_1(sK6) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_3389,c_1805]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_39,plain,
% 3.95/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_9,plain,
% 3.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.95/1.02      | ~ v1_relat_1(X1)
% 3.95/1.02      | v1_relat_1(X0) ),
% 3.95/1.02      inference(cnf_transformation,[],[f61]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_2057,plain,
% 3.95/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 3.95/1.02      | ~ v1_relat_1(X0)
% 3.95/1.02      | v1_relat_1(sK6) ),
% 3.95/1.02      inference(instantiation,[status(thm)],[c_9]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_2194,plain,
% 3.95/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.95/1.02      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 3.95/1.02      | v1_relat_1(sK6) ),
% 3.95/1.02      inference(instantiation,[status(thm)],[c_2057]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_2195,plain,
% 3.95/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.95/1.02      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.95/1.02      | v1_relat_1(sK6) = iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_2194]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_10,plain,
% 3.95/1.02      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.95/1.02      inference(cnf_transformation,[],[f62]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4026,plain,
% 3.95/1.02      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 3.95/1.02      inference(instantiation,[status(thm)],[c_10]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4027,plain,
% 3.95/1.02      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_4026]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4072,plain,
% 3.95/1.02      ( r2_hidden(sK1(X0,X1,sK6),sK3) = iProver_top
% 3.95/1.02      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.95/1.02      | sK4 = k1_xboole_0 ),
% 3.95/1.02      inference(global_propositional_subsumption,
% 3.95/1.02                [status(thm)],
% 3.95/1.02                [c_3771,c_39,c_2195,c_4027]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4073,plain,
% 3.95/1.02      ( sK4 = k1_xboole_0
% 3.95/1.02      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.95/1.02      | r2_hidden(sK1(X0,X1,sK6),sK3) = iProver_top ),
% 3.95/1.02      inference(renaming,[status(thm)],[c_4072]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_7,plain,
% 3.95/1.02      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.95/1.02      inference(cnf_transformation,[],[f59]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1812,plain,
% 3.95/1.02      ( m1_subset_1(X0,X1) = iProver_top
% 3.95/1.02      | r2_hidden(X0,X1) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4083,plain,
% 3.95/1.02      ( sK4 = k1_xboole_0
% 3.95/1.02      | m1_subset_1(sK1(X0,X1,sK6),sK3) = iProver_top
% 3.95/1.02      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_4073,c_1812]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_25,plain,
% 3.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.95/1.02      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.95/1.02      inference(cnf_transformation,[],[f77]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1799,plain,
% 3.95/1.02      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.95/1.02      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_2525,plain,
% 3.95/1.02      ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_1796,c_1799]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_33,negated_conjecture,
% 3.95/1.02      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 3.95/1.02      inference(cnf_transformation,[],[f87]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1797,plain,
% 3.95/1.02      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_2816,plain,
% 3.95/1.02      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 3.95/1.02      inference(demodulation,[status(thm)],[c_2525,c_1797]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_13,plain,
% 3.95/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.95/1.02      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.95/1.02      | ~ v1_relat_1(X1) ),
% 3.95/1.02      inference(cnf_transformation,[],[f64]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1806,plain,
% 3.95/1.02      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.95/1.02      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.95/1.02      | v1_relat_1(X1) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_22,plain,
% 3.95/1.02      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.95/1.02      | ~ v1_funct_1(X2)
% 3.95/1.02      | ~ v1_relat_1(X2)
% 3.95/1.02      | k1_funct_1(X2,X0) = X1 ),
% 3.95/1.02      inference(cnf_transformation,[],[f74]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_36,negated_conjecture,
% 3.95/1.02      ( v1_funct_1(sK6) ),
% 3.95/1.02      inference(cnf_transformation,[],[f84]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_503,plain,
% 3.95/1.02      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.95/1.02      | ~ v1_relat_1(X2)
% 3.95/1.02      | k1_funct_1(X2,X0) = X1
% 3.95/1.02      | sK6 != X2 ),
% 3.95/1.02      inference(resolution_lifted,[status(thm)],[c_22,c_36]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_504,plain,
% 3.95/1.02      ( ~ r2_hidden(k4_tarski(X0,X1),sK6)
% 3.95/1.02      | ~ v1_relat_1(sK6)
% 3.95/1.02      | k1_funct_1(sK6,X0) = X1 ),
% 3.95/1.02      inference(unflattening,[status(thm)],[c_503]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1790,plain,
% 3.95/1.02      ( k1_funct_1(sK6,X0) = X1
% 3.95/1.02      | r2_hidden(k4_tarski(X0,X1),sK6) != iProver_top
% 3.95/1.02      | v1_relat_1(sK6) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_504]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4328,plain,
% 3.95/1.02      ( k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0
% 3.95/1.02      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.95/1.02      | v1_relat_1(sK6) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_1806,c_1790]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_5125,plain,
% 3.95/1.02      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.95/1.02      | k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0 ),
% 3.95/1.02      inference(global_propositional_subsumption,
% 3.95/1.02                [status(thm)],
% 3.95/1.02                [c_4328,c_39,c_2195,c_4027]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_5126,plain,
% 3.95/1.02      ( k1_funct_1(sK6,sK1(X0,X1,sK6)) = X0
% 3.95/1.02      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.95/1.02      inference(renaming,[status(thm)],[c_5125]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_5136,plain,
% 3.95/1.02      ( k1_funct_1(sK6,sK1(sK7,sK5,sK6)) = sK7 ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_2816,c_5126]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_32,negated_conjecture,
% 3.95/1.02      ( ~ m1_subset_1(X0,sK3)
% 3.95/1.02      | ~ r2_hidden(X0,sK5)
% 3.95/1.02      | k1_funct_1(sK6,X0) != sK7 ),
% 3.95/1.02      inference(cnf_transformation,[],[f88]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1798,plain,
% 3.95/1.02      ( k1_funct_1(sK6,X0) != sK7
% 3.95/1.02      | m1_subset_1(X0,sK3) != iProver_top
% 3.95/1.02      | r2_hidden(X0,sK5) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_5168,plain,
% 3.95/1.02      ( m1_subset_1(sK1(sK7,sK5,sK6),sK3) != iProver_top
% 3.95/1.02      | r2_hidden(sK1(sK7,sK5,sK6),sK5) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_5136,c_1798]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_14268,plain,
% 3.95/1.02      ( sK4 = k1_xboole_0
% 3.95/1.02      | r2_hidden(sK1(sK7,sK5,sK6),sK5) != iProver_top
% 3.95/1.02      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_4083,c_5168]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_12,plain,
% 3.95/1.02      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.95/1.02      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.95/1.02      | ~ v1_relat_1(X1) ),
% 3.95/1.02      inference(cnf_transformation,[],[f65]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_13572,plain,
% 3.95/1.02      ( r2_hidden(sK1(sK7,sK5,sK6),sK5)
% 3.95/1.02      | ~ r2_hidden(sK7,k9_relat_1(sK6,sK5))
% 3.95/1.02      | ~ v1_relat_1(sK6) ),
% 3.95/1.02      inference(instantiation,[status(thm)],[c_12]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_13573,plain,
% 3.95/1.02      ( r2_hidden(sK1(sK7,sK5,sK6),sK5) = iProver_top
% 3.95/1.02      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top
% 3.95/1.02      | v1_relat_1(sK6) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_13572]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_14530,plain,
% 3.95/1.02      ( sK4 = k1_xboole_0 ),
% 3.95/1.02      inference(global_propositional_subsumption,
% 3.95/1.02                [status(thm)],
% 3.95/1.02                [c_14268,c_39,c_2195,c_2816,c_4027,c_13573]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_0,plain,
% 3.95/1.02      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.95/1.02      inference(cnf_transformation,[],[f53]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1816,plain,
% 3.95/1.02      ( r2_hidden(sK0(X0),X0) = iProver_top
% 3.95/1.02      | v1_xboole_0(X0) = iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_6,plain,
% 3.95/1.02      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.95/1.02      | ~ r2_hidden(X2,X0)
% 3.95/1.02      | r2_hidden(X2,X1) ),
% 3.95/1.02      inference(cnf_transformation,[],[f58]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1813,plain,
% 3.95/1.02      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.95/1.02      | r2_hidden(X2,X0) != iProver_top
% 3.95/1.02      | r2_hidden(X2,X1) = iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4539,plain,
% 3.95/1.02      ( r2_hidden(X0,k2_zfmisc_1(sK3,sK4)) = iProver_top
% 3.95/1.02      | r2_hidden(X0,sK6) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_1796,c_1813]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_17,plain,
% 3.95/1.02      ( ~ r2_hidden(X0,X1) | k1_funct_1(sK2(X1),X0) = k1_xboole_0 ),
% 3.95/1.02      inference(cnf_transformation,[],[f72]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1802,plain,
% 3.95/1.02      ( k1_funct_1(sK2(X0),X1) = k1_xboole_0
% 3.95/1.02      | r2_hidden(X1,X0) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4803,plain,
% 3.95/1.02      ( k1_funct_1(sK2(k2_zfmisc_1(sK3,sK4)),X0) = k1_xboole_0
% 3.95/1.02      | r2_hidden(X0,sK6) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_4539,c_1802]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4992,plain,
% 3.95/1.02      ( k1_funct_1(sK2(k2_zfmisc_1(sK3,sK4)),sK0(sK6)) = k1_xboole_0
% 3.95/1.02      | v1_xboole_0(sK6) = iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_1816,c_4803]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_21,plain,
% 3.95/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.95/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.95/1.02      | ~ v1_funct_1(X1)
% 3.95/1.02      | ~ v1_relat_1(X1) ),
% 3.95/1.02      inference(cnf_transformation,[],[f91]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_488,plain,
% 3.95/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.95/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.95/1.02      | ~ v1_relat_1(X1)
% 3.95/1.02      | sK6 != X1 ),
% 3.95/1.02      inference(resolution_lifted,[status(thm)],[c_21,c_36]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_489,plain,
% 3.95/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 3.95/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6)
% 3.95/1.02      | ~ v1_relat_1(sK6) ),
% 3.95/1.02      inference(unflattening,[status(thm)],[c_488]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1791,plain,
% 3.95/1.02      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.95/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK6,X0)),sK6) = iProver_top
% 3.95/1.02      | v1_relat_1(sK6) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_489]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1,plain,
% 3.95/1.02      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.95/1.02      inference(cnf_transformation,[],[f52]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1815,plain,
% 3.95/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.95/1.02      | v1_xboole_0(X1) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_2631,plain,
% 3.95/1.02      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.95/1.02      | v1_relat_1(sK6) != iProver_top
% 3.95/1.02      | v1_xboole_0(sK6) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_1791,c_1815]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_8,plain,
% 3.95/1.02      ( v1_relat_1(X0) | ~ v1_xboole_0(X0) ),
% 3.95/1.02      inference(cnf_transformation,[],[f60]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_2118,plain,
% 3.95/1.02      ( v1_relat_1(sK6) | ~ v1_xboole_0(sK6) ),
% 3.95/1.02      inference(instantiation,[status(thm)],[c_8]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_2119,plain,
% 3.95/1.02      ( v1_relat_1(sK6) = iProver_top | v1_xboole_0(sK6) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_2118]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_3136,plain,
% 3.95/1.02      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 3.95/1.02      | v1_xboole_0(sK6) != iProver_top ),
% 3.95/1.02      inference(global_propositional_subsumption,
% 3.95/1.02                [status(thm)],
% 3.95/1.02                [c_2631,c_2119]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_3394,plain,
% 3.95/1.02      ( sK4 = k1_xboole_0
% 3.95/1.02      | r2_hidden(X0,sK3) != iProver_top
% 3.95/1.02      | v1_xboole_0(sK6) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_3389,c_3136]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4085,plain,
% 3.95/1.02      ( sK4 = k1_xboole_0
% 3.95/1.02      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.95/1.02      | v1_xboole_0(sK6) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_4073,c_3394]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_3776,plain,
% 3.95/1.02      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.95/1.02      | v1_relat_1(sK6) != iProver_top
% 3.95/1.02      | v1_xboole_0(sK6) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_1805,c_3136]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4227,plain,
% 3.95/1.02      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.95/1.02      | v1_xboole_0(sK6) != iProver_top ),
% 3.95/1.02      inference(global_propositional_subsumption,
% 3.95/1.02                [status(thm)],
% 3.95/1.02                [c_4085,c_39,c_2195,c_3776,c_4027]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4236,plain,
% 3.95/1.02      ( v1_xboole_0(sK6) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_2816,c_4227]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_7411,plain,
% 3.95/1.02      ( k1_funct_1(sK2(k2_zfmisc_1(sK3,sK4)),sK0(sK6)) = k1_xboole_0 ),
% 3.95/1.02      inference(global_propositional_subsumption,
% 3.95/1.02                [status(thm)],
% 3.95/1.02                [c_4992,c_4236]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_14557,plain,
% 3.95/1.02      ( k1_funct_1(sK2(k2_zfmisc_1(sK3,k1_xboole_0)),sK0(sK6)) = k1_xboole_0 ),
% 3.95/1.02      inference(demodulation,[status(thm)],[c_14530,c_7411]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_3,plain,
% 3.95/1.02      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.95/1.02      inference(cnf_transformation,[],[f89]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_14637,plain,
% 3.95/1.02      ( k1_funct_1(sK2(k1_xboole_0),sK0(sK6)) = k1_xboole_0 ),
% 3.95/1.02      inference(demodulation,[status(thm)],[c_14557,c_3]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_19,plain,
% 3.95/1.02      ( v1_funct_1(sK2(X0)) ),
% 3.95/1.02      inference(cnf_transformation,[],[f70]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_439,plain,
% 3.95/1.02      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.95/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.95/1.02      | ~ v1_relat_1(X1)
% 3.95/1.02      | sK2(X2) != X1 ),
% 3.95/1.02      inference(resolution_lifted,[status(thm)],[c_19,c_21]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_440,plain,
% 3.95/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK2(X1)))
% 3.95/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK2(X1),X0)),sK2(X1))
% 3.95/1.02      | ~ v1_relat_1(sK2(X1)) ),
% 3.95/1.02      inference(unflattening,[status(thm)],[c_439]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_20,plain,
% 3.95/1.02      ( v1_relat_1(sK2(X0)) ),
% 3.95/1.02      inference(cnf_transformation,[],[f69]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_450,plain,
% 3.95/1.02      ( ~ r2_hidden(X0,k1_relat_1(sK2(X1)))
% 3.95/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK2(X1),X0)),sK2(X1)) ),
% 3.95/1.02      inference(forward_subsumption_resolution,
% 3.95/1.02                [status(thm)],
% 3.95/1.02                [c_440,c_20]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1794,plain,
% 3.95/1.02      ( r2_hidden(X0,k1_relat_1(sK2(X1))) != iProver_top
% 3.95/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK2(X1),X0)),sK2(X1)) = iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_450]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_18,plain,
% 3.95/1.02      ( k1_relat_1(sK2(X0)) = X0 ),
% 3.95/1.02      inference(cnf_transformation,[],[f71]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1904,plain,
% 3.95/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.95/1.02      | r2_hidden(k4_tarski(X0,k1_funct_1(sK2(X1),X0)),sK2(X1)) = iProver_top ),
% 3.95/1.02      inference(demodulation,[status(thm)],[c_1794,c_18]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_11,plain,
% 3.95/1.02      ( ~ r2_hidden(X0,X1)
% 3.95/1.02      | r2_hidden(X2,k9_relat_1(X3,X1))
% 3.95/1.02      | ~ r2_hidden(X0,k1_relat_1(X3))
% 3.95/1.02      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 3.95/1.02      | ~ v1_relat_1(X3) ),
% 3.95/1.02      inference(cnf_transformation,[],[f66]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1808,plain,
% 3.95/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.95/1.02      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 3.95/1.02      | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
% 3.95/1.02      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 3.95/1.02      | v1_relat_1(X3) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_5213,plain,
% 3.95/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.95/1.02      | r2_hidden(X0,X2) != iProver_top
% 3.95/1.02      | r2_hidden(X0,k1_relat_1(sK2(X1))) != iProver_top
% 3.95/1.02      | r2_hidden(k1_funct_1(sK2(X1),X0),k9_relat_1(sK2(X1),X2)) = iProver_top
% 3.95/1.02      | v1_relat_1(sK2(X1)) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_1904,c_1808]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_5239,plain,
% 3.95/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.95/1.02      | r2_hidden(X0,X2) != iProver_top
% 3.95/1.02      | r2_hidden(k1_funct_1(sK2(X1),X0),k9_relat_1(sK2(X1),X2)) = iProver_top
% 3.95/1.02      | v1_relat_1(sK2(X1)) != iProver_top ),
% 3.95/1.02      inference(demodulation,[status(thm)],[c_5213,c_18]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_1801,plain,
% 3.95/1.02      ( v1_relat_1(sK2(X0)) = iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_5418,plain,
% 3.95/1.02      ( r2_hidden(X0,X1) != iProver_top
% 3.95/1.02      | r2_hidden(X0,X2) != iProver_top
% 3.95/1.02      | r2_hidden(k1_funct_1(sK2(X1),X0),k9_relat_1(sK2(X1),X2)) = iProver_top ),
% 3.95/1.02      inference(forward_subsumption_resolution,
% 3.95/1.02                [status(thm)],
% 3.95/1.02                [c_5239,c_1801]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_15075,plain,
% 3.95/1.02      ( r2_hidden(sK0(sK6),X0) != iProver_top
% 3.95/1.02      | r2_hidden(sK0(sK6),k1_xboole_0) != iProver_top
% 3.95/1.02      | r2_hidden(k1_xboole_0,k9_relat_1(sK2(k1_xboole_0),X0)) = iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_14637,c_5418]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_15093,plain,
% 3.95/1.02      ( r2_hidden(sK0(sK6),k1_xboole_0) != iProver_top
% 3.95/1.02      | r2_hidden(k1_xboole_0,k9_relat_1(sK2(k1_xboole_0),k1_xboole_0)) = iProver_top ),
% 3.95/1.02      inference(instantiation,[status(thm)],[c_15075]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_14573,plain,
% 3.95/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.95/1.02      inference(demodulation,[status(thm)],[c_14530,c_1796]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_14575,plain,
% 3.95/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) = iProver_top ),
% 3.95/1.02      inference(demodulation,[status(thm)],[c_14573,c_3]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_3770,plain,
% 3.95/1.02      ( r2_hidden(X0,k9_relat_1(sK2(X1),X2)) != iProver_top
% 3.95/1.02      | r2_hidden(sK1(X0,X2,sK2(X1)),X1) = iProver_top
% 3.95/1.02      | v1_relat_1(sK2(X1)) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_18,c_1805]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_5337,plain,
% 3.95/1.02      ( r2_hidden(X0,k9_relat_1(sK2(X1),X2)) != iProver_top
% 3.95/1.02      | r2_hidden(sK1(X0,X2,sK2(X1)),X1) = iProver_top ),
% 3.95/1.02      inference(forward_subsumption_resolution,
% 3.95/1.02                [status(thm)],
% 3.95/1.02                [c_3770,c_1801]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_5342,plain,
% 3.95/1.02      ( r2_hidden(X0,k9_relat_1(sK2(X1),X2)) != iProver_top
% 3.95/1.02      | v1_xboole_0(X1) != iProver_top ),
% 3.95/1.02      inference(superposition,[status(thm)],[c_5337,c_1815]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_5393,plain,
% 3.95/1.02      ( r2_hidden(k1_xboole_0,k9_relat_1(sK2(k1_xboole_0),k1_xboole_0)) != iProver_top
% 3.95/1.02      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.95/1.02      inference(instantiation,[status(thm)],[c_5342]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4050,plain,
% 3.95/1.02      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 3.95/1.02      | r2_hidden(sK0(sK6),X0)
% 3.95/1.02      | ~ r2_hidden(sK0(sK6),sK6) ),
% 3.95/1.02      inference(instantiation,[status(thm)],[c_6]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4051,plain,
% 3.95/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(X0)) != iProver_top
% 3.95/1.02      | r2_hidden(sK0(sK6),X0) = iProver_top
% 3.95/1.02      | r2_hidden(sK0(sK6),sK6) != iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_4050]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_4053,plain,
% 3.95/1.02      ( m1_subset_1(sK6,k1_zfmisc_1(k1_xboole_0)) != iProver_top
% 3.95/1.02      | r2_hidden(sK0(sK6),sK6) != iProver_top
% 3.95/1.02      | r2_hidden(sK0(sK6),k1_xboole_0) = iProver_top ),
% 3.95/1.02      inference(instantiation,[status(thm)],[c_4051]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_2186,plain,
% 3.95/1.02      ( r2_hidden(sK0(sK6),sK6) | v1_xboole_0(sK6) ),
% 3.95/1.02      inference(instantiation,[status(thm)],[c_0]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_2187,plain,
% 3.95/1.02      ( r2_hidden(sK0(sK6),sK6) = iProver_top
% 3.95/1.02      | v1_xboole_0(sK6) = iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_2186]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_2,plain,
% 3.95/1.02      ( v1_xboole_0(k1_xboole_0) ),
% 3.95/1.02      inference(cnf_transformation,[],[f54]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(c_118,plain,
% 3.95/1.02      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.95/1.02      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.95/1.02  
% 3.95/1.02  cnf(contradiction,plain,
% 3.95/1.02      ( $false ),
% 3.95/1.02      inference(minisat,
% 3.95/1.02                [status(thm)],
% 3.95/1.02                [c_15093,c_14575,c_5393,c_4236,c_4053,c_2187,c_118]) ).
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  % SZS output end CNFRefutation for theBenchmark.p
% 3.95/1.02  
% 3.95/1.02  ------                               Statistics
% 3.95/1.02  
% 3.95/1.02  ------ General
% 3.95/1.02  
% 3.95/1.02  abstr_ref_over_cycles:                  0
% 3.95/1.02  abstr_ref_under_cycles:                 0
% 3.95/1.02  gc_basic_clause_elim:                   0
% 3.95/1.02  forced_gc_time:                         0
% 3.95/1.02  parsing_time:                           0.01
% 3.95/1.02  unif_index_cands_time:                  0.
% 3.95/1.02  unif_index_add_time:                    0.
% 3.95/1.02  orderings_time:                         0.
% 3.95/1.02  out_proof_time:                         0.012
% 3.95/1.02  total_time:                             0.403
% 3.95/1.02  num_of_symbols:                         55
% 3.95/1.02  num_of_terms:                           11926
% 3.95/1.02  
% 3.95/1.02  ------ Preprocessing
% 3.95/1.02  
% 3.95/1.02  num_of_splits:                          0
% 3.95/1.02  num_of_split_atoms:                     0
% 3.95/1.02  num_of_reused_defs:                     0
% 3.95/1.02  num_eq_ax_congr_red:                    29
% 3.95/1.02  num_of_sem_filtered_clauses:            1
% 3.95/1.02  num_of_subtypes:                        0
% 3.95/1.02  monotx_restored_types:                  0
% 3.95/1.02  sat_num_of_epr_types:                   0
% 3.95/1.02  sat_num_of_non_cyclic_types:            0
% 3.95/1.02  sat_guarded_non_collapsed_types:        0
% 3.95/1.02  num_pure_diseq_elim:                    0
% 3.95/1.02  simp_replaced_by:                       0
% 3.95/1.02  res_preprocessed:                       166
% 3.95/1.02  prep_upred:                             0
% 3.95/1.02  prep_unflattend:                        77
% 3.95/1.02  smt_new_axioms:                         0
% 3.95/1.02  pred_elim_cands:                        4
% 3.95/1.02  pred_elim:                              2
% 3.95/1.02  pred_elim_cl:                           3
% 3.95/1.02  pred_elim_cycles:                       6
% 3.95/1.02  merged_defs:                            0
% 3.95/1.02  merged_defs_ncl:                        0
% 3.95/1.02  bin_hyper_res:                          0
% 3.95/1.02  prep_cycles:                            4
% 3.95/1.02  pred_elim_time:                         0.009
% 3.95/1.02  splitting_time:                         0.
% 3.95/1.02  sem_filter_time:                        0.
% 3.95/1.02  monotx_time:                            0.004
% 3.95/1.02  subtype_inf_time:                       0.
% 3.95/1.02  
% 3.95/1.02  ------ Problem properties
% 3.95/1.02  
% 3.95/1.02  clauses:                                34
% 3.95/1.02  conjectures:                            3
% 3.95/1.02  epr:                                    4
% 3.95/1.02  horn:                                   30
% 3.95/1.02  ground:                                 6
% 3.95/1.02  unary:                                  8
% 3.95/1.02  binary:                                 11
% 3.95/1.02  lits:                                   78
% 3.95/1.02  lits_eq:                                23
% 3.95/1.02  fd_pure:                                0
% 3.95/1.02  fd_pseudo:                              0
% 3.95/1.02  fd_cond:                                3
% 3.95/1.02  fd_pseudo_cond:                         2
% 3.95/1.02  ac_symbols:                             0
% 3.95/1.02  
% 3.95/1.02  ------ Propositional Solver
% 3.95/1.02  
% 3.95/1.02  prop_solver_calls:                      32
% 3.95/1.02  prop_fast_solver_calls:                 1456
% 3.95/1.02  smt_solver_calls:                       0
% 3.95/1.02  smt_fast_solver_calls:                  0
% 3.95/1.02  prop_num_of_clauses:                    5132
% 3.95/1.02  prop_preprocess_simplified:             11633
% 3.95/1.02  prop_fo_subsumed:                       58
% 3.95/1.02  prop_solver_time:                       0.
% 3.95/1.02  smt_solver_time:                        0.
% 3.95/1.02  smt_fast_solver_time:                   0.
% 3.95/1.02  prop_fast_solver_time:                  0.
% 3.95/1.02  prop_unsat_core_time:                   0.
% 3.95/1.02  
% 3.95/1.02  ------ QBF
% 3.95/1.02  
% 3.95/1.02  qbf_q_res:                              0
% 3.95/1.02  qbf_num_tautologies:                    0
% 3.95/1.02  qbf_prep_cycles:                        0
% 3.95/1.02  
% 3.95/1.02  ------ BMC1
% 3.95/1.02  
% 3.95/1.02  bmc1_current_bound:                     -1
% 3.95/1.02  bmc1_last_solved_bound:                 -1
% 3.95/1.02  bmc1_unsat_core_size:                   -1
% 3.95/1.02  bmc1_unsat_core_parents_size:           -1
% 3.95/1.02  bmc1_merge_next_fun:                    0
% 3.95/1.02  bmc1_unsat_core_clauses_time:           0.
% 3.95/1.02  
% 3.95/1.02  ------ Instantiation
% 3.95/1.02  
% 3.95/1.02  inst_num_of_clauses:                    1853
% 3.95/1.02  inst_num_in_passive:                    731
% 3.95/1.02  inst_num_in_active:                     857
% 3.95/1.02  inst_num_in_unprocessed:                266
% 3.95/1.02  inst_num_of_loops:                      930
% 3.95/1.02  inst_num_of_learning_restarts:          0
% 3.95/1.02  inst_num_moves_active_passive:          69
% 3.95/1.02  inst_lit_activity:                      0
% 3.95/1.02  inst_lit_activity_moves:                0
% 3.95/1.02  inst_num_tautologies:                   0
% 3.95/1.02  inst_num_prop_implied:                  0
% 3.95/1.02  inst_num_existing_simplified:           0
% 3.95/1.02  inst_num_eq_res_simplified:             0
% 3.95/1.02  inst_num_child_elim:                    0
% 3.95/1.02  inst_num_of_dismatching_blockings:      617
% 3.95/1.02  inst_num_of_non_proper_insts:           1432
% 3.95/1.02  inst_num_of_duplicates:                 0
% 3.95/1.02  inst_inst_num_from_inst_to_res:         0
% 3.95/1.02  inst_dismatching_checking_time:         0.
% 3.95/1.02  
% 3.95/1.02  ------ Resolution
% 3.95/1.02  
% 3.95/1.02  res_num_of_clauses:                     0
% 3.95/1.02  res_num_in_passive:                     0
% 3.95/1.02  res_num_in_active:                      0
% 3.95/1.02  res_num_of_loops:                       170
% 3.95/1.02  res_forward_subset_subsumed:            80
% 3.95/1.02  res_backward_subset_subsumed:           6
% 3.95/1.02  res_forward_subsumed:                   0
% 3.95/1.02  res_backward_subsumed:                  0
% 3.95/1.02  res_forward_subsumption_resolution:     3
% 3.95/1.02  res_backward_subsumption_resolution:    0
% 3.95/1.02  res_clause_to_clause_subsumption:       1507
% 3.95/1.02  res_orphan_elimination:                 0
% 3.95/1.02  res_tautology_del:                      152
% 3.95/1.02  res_num_eq_res_simplified:              0
% 3.95/1.02  res_num_sel_changes:                    0
% 3.95/1.02  res_moves_from_active_to_pass:          0
% 3.95/1.02  
% 3.95/1.02  ------ Superposition
% 3.95/1.02  
% 3.95/1.02  sup_time_total:                         0.
% 3.95/1.02  sup_time_generating:                    0.
% 3.95/1.02  sup_time_sim_full:                      0.
% 3.95/1.02  sup_time_sim_immed:                     0.
% 3.95/1.02  
% 3.95/1.02  sup_num_of_clauses:                     460
% 3.95/1.02  sup_num_in_active:                      124
% 3.95/1.02  sup_num_in_passive:                     336
% 3.95/1.02  sup_num_of_loops:                       184
% 3.95/1.02  sup_fw_superposition:                   362
% 3.95/1.02  sup_bw_superposition:                   238
% 3.95/1.02  sup_immediate_simplified:               121
% 3.95/1.02  sup_given_eliminated:                   3
% 3.95/1.02  comparisons_done:                       0
% 3.95/1.02  comparisons_avoided:                    3
% 3.95/1.02  
% 3.95/1.02  ------ Simplifications
% 3.95/1.02  
% 3.95/1.02  
% 3.95/1.02  sim_fw_subset_subsumed:                 33
% 3.95/1.02  sim_bw_subset_subsumed:                 56
% 3.95/1.02  sim_fw_subsumed:                        7
% 3.95/1.02  sim_bw_subsumed:                        5
% 3.95/1.02  sim_fw_subsumption_res:                 4
% 3.95/1.02  sim_bw_subsumption_res:                 0
% 3.95/1.02  sim_tautology_del:                      5
% 3.95/1.02  sim_eq_tautology_del:                   21
% 3.95/1.02  sim_eq_res_simp:                        1
% 3.95/1.02  sim_fw_demodulated:                     36
% 3.95/1.02  sim_bw_demodulated:                     44
% 3.95/1.02  sim_light_normalised:                   43
% 3.95/1.02  sim_joinable_taut:                      0
% 3.95/1.02  sim_joinable_simp:                      0
% 3.95/1.02  sim_ac_normalised:                      0
% 3.95/1.02  sim_smt_subsumption:                    0
% 3.95/1.02  
%------------------------------------------------------------------------------
