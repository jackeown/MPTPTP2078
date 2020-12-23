%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:08 EST 2020

% Result     : Theorem 3.63s
% Output     : CNFRefutation 3.63s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 787 expanded)
%              Number of clauses        :   91 ( 296 expanded)
%              Number of leaves         :   21 ( 168 expanded)
%              Depth                    :   25
%              Number of atoms          :  534 (3385 expanded)
%              Number of equality atoms :  181 ( 723 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   14 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f35,plain,(
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
    inference(flattening,[],[f35])).

fof(f51,plain,(
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
    inference(nnf_transformation,[],[f36])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f18,conjecture,(
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

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f53,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK6
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK6,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
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
              ( k1_funct_1(sK5,X5) != X4
              | ~ r2_hidden(X5,sK4)
              | ~ m1_subset_1(X5,sK2) )
          & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
      & v1_funct_2(sK5,sK2,sK3)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f54,plain,
    ( ! [X5] :
        ( k1_funct_1(sK5,X5) != sK6
        | ~ r2_hidden(X5,sK4)
        | ~ m1_subset_1(X5,sK2) )
    & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    & v1_funct_2(sK5,sK2,sK3)
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f38,f53,f52])).

fof(f87,plain,(
    v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f54])).

fof(f88,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f54])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f45,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f46,plain,(
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
    inference(rectify,[],[f45])).

fof(f47,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f60,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f3,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f61,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
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
    inference(ennf_transformation,[],[f7])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f62,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f66,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f9])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f14])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f79,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f89,plain,(
    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(cnf_transformation,[],[f54])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f49])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f86,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f54])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f91,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f75])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

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

fof(f39,plain,(
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

fof(f40,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f39])).

fof(f41,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).

fof(f55,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f90,plain,(
    ! [X5] :
      ( k1_funct_1(sK5,X5) != sK6
      | ~ r2_hidden(X5,sK4)
      | ~ m1_subset_1(X5,sK2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK5,sK2,sK3) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_865,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK3 != X2
    | sK2 != X1
    | sK5 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_34])).

cnf(c_866,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
    | k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(unflattening,[status(thm)],[c_865])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_868,plain,
    ( k1_relset_1(sK2,sK3,sK5) = sK2
    | k1_xboole_0 = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_866,c_33])).

cnf(c_2676,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_2680,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3786,plain,
    ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
    inference(superposition,[status(thm)],[c_2676,c_2680])).

cnf(c_3797,plain,
    ( k1_relat_1(sK5) = sK2
    | sK3 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_868,c_3786])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_2684,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4236,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3797,c_2684])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2691,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_4520,plain,
    ( sK3 = k1_xboole_0
    | m1_subset_1(sK1(X0,X1,sK5),sK2) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4236,c_2691])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_3144,plain,
    ( r1_tarski(k1_xboole_0,sK6) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3147,plain,
    ( r1_tarski(k1_xboole_0,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3144])).

cnf(c_2055,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_3149,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(X1,sK6)
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_2055])).

cnf(c_5537,plain,
    ( ~ r1_tarski(X0,sK6)
    | r1_tarski(sK3,sK6)
    | sK3 != X0 ),
    inference(instantiation,[status(thm)],[c_3149])).

cnf(c_5538,plain,
    ( sK3 != X0
    | r1_tarski(X0,sK6) != iProver_top
    | r1_tarski(sK3,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5537])).

cnf(c_5540,plain,
    ( sK3 != k1_xboole_0
    | r1_tarski(sK3,sK6) = iProver_top
    | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5538])).

cnf(c_7,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2689,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_3367,plain,
    ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2676,c_2689])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_6,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_284,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_6])).

cnf(c_285,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_284])).

cnf(c_357,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_8,c_285])).

cnf(c_2675,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_357])).

cnf(c_6064,plain,
    ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
    | v1_relat_1(sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_3367,c_2675])).

cnf(c_11,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f66])).

cnf(c_2688,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_6237,plain,
    ( v1_relat_1(sK5) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6064,c_2688])).

cnf(c_22,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_10,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_513,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_10])).

cnf(c_2672,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_513])).

cnf(c_3061,plain,
    ( r1_tarski(k2_relat_1(sK5),sK3) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2676,c_2672])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_2679,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3534,plain,
    ( k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
    inference(superposition,[status(thm)],[c_2676,c_2679])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2677,plain,
    ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3845,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3534,c_2677])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2685,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_19,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_490,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1
    | sK5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_35])).

cnf(c_491,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
    | ~ v1_relat_1(sK5)
    | k1_funct_1(sK5,X0) = X1 ),
    inference(unflattening,[status(thm)],[c_490])).

cnf(c_2673,plain,
    ( k1_funct_1(sK5,X0) = X1
    | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_491])).

cnf(c_4720,plain,
    ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2685,c_2673])).

cnf(c_5145,plain,
    ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3845,c_4720])).

cnf(c_6239,plain,
    ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6 ),
    inference(superposition,[status(thm)],[c_6237,c_5145])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_475,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_relat_1(X1)
    | sK5 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_35])).

cnf(c_476,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK5))
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
    | ~ v1_relat_1(sK5) ),
    inference(unflattening,[status(thm)],[c_475])).

cnf(c_2674,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_476])).

cnf(c_16,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2683,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_4103,plain,
    ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
    | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2674,c_2683])).

cnf(c_6383,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) != iProver_top
    | r2_hidden(sK6,k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_6239,c_4103])).

cnf(c_7183,plain,
    ( r2_hidden(sK6,k2_relat_1(sK5)) = iProver_top
    | r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6383,c_6237])).

cnf(c_7184,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) != iProver_top
    | r2_hidden(sK6,k2_relat_1(sK5)) = iProver_top ),
    inference(renaming,[status(thm)],[c_7183])).

cnf(c_7191,plain,
    ( sK3 = k1_xboole_0
    | r2_hidden(sK1(sK6,sK4,sK5),sK2) != iProver_top
    | r2_hidden(sK6,k2_relat_1(sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3797,c_7184])).

cnf(c_7189,plain,
    ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
    | r2_hidden(sK6,k2_relat_1(sK5)) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2684,c_7184])).

cnf(c_7207,plain,
    ( r2_hidden(sK6,k2_relat_1(sK5)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7191,c_3845,c_6237,c_7189])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_2693,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_7212,plain,
    ( r2_hidden(sK6,X0) = iProver_top
    | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7207,c_2693])).

cnf(c_7310,plain,
    ( r2_hidden(sK6,sK3) = iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3061,c_7212])).

cnf(c_7318,plain,
    ( r2_hidden(sK6,sK3) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7310,c_6237])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_2681,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_7324,plain,
    ( r1_tarski(sK3,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_7318,c_2681])).

cnf(c_15061,plain,
    ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
    | m1_subset_1(sK1(X0,X1,sK5),sK2) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4520,c_3147,c_5540,c_6237,c_7324])).

cnf(c_15062,plain,
    ( m1_subset_1(sK1(X0,X1,sK5),sK2) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
    inference(renaming,[status(thm)],[c_15061])).

cnf(c_31,negated_conjecture,
    ( ~ m1_subset_1(X0,sK2)
    | ~ r2_hidden(X0,sK4)
    | k1_funct_1(sK5,X0) != sK6 ),
    inference(cnf_transformation,[],[f90])).

cnf(c_2678,plain,
    ( k1_funct_1(sK5,X0) != sK6
    | m1_subset_1(X0,sK2) != iProver_top
    | r2_hidden(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_6387,plain,
    ( m1_subset_1(sK1(sK6,sK4,sK5),sK2) != iProver_top
    | r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_6239,c_2678])).

cnf(c_15069,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top
    | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_15062,c_6387])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_3272,plain,
    ( r2_hidden(sK1(sK6,X0,X1),X0)
    | ~ r2_hidden(sK6,k9_relat_1(X1,X0))
    | ~ v1_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_8256,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),sK4)
    | ~ r2_hidden(sK6,k9_relat_1(sK5,sK4))
    | ~ v1_relat_1(sK5) ),
    inference(instantiation,[status(thm)],[c_3272])).

cnf(c_8257,plain,
    ( r2_hidden(sK1(sK6,sK4,sK5),sK4) = iProver_top
    | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
    | v1_relat_1(sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8256])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_15069,c_8257,c_6237,c_3845])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:15:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.63/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.63/0.98  
% 3.63/0.98  ------  iProver source info
% 3.63/0.98  
% 3.63/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.63/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.63/0.98  git: non_committed_changes: false
% 3.63/0.98  git: last_make_outside_of_git: false
% 3.63/0.98  
% 3.63/0.98  ------ 
% 3.63/0.98  
% 3.63/0.98  ------ Input Options
% 3.63/0.98  
% 3.63/0.98  --out_options                           all
% 3.63/0.98  --tptp_safe_out                         true
% 3.63/0.98  --problem_path                          ""
% 3.63/0.98  --include_path                          ""
% 3.63/0.98  --clausifier                            res/vclausify_rel
% 3.63/0.98  --clausifier_options                    --mode clausify
% 3.63/0.98  --stdin                                 false
% 3.63/0.98  --stats_out                             all
% 3.63/0.98  
% 3.63/0.98  ------ General Options
% 3.63/0.98  
% 3.63/0.98  --fof                                   false
% 3.63/0.98  --time_out_real                         305.
% 3.63/0.98  --time_out_virtual                      -1.
% 3.63/0.98  --symbol_type_check                     false
% 3.63/0.98  --clausify_out                          false
% 3.63/0.98  --sig_cnt_out                           false
% 3.63/0.98  --trig_cnt_out                          false
% 3.63/0.98  --trig_cnt_out_tolerance                1.
% 3.63/0.98  --trig_cnt_out_sk_spl                   false
% 3.63/0.98  --abstr_cl_out                          false
% 3.63/0.98  
% 3.63/0.98  ------ Global Options
% 3.63/0.98  
% 3.63/0.98  --schedule                              default
% 3.63/0.98  --add_important_lit                     false
% 3.63/0.98  --prop_solver_per_cl                    1000
% 3.63/0.98  --min_unsat_core                        false
% 3.63/0.98  --soft_assumptions                      false
% 3.63/0.98  --soft_lemma_size                       3
% 3.63/0.98  --prop_impl_unit_size                   0
% 3.63/0.98  --prop_impl_unit                        []
% 3.63/0.98  --share_sel_clauses                     true
% 3.63/0.98  --reset_solvers                         false
% 3.63/0.98  --bc_imp_inh                            [conj_cone]
% 3.63/0.98  --conj_cone_tolerance                   3.
% 3.63/0.98  --extra_neg_conj                        none
% 3.63/0.98  --large_theory_mode                     true
% 3.63/0.98  --prolific_symb_bound                   200
% 3.63/0.98  --lt_threshold                          2000
% 3.63/0.98  --clause_weak_htbl                      true
% 3.63/0.98  --gc_record_bc_elim                     false
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing Options
% 3.63/0.98  
% 3.63/0.98  --preprocessing_flag                    true
% 3.63/0.98  --time_out_prep_mult                    0.1
% 3.63/0.98  --splitting_mode                        input
% 3.63/0.98  --splitting_grd                         true
% 3.63/0.98  --splitting_cvd                         false
% 3.63/0.98  --splitting_cvd_svl                     false
% 3.63/0.98  --splitting_nvd                         32
% 3.63/0.98  --sub_typing                            true
% 3.63/0.98  --prep_gs_sim                           true
% 3.63/0.98  --prep_unflatten                        true
% 3.63/0.98  --prep_res_sim                          true
% 3.63/0.98  --prep_upred                            true
% 3.63/0.98  --prep_sem_filter                       exhaustive
% 3.63/0.98  --prep_sem_filter_out                   false
% 3.63/0.98  --pred_elim                             true
% 3.63/0.98  --res_sim_input                         true
% 3.63/0.98  --eq_ax_congr_red                       true
% 3.63/0.98  --pure_diseq_elim                       true
% 3.63/0.98  --brand_transform                       false
% 3.63/0.98  --non_eq_to_eq                          false
% 3.63/0.98  --prep_def_merge                        true
% 3.63/0.98  --prep_def_merge_prop_impl              false
% 3.63/0.98  --prep_def_merge_mbd                    true
% 3.63/0.98  --prep_def_merge_tr_red                 false
% 3.63/0.98  --prep_def_merge_tr_cl                  false
% 3.63/0.98  --smt_preprocessing                     true
% 3.63/0.98  --smt_ac_axioms                         fast
% 3.63/0.98  --preprocessed_out                      false
% 3.63/0.98  --preprocessed_stats                    false
% 3.63/0.98  
% 3.63/0.98  ------ Abstraction refinement Options
% 3.63/0.98  
% 3.63/0.98  --abstr_ref                             []
% 3.63/0.98  --abstr_ref_prep                        false
% 3.63/0.98  --abstr_ref_until_sat                   false
% 3.63/0.98  --abstr_ref_sig_restrict                funpre
% 3.63/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/0.98  --abstr_ref_under                       []
% 3.63/0.98  
% 3.63/0.98  ------ SAT Options
% 3.63/0.98  
% 3.63/0.98  --sat_mode                              false
% 3.63/0.98  --sat_fm_restart_options                ""
% 3.63/0.98  --sat_gr_def                            false
% 3.63/0.98  --sat_epr_types                         true
% 3.63/0.98  --sat_non_cyclic_types                  false
% 3.63/0.98  --sat_finite_models                     false
% 3.63/0.98  --sat_fm_lemmas                         false
% 3.63/0.98  --sat_fm_prep                           false
% 3.63/0.98  --sat_fm_uc_incr                        true
% 3.63/0.98  --sat_out_model                         small
% 3.63/0.98  --sat_out_clauses                       false
% 3.63/0.98  
% 3.63/0.98  ------ QBF Options
% 3.63/0.98  
% 3.63/0.98  --qbf_mode                              false
% 3.63/0.98  --qbf_elim_univ                         false
% 3.63/0.98  --qbf_dom_inst                          none
% 3.63/0.98  --qbf_dom_pre_inst                      false
% 3.63/0.98  --qbf_sk_in                             false
% 3.63/0.98  --qbf_pred_elim                         true
% 3.63/0.98  --qbf_split                             512
% 3.63/0.98  
% 3.63/0.98  ------ BMC1 Options
% 3.63/0.98  
% 3.63/0.98  --bmc1_incremental                      false
% 3.63/0.98  --bmc1_axioms                           reachable_all
% 3.63/0.98  --bmc1_min_bound                        0
% 3.63/0.98  --bmc1_max_bound                        -1
% 3.63/0.98  --bmc1_max_bound_default                -1
% 3.63/0.98  --bmc1_symbol_reachability              true
% 3.63/0.98  --bmc1_property_lemmas                  false
% 3.63/0.98  --bmc1_k_induction                      false
% 3.63/0.98  --bmc1_non_equiv_states                 false
% 3.63/0.98  --bmc1_deadlock                         false
% 3.63/0.98  --bmc1_ucm                              false
% 3.63/0.98  --bmc1_add_unsat_core                   none
% 3.63/0.98  --bmc1_unsat_core_children              false
% 3.63/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/0.98  --bmc1_out_stat                         full
% 3.63/0.98  --bmc1_ground_init                      false
% 3.63/0.98  --bmc1_pre_inst_next_state              false
% 3.63/0.98  --bmc1_pre_inst_state                   false
% 3.63/0.98  --bmc1_pre_inst_reach_state             false
% 3.63/0.98  --bmc1_out_unsat_core                   false
% 3.63/0.98  --bmc1_aig_witness_out                  false
% 3.63/0.98  --bmc1_verbose                          false
% 3.63/0.98  --bmc1_dump_clauses_tptp                false
% 3.63/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.63/0.98  --bmc1_dump_file                        -
% 3.63/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.63/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.63/0.98  --bmc1_ucm_extend_mode                  1
% 3.63/0.98  --bmc1_ucm_init_mode                    2
% 3.63/0.98  --bmc1_ucm_cone_mode                    none
% 3.63/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.63/0.98  --bmc1_ucm_relax_model                  4
% 3.63/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.63/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/0.98  --bmc1_ucm_layered_model                none
% 3.63/0.98  --bmc1_ucm_max_lemma_size               10
% 3.63/0.98  
% 3.63/0.98  ------ AIG Options
% 3.63/0.98  
% 3.63/0.98  --aig_mode                              false
% 3.63/0.98  
% 3.63/0.98  ------ Instantiation Options
% 3.63/0.98  
% 3.63/0.98  --instantiation_flag                    true
% 3.63/0.98  --inst_sos_flag                         false
% 3.63/0.98  --inst_sos_phase                        true
% 3.63/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel_side                     num_symb
% 3.63/0.98  --inst_solver_per_active                1400
% 3.63/0.98  --inst_solver_calls_frac                1.
% 3.63/0.98  --inst_passive_queue_type               priority_queues
% 3.63/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/0.98  --inst_passive_queues_freq              [25;2]
% 3.63/0.98  --inst_dismatching                      true
% 3.63/0.98  --inst_eager_unprocessed_to_passive     true
% 3.63/0.98  --inst_prop_sim_given                   true
% 3.63/0.98  --inst_prop_sim_new                     false
% 3.63/0.98  --inst_subs_new                         false
% 3.63/0.98  --inst_eq_res_simp                      false
% 3.63/0.98  --inst_subs_given                       false
% 3.63/0.98  --inst_orphan_elimination               true
% 3.63/0.98  --inst_learning_loop_flag               true
% 3.63/0.98  --inst_learning_start                   3000
% 3.63/0.98  --inst_learning_factor                  2
% 3.63/0.98  --inst_start_prop_sim_after_learn       3
% 3.63/0.98  --inst_sel_renew                        solver
% 3.63/0.98  --inst_lit_activity_flag                true
% 3.63/0.98  --inst_restr_to_given                   false
% 3.63/0.98  --inst_activity_threshold               500
% 3.63/0.98  --inst_out_proof                        true
% 3.63/0.98  
% 3.63/0.98  ------ Resolution Options
% 3.63/0.98  
% 3.63/0.98  --resolution_flag                       true
% 3.63/0.98  --res_lit_sel                           adaptive
% 3.63/0.98  --res_lit_sel_side                      none
% 3.63/0.98  --res_ordering                          kbo
% 3.63/0.98  --res_to_prop_solver                    active
% 3.63/0.98  --res_prop_simpl_new                    false
% 3.63/0.98  --res_prop_simpl_given                  true
% 3.63/0.98  --res_passive_queue_type                priority_queues
% 3.63/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/0.98  --res_passive_queues_freq               [15;5]
% 3.63/0.98  --res_forward_subs                      full
% 3.63/0.98  --res_backward_subs                     full
% 3.63/0.98  --res_forward_subs_resolution           true
% 3.63/0.98  --res_backward_subs_resolution          true
% 3.63/0.98  --res_orphan_elimination                true
% 3.63/0.98  --res_time_limit                        2.
% 3.63/0.98  --res_out_proof                         true
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Options
% 3.63/0.98  
% 3.63/0.98  --superposition_flag                    true
% 3.63/0.98  --sup_passive_queue_type                priority_queues
% 3.63/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.63/0.98  --demod_completeness_check              fast
% 3.63/0.98  --demod_use_ground                      true
% 3.63/0.98  --sup_to_prop_solver                    passive
% 3.63/0.98  --sup_prop_simpl_new                    true
% 3.63/0.98  --sup_prop_simpl_given                  true
% 3.63/0.98  --sup_fun_splitting                     false
% 3.63/0.98  --sup_smt_interval                      50000
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Simplification Setup
% 3.63/0.98  
% 3.63/0.98  --sup_indices_passive                   []
% 3.63/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_full_bw                           [BwDemod]
% 3.63/0.98  --sup_immed_triv                        [TrivRules]
% 3.63/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_immed_bw_main                     []
% 3.63/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  
% 3.63/0.98  ------ Combination Options
% 3.63/0.98  
% 3.63/0.98  --comb_res_mult                         3
% 3.63/0.98  --comb_sup_mult                         2
% 3.63/0.98  --comb_inst_mult                        10
% 3.63/0.98  
% 3.63/0.98  ------ Debug Options
% 3.63/0.98  
% 3.63/0.98  --dbg_backtrace                         false
% 3.63/0.98  --dbg_dump_prop_clauses                 false
% 3.63/0.98  --dbg_dump_prop_clauses_file            -
% 3.63/0.98  --dbg_out_stat                          false
% 3.63/0.98  ------ Parsing...
% 3.63/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 3 0s  sf_e  pe_s  pe_e 
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.63/0.98  ------ Proving...
% 3.63/0.98  ------ Problem Properties 
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  clauses                                 27
% 3.63/0.98  conjectures                             3
% 3.63/0.98  EPR                                     5
% 3.63/0.98  Horn                                    24
% 3.63/0.98  unary                                   4
% 3.63/0.98  binary                                  9
% 3.63/0.98  lits                                    67
% 3.63/0.98  lits eq                                 11
% 3.63/0.98  fd_pure                                 0
% 3.63/0.98  fd_pseudo                               0
% 3.63/0.98  fd_cond                                 0
% 3.63/0.98  fd_pseudo_cond                          1
% 3.63/0.98  AC symbols                              0
% 3.63/0.98  
% 3.63/0.98  ------ Schedule dynamic 5 is on 
% 3.63/0.98  
% 3.63/0.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  ------ 
% 3.63/0.98  Current options:
% 3.63/0.98  ------ 
% 3.63/0.98  
% 3.63/0.98  ------ Input Options
% 3.63/0.98  
% 3.63/0.98  --out_options                           all
% 3.63/0.98  --tptp_safe_out                         true
% 3.63/0.98  --problem_path                          ""
% 3.63/0.98  --include_path                          ""
% 3.63/0.98  --clausifier                            res/vclausify_rel
% 3.63/0.98  --clausifier_options                    --mode clausify
% 3.63/0.98  --stdin                                 false
% 3.63/0.98  --stats_out                             all
% 3.63/0.98  
% 3.63/0.98  ------ General Options
% 3.63/0.98  
% 3.63/0.98  --fof                                   false
% 3.63/0.98  --time_out_real                         305.
% 3.63/0.98  --time_out_virtual                      -1.
% 3.63/0.98  --symbol_type_check                     false
% 3.63/0.98  --clausify_out                          false
% 3.63/0.98  --sig_cnt_out                           false
% 3.63/0.98  --trig_cnt_out                          false
% 3.63/0.98  --trig_cnt_out_tolerance                1.
% 3.63/0.98  --trig_cnt_out_sk_spl                   false
% 3.63/0.98  --abstr_cl_out                          false
% 3.63/0.98  
% 3.63/0.98  ------ Global Options
% 3.63/0.98  
% 3.63/0.98  --schedule                              default
% 3.63/0.98  --add_important_lit                     false
% 3.63/0.98  --prop_solver_per_cl                    1000
% 3.63/0.98  --min_unsat_core                        false
% 3.63/0.98  --soft_assumptions                      false
% 3.63/0.98  --soft_lemma_size                       3
% 3.63/0.98  --prop_impl_unit_size                   0
% 3.63/0.98  --prop_impl_unit                        []
% 3.63/0.98  --share_sel_clauses                     true
% 3.63/0.98  --reset_solvers                         false
% 3.63/0.98  --bc_imp_inh                            [conj_cone]
% 3.63/0.98  --conj_cone_tolerance                   3.
% 3.63/0.98  --extra_neg_conj                        none
% 3.63/0.98  --large_theory_mode                     true
% 3.63/0.98  --prolific_symb_bound                   200
% 3.63/0.98  --lt_threshold                          2000
% 3.63/0.98  --clause_weak_htbl                      true
% 3.63/0.98  --gc_record_bc_elim                     false
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing Options
% 3.63/0.98  
% 3.63/0.98  --preprocessing_flag                    true
% 3.63/0.98  --time_out_prep_mult                    0.1
% 3.63/0.98  --splitting_mode                        input
% 3.63/0.98  --splitting_grd                         true
% 3.63/0.98  --splitting_cvd                         false
% 3.63/0.98  --splitting_cvd_svl                     false
% 3.63/0.98  --splitting_nvd                         32
% 3.63/0.98  --sub_typing                            true
% 3.63/0.98  --prep_gs_sim                           true
% 3.63/0.98  --prep_unflatten                        true
% 3.63/0.98  --prep_res_sim                          true
% 3.63/0.98  --prep_upred                            true
% 3.63/0.98  --prep_sem_filter                       exhaustive
% 3.63/0.98  --prep_sem_filter_out                   false
% 3.63/0.98  --pred_elim                             true
% 3.63/0.98  --res_sim_input                         true
% 3.63/0.98  --eq_ax_congr_red                       true
% 3.63/0.98  --pure_diseq_elim                       true
% 3.63/0.98  --brand_transform                       false
% 3.63/0.98  --non_eq_to_eq                          false
% 3.63/0.98  --prep_def_merge                        true
% 3.63/0.98  --prep_def_merge_prop_impl              false
% 3.63/0.98  --prep_def_merge_mbd                    true
% 3.63/0.98  --prep_def_merge_tr_red                 false
% 3.63/0.98  --prep_def_merge_tr_cl                  false
% 3.63/0.98  --smt_preprocessing                     true
% 3.63/0.98  --smt_ac_axioms                         fast
% 3.63/0.98  --preprocessed_out                      false
% 3.63/0.98  --preprocessed_stats                    false
% 3.63/0.98  
% 3.63/0.98  ------ Abstraction refinement Options
% 3.63/0.98  
% 3.63/0.98  --abstr_ref                             []
% 3.63/0.98  --abstr_ref_prep                        false
% 3.63/0.98  --abstr_ref_until_sat                   false
% 3.63/0.98  --abstr_ref_sig_restrict                funpre
% 3.63/0.98  --abstr_ref_af_restrict_to_split_sk     false
% 3.63/0.98  --abstr_ref_under                       []
% 3.63/0.98  
% 3.63/0.98  ------ SAT Options
% 3.63/0.98  
% 3.63/0.98  --sat_mode                              false
% 3.63/0.98  --sat_fm_restart_options                ""
% 3.63/0.98  --sat_gr_def                            false
% 3.63/0.98  --sat_epr_types                         true
% 3.63/0.98  --sat_non_cyclic_types                  false
% 3.63/0.98  --sat_finite_models                     false
% 3.63/0.98  --sat_fm_lemmas                         false
% 3.63/0.98  --sat_fm_prep                           false
% 3.63/0.98  --sat_fm_uc_incr                        true
% 3.63/0.98  --sat_out_model                         small
% 3.63/0.98  --sat_out_clauses                       false
% 3.63/0.98  
% 3.63/0.98  ------ QBF Options
% 3.63/0.98  
% 3.63/0.98  --qbf_mode                              false
% 3.63/0.98  --qbf_elim_univ                         false
% 3.63/0.98  --qbf_dom_inst                          none
% 3.63/0.98  --qbf_dom_pre_inst                      false
% 3.63/0.98  --qbf_sk_in                             false
% 3.63/0.98  --qbf_pred_elim                         true
% 3.63/0.98  --qbf_split                             512
% 3.63/0.98  
% 3.63/0.98  ------ BMC1 Options
% 3.63/0.98  
% 3.63/0.98  --bmc1_incremental                      false
% 3.63/0.98  --bmc1_axioms                           reachable_all
% 3.63/0.98  --bmc1_min_bound                        0
% 3.63/0.98  --bmc1_max_bound                        -1
% 3.63/0.98  --bmc1_max_bound_default                -1
% 3.63/0.98  --bmc1_symbol_reachability              true
% 3.63/0.98  --bmc1_property_lemmas                  false
% 3.63/0.98  --bmc1_k_induction                      false
% 3.63/0.98  --bmc1_non_equiv_states                 false
% 3.63/0.98  --bmc1_deadlock                         false
% 3.63/0.98  --bmc1_ucm                              false
% 3.63/0.98  --bmc1_add_unsat_core                   none
% 3.63/0.98  --bmc1_unsat_core_children              false
% 3.63/0.98  --bmc1_unsat_core_extrapolate_axioms    false
% 3.63/0.98  --bmc1_out_stat                         full
% 3.63/0.98  --bmc1_ground_init                      false
% 3.63/0.98  --bmc1_pre_inst_next_state              false
% 3.63/0.98  --bmc1_pre_inst_state                   false
% 3.63/0.98  --bmc1_pre_inst_reach_state             false
% 3.63/0.98  --bmc1_out_unsat_core                   false
% 3.63/0.98  --bmc1_aig_witness_out                  false
% 3.63/0.98  --bmc1_verbose                          false
% 3.63/0.98  --bmc1_dump_clauses_tptp                false
% 3.63/0.98  --bmc1_dump_unsat_core_tptp             false
% 3.63/0.98  --bmc1_dump_file                        -
% 3.63/0.98  --bmc1_ucm_expand_uc_limit              128
% 3.63/0.98  --bmc1_ucm_n_expand_iterations          6
% 3.63/0.98  --bmc1_ucm_extend_mode                  1
% 3.63/0.98  --bmc1_ucm_init_mode                    2
% 3.63/0.98  --bmc1_ucm_cone_mode                    none
% 3.63/0.98  --bmc1_ucm_reduced_relation_type        0
% 3.63/0.98  --bmc1_ucm_relax_model                  4
% 3.63/0.98  --bmc1_ucm_full_tr_after_sat            true
% 3.63/0.98  --bmc1_ucm_expand_neg_assumptions       false
% 3.63/0.98  --bmc1_ucm_layered_model                none
% 3.63/0.98  --bmc1_ucm_max_lemma_size               10
% 3.63/0.98  
% 3.63/0.98  ------ AIG Options
% 3.63/0.98  
% 3.63/0.98  --aig_mode                              false
% 3.63/0.98  
% 3.63/0.98  ------ Instantiation Options
% 3.63/0.98  
% 3.63/0.98  --instantiation_flag                    true
% 3.63/0.98  --inst_sos_flag                         false
% 3.63/0.98  --inst_sos_phase                        true
% 3.63/0.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.63/0.98  --inst_lit_sel_side                     none
% 3.63/0.98  --inst_solver_per_active                1400
% 3.63/0.98  --inst_solver_calls_frac                1.
% 3.63/0.98  --inst_passive_queue_type               priority_queues
% 3.63/0.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.63/0.98  --inst_passive_queues_freq              [25;2]
% 3.63/0.98  --inst_dismatching                      true
% 3.63/0.98  --inst_eager_unprocessed_to_passive     true
% 3.63/0.98  --inst_prop_sim_given                   true
% 3.63/0.98  --inst_prop_sim_new                     false
% 3.63/0.98  --inst_subs_new                         false
% 3.63/0.98  --inst_eq_res_simp                      false
% 3.63/0.98  --inst_subs_given                       false
% 3.63/0.98  --inst_orphan_elimination               true
% 3.63/0.98  --inst_learning_loop_flag               true
% 3.63/0.98  --inst_learning_start                   3000
% 3.63/0.98  --inst_learning_factor                  2
% 3.63/0.98  --inst_start_prop_sim_after_learn       3
% 3.63/0.98  --inst_sel_renew                        solver
% 3.63/0.98  --inst_lit_activity_flag                true
% 3.63/0.98  --inst_restr_to_given                   false
% 3.63/0.98  --inst_activity_threshold               500
% 3.63/0.98  --inst_out_proof                        true
% 3.63/0.98  
% 3.63/0.98  ------ Resolution Options
% 3.63/0.98  
% 3.63/0.98  --resolution_flag                       false
% 3.63/0.98  --res_lit_sel                           adaptive
% 3.63/0.98  --res_lit_sel_side                      none
% 3.63/0.98  --res_ordering                          kbo
% 3.63/0.98  --res_to_prop_solver                    active
% 3.63/0.98  --res_prop_simpl_new                    false
% 3.63/0.98  --res_prop_simpl_given                  true
% 3.63/0.98  --res_passive_queue_type                priority_queues
% 3.63/0.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.63/0.98  --res_passive_queues_freq               [15;5]
% 3.63/0.98  --res_forward_subs                      full
% 3.63/0.98  --res_backward_subs                     full
% 3.63/0.98  --res_forward_subs_resolution           true
% 3.63/0.98  --res_backward_subs_resolution          true
% 3.63/0.98  --res_orphan_elimination                true
% 3.63/0.98  --res_time_limit                        2.
% 3.63/0.98  --res_out_proof                         true
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Options
% 3.63/0.98  
% 3.63/0.98  --superposition_flag                    true
% 3.63/0.98  --sup_passive_queue_type                priority_queues
% 3.63/0.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.63/0.98  --sup_passive_queues_freq               [8;1;4]
% 3.63/0.98  --demod_completeness_check              fast
% 3.63/0.98  --demod_use_ground                      true
% 3.63/0.98  --sup_to_prop_solver                    passive
% 3.63/0.98  --sup_prop_simpl_new                    true
% 3.63/0.98  --sup_prop_simpl_given                  true
% 3.63/0.98  --sup_fun_splitting                     false
% 3.63/0.98  --sup_smt_interval                      50000
% 3.63/0.98  
% 3.63/0.98  ------ Superposition Simplification Setup
% 3.63/0.98  
% 3.63/0.98  --sup_indices_passive                   []
% 3.63/0.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 3.63/0.98  --sup_full_triv                         [TrivRules;PropSubs]
% 3.63/0.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_full_bw                           [BwDemod]
% 3.63/0.98  --sup_immed_triv                        [TrivRules]
% 3.63/0.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.63/0.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_immed_bw_main                     []
% 3.63/0.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  --sup_input_triv                        [Unflattening;TrivRules]
% 3.63/0.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 3.63/0.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 3.63/0.98  
% 3.63/0.98  ------ Combination Options
% 3.63/0.98  
% 3.63/0.98  --comb_res_mult                         3
% 3.63/0.98  --comb_sup_mult                         2
% 3.63/0.98  --comb_inst_mult                        10
% 3.63/0.98  
% 3.63/0.98  ------ Debug Options
% 3.63/0.98  
% 3.63/0.98  --dbg_backtrace                         false
% 3.63/0.98  --dbg_dump_prop_clauses                 false
% 3.63/0.98  --dbg_dump_prop_clauses_file            -
% 3.63/0.98  --dbg_out_stat                          false
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  ------ Proving...
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  % SZS status Theorem for theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  fof(f17,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f35,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.98    inference(ennf_transformation,[],[f17])).
% 3.63/0.98  
% 3.63/0.98  fof(f36,plain,(
% 3.63/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.98    inference(flattening,[],[f35])).
% 3.63/0.98  
% 3.63/0.98  fof(f51,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.98    inference(nnf_transformation,[],[f36])).
% 3.63/0.98  
% 3.63/0.98  fof(f80,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f51])).
% 3.63/0.98  
% 3.63/0.98  fof(f18,conjecture,(
% 3.63/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f19,negated_conjecture,(
% 3.63/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.63/0.98    inference(negated_conjecture,[],[f18])).
% 3.63/0.98  
% 3.63/0.98  fof(f37,plain,(
% 3.63/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.63/0.98    inference(ennf_transformation,[],[f19])).
% 3.63/0.98  
% 3.63/0.98  fof(f38,plain,(
% 3.63/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.63/0.98    inference(flattening,[],[f37])).
% 3.63/0.98  
% 3.63/0.98  fof(f53,plain,(
% 3.63/0.98    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK6 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK6,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f52,plain,(
% 3.63/0.98    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK5,X5) != X4 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) & r2_hidden(X4,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f54,plain,(
% 3.63/0.98    (! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) & r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) & v1_funct_2(sK5,sK2,sK3) & v1_funct_1(sK5)),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5,sK6])],[f38,f53,f52])).
% 3.63/0.98  
% 3.63/0.98  fof(f87,plain,(
% 3.63/0.98    v1_funct_2(sK5,sK2,sK3)),
% 3.63/0.98    inference(cnf_transformation,[],[f54])).
% 3.63/0.98  
% 3.63/0.98  fof(f88,plain,(
% 3.63/0.98    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))),
% 3.63/0.98    inference(cnf_transformation,[],[f54])).
% 3.63/0.98  
% 3.63/0.98  fof(f15,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f33,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.98    inference(ennf_transformation,[],[f15])).
% 3.63/0.98  
% 3.63/0.98  fof(f78,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f33])).
% 3.63/0.98  
% 3.63/0.98  fof(f10,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f26,plain,(
% 3.63/0.98    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.63/0.98    inference(ennf_transformation,[],[f10])).
% 3.63/0.98  
% 3.63/0.98  fof(f45,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.63/0.98    inference(nnf_transformation,[],[f26])).
% 3.63/0.98  
% 3.63/0.98  fof(f46,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.63/0.98    inference(rectify,[],[f45])).
% 3.63/0.98  
% 3.63/0.98  fof(f47,plain,(
% 3.63/0.98    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f48,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f46,f47])).
% 3.63/0.98  
% 3.63/0.98  fof(f67,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f48])).
% 3.63/0.98  
% 3.63/0.98  fof(f5,axiom,(
% 3.63/0.98    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f23,plain,(
% 3.63/0.98    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.63/0.98    inference(ennf_transformation,[],[f5])).
% 3.63/0.98  
% 3.63/0.98  fof(f60,plain,(
% 3.63/0.98    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f23])).
% 3.63/0.98  
% 3.63/0.98  fof(f3,axiom,(
% 3.63/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f58,plain,(
% 3.63/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f3])).
% 3.63/0.98  
% 3.63/0.98  fof(f6,axiom,(
% 3.63/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f43,plain,(
% 3.63/0.98    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.63/0.98    inference(nnf_transformation,[],[f6])).
% 3.63/0.98  
% 3.63/0.98  fof(f61,plain,(
% 3.63/0.98    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f43])).
% 3.63/0.98  
% 3.63/0.98  fof(f7,axiom,(
% 3.63/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f24,plain,(
% 3.63/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.63/0.98    inference(ennf_transformation,[],[f7])).
% 3.63/0.98  
% 3.63/0.98  fof(f63,plain,(
% 3.63/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f24])).
% 3.63/0.98  
% 3.63/0.98  fof(f62,plain,(
% 3.63/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f43])).
% 3.63/0.98  
% 3.63/0.98  fof(f9,axiom,(
% 3.63/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f66,plain,(
% 3.63/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f9])).
% 3.63/0.98  
% 3.63/0.98  fof(f14,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f20,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.63/0.98    inference(pure_predicate_removal,[],[f14])).
% 3.63/0.98  
% 3.63/0.98  fof(f32,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.98    inference(ennf_transformation,[],[f20])).
% 3.63/0.98  
% 3.63/0.98  fof(f77,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f32])).
% 3.63/0.98  
% 3.63/0.98  fof(f8,axiom,(
% 3.63/0.98    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f25,plain,(
% 3.63/0.98    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.63/0.98    inference(ennf_transformation,[],[f8])).
% 3.63/0.98  
% 3.63/0.98  fof(f44,plain,(
% 3.63/0.98    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.63/0.98    inference(nnf_transformation,[],[f25])).
% 3.63/0.98  
% 3.63/0.98  fof(f64,plain,(
% 3.63/0.98    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f44])).
% 3.63/0.98  
% 3.63/0.98  fof(f16,axiom,(
% 3.63/0.98    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f34,plain,(
% 3.63/0.98    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.63/0.98    inference(ennf_transformation,[],[f16])).
% 3.63/0.98  
% 3.63/0.98  fof(f79,plain,(
% 3.63/0.98    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.63/0.98    inference(cnf_transformation,[],[f34])).
% 3.63/0.98  
% 3.63/0.98  fof(f89,plain,(
% 3.63/0.98    r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4))),
% 3.63/0.98    inference(cnf_transformation,[],[f54])).
% 3.63/0.98  
% 3.63/0.98  fof(f68,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f48])).
% 3.63/0.98  
% 3.63/0.98  fof(f12,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f29,plain,(
% 3.63/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 3.63/0.98    inference(ennf_transformation,[],[f12])).
% 3.63/0.98  
% 3.63/0.98  fof(f30,plain,(
% 3.63/0.98    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.63/0.98    inference(flattening,[],[f29])).
% 3.63/0.98  
% 3.63/0.98  fof(f49,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.63/0.98    inference(nnf_transformation,[],[f30])).
% 3.63/0.98  
% 3.63/0.98  fof(f50,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 3.63/0.98    inference(flattening,[],[f49])).
% 3.63/0.98  
% 3.63/0.98  fof(f74,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f50])).
% 3.63/0.98  
% 3.63/0.98  fof(f86,plain,(
% 3.63/0.98    v1_funct_1(sK5)),
% 3.63/0.98    inference(cnf_transformation,[],[f54])).
% 3.63/0.98  
% 3.63/0.98  fof(f75,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f50])).
% 3.63/0.98  
% 3.63/0.98  fof(f91,plain,(
% 3.63/0.98    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 3.63/0.98    inference(equality_resolution,[],[f75])).
% 3.63/0.98  
% 3.63/0.98  fof(f11,axiom,(
% 3.63/0.98    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f27,plain,(
% 3.63/0.98    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.63/0.98    inference(ennf_transformation,[],[f11])).
% 3.63/0.98  
% 3.63/0.98  fof(f28,plain,(
% 3.63/0.98    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.63/0.98    inference(flattening,[],[f27])).
% 3.63/0.98  
% 3.63/0.98  fof(f72,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f28])).
% 3.63/0.98  
% 3.63/0.98  fof(f2,axiom,(
% 3.63/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f21,plain,(
% 3.63/0.98    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 3.63/0.98    inference(ennf_transformation,[],[f2])).
% 3.63/0.98  
% 3.63/0.98  fof(f39,plain,(
% 3.63/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 3.63/0.98    inference(nnf_transformation,[],[f21])).
% 3.63/0.98  
% 3.63/0.98  fof(f40,plain,(
% 3.63/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.63/0.98    inference(rectify,[],[f39])).
% 3.63/0.98  
% 3.63/0.98  fof(f41,plain,(
% 3.63/0.98    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 3.63/0.98    introduced(choice_axiom,[])).
% 3.63/0.98  
% 3.63/0.98  fof(f42,plain,(
% 3.63/0.98    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 3.63/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f40,f41])).
% 3.63/0.98  
% 3.63/0.98  fof(f55,plain,(
% 3.63/0.98    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f42])).
% 3.63/0.98  
% 3.63/0.98  fof(f13,axiom,(
% 3.63/0.98    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.63/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.63/0.98  
% 3.63/0.98  fof(f31,plain,(
% 3.63/0.98    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.63/0.98    inference(ennf_transformation,[],[f13])).
% 3.63/0.98  
% 3.63/0.98  fof(f76,plain,(
% 3.63/0.98    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f31])).
% 3.63/0.98  
% 3.63/0.98  fof(f90,plain,(
% 3.63/0.98    ( ! [X5] : (k1_funct_1(sK5,X5) != sK6 | ~r2_hidden(X5,sK4) | ~m1_subset_1(X5,sK2)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f54])).
% 3.63/0.98  
% 3.63/0.98  fof(f69,plain,(
% 3.63/0.98    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.63/0.98    inference(cnf_transformation,[],[f48])).
% 3.63/0.98  
% 3.63/0.98  cnf(c_30,plain,
% 3.63/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.63/0.98      | k1_xboole_0 = X2 ),
% 3.63/0.98      inference(cnf_transformation,[],[f80]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_34,negated_conjecture,
% 3.63/0.98      ( v1_funct_2(sK5,sK2,sK3) ),
% 3.63/0.98      inference(cnf_transformation,[],[f87]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_865,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.63/0.98      | sK3 != X2
% 3.63/0.98      | sK2 != X1
% 3.63/0.98      | sK5 != X0
% 3.63/0.98      | k1_xboole_0 = X2 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_30,c_34]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_866,plain,
% 3.63/0.98      ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3)))
% 3.63/0.98      | k1_relset_1(sK2,sK3,sK5) = sK2
% 3.63/0.98      | k1_xboole_0 = sK3 ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_865]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_33,negated_conjecture,
% 3.63/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) ),
% 3.63/0.98      inference(cnf_transformation,[],[f88]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_868,plain,
% 3.63/0.98      ( k1_relset_1(sK2,sK3,sK5) = sK2 | k1_xboole_0 = sK3 ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_866,c_33]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2676,plain,
% 3.63/0.98      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK2,sK3))) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_23,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f78]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2680,plain,
% 3.63/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.63/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3786,plain,
% 3.63/0.98      ( k1_relset_1(sK2,sK3,sK5) = k1_relat_1(sK5) ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_2676,c_2680]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3797,plain,
% 3.63/0.98      ( k1_relat_1(sK5) = sK2 | sK3 = k1_xboole_0 ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_868,c_3786]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_15,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.63/0.98      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 3.63/0.98      | ~ v1_relat_1(X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2684,plain,
% 3.63/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.63/0.98      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.63/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4236,plain,
% 3.63/0.98      ( sK3 = k1_xboole_0
% 3.63/0.98      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.63/0.98      | r2_hidden(sK1(X0,X1,sK5),sK2) = iProver_top
% 3.63/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_3797,c_2684]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5,plain,
% 3.63/0.98      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2691,plain,
% 3.63/0.98      ( m1_subset_1(X0,X1) = iProver_top
% 3.63/0.98      | r2_hidden(X0,X1) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4520,plain,
% 3.63/0.98      ( sK3 = k1_xboole_0
% 3.63/0.98      | m1_subset_1(sK1(X0,X1,sK5),sK2) = iProver_top
% 3.63/0.98      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.63/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_4236,c_2691]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3,plain,
% 3.63/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f58]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3144,plain,
% 3.63/0.98      ( r1_tarski(k1_xboole_0,sK6) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3147,plain,
% 3.63/0.98      ( r1_tarski(k1_xboole_0,sK6) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_3144]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2055,plain,
% 3.63/0.98      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.63/0.98      theory(equality) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3149,plain,
% 3.63/0.98      ( ~ r1_tarski(X0,sK6) | r1_tarski(X1,sK6) | X1 != X0 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_2055]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5537,plain,
% 3.63/0.98      ( ~ r1_tarski(X0,sK6) | r1_tarski(sK3,sK6) | sK3 != X0 ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_3149]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5538,plain,
% 3.63/0.98      ( sK3 != X0
% 3.63/0.98      | r1_tarski(X0,sK6) != iProver_top
% 3.63/0.98      | r1_tarski(sK3,sK6) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_5537]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5540,plain,
% 3.63/0.98      ( sK3 != k1_xboole_0
% 3.63/0.98      | r1_tarski(sK3,sK6) = iProver_top
% 3.63/0.98      | r1_tarski(k1_xboole_0,sK6) != iProver_top ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_5538]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2689,plain,
% 3.63/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.63/0.98      | r1_tarski(X0,X1) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3367,plain,
% 3.63/0.98      ( r1_tarski(sK5,k2_zfmisc_1(sK2,sK3)) = iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_2676,c_2689]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.63/0.98      | ~ v1_relat_1(X1)
% 3.63/0.98      | v1_relat_1(X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6,plain,
% 3.63/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_284,plain,
% 3.63/0.98      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.63/0.98      inference(prop_impl,[status(thm)],[c_6]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_285,plain,
% 3.63/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.63/0.98      inference(renaming,[status(thm)],[c_284]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_357,plain,
% 3.63/0.98      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.63/0.98      inference(bin_hyper_res,[status(thm)],[c_8,c_285]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2675,plain,
% 3.63/0.98      ( r1_tarski(X0,X1) != iProver_top
% 3.63/0.98      | v1_relat_1(X1) != iProver_top
% 3.63/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_357]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6064,plain,
% 3.63/0.98      ( v1_relat_1(k2_zfmisc_1(sK2,sK3)) != iProver_top
% 3.63/0.98      | v1_relat_1(sK5) = iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_3367,c_2675]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_11,plain,
% 3.63/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.63/0.98      inference(cnf_transformation,[],[f66]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2688,plain,
% 3.63/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6237,plain,
% 3.63/0.98      ( v1_relat_1(sK5) = iProver_top ),
% 3.63/0.98      inference(forward_subsumption_resolution,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_6064,c_2688]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_22,plain,
% 3.63/0.98      ( v5_relat_1(X0,X1)
% 3.63/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.63/0.98      inference(cnf_transformation,[],[f77]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_10,plain,
% 3.63/0.98      ( ~ v5_relat_1(X0,X1)
% 3.63/0.98      | r1_tarski(k2_relat_1(X0),X1)
% 3.63/0.98      | ~ v1_relat_1(X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_513,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | r1_tarski(k2_relat_1(X0),X2)
% 3.63/0.98      | ~ v1_relat_1(X0) ),
% 3.63/0.98      inference(resolution,[status(thm)],[c_22,c_10]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2672,plain,
% 3.63/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.63/0.98      | r1_tarski(k2_relat_1(X0),X2) = iProver_top
% 3.63/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_513]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3061,plain,
% 3.63/0.98      ( r1_tarski(k2_relat_1(sK5),sK3) = iProver_top
% 3.63/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_2676,c_2672]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_24,plain,
% 3.63/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.63/0.98      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.63/0.98      inference(cnf_transformation,[],[f79]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2679,plain,
% 3.63/0.98      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.63/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3534,plain,
% 3.63/0.98      ( k7_relset_1(sK2,sK3,sK5,X0) = k9_relat_1(sK5,X0) ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_2676,c_2679]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_32,negated_conjecture,
% 3.63/0.98      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) ),
% 3.63/0.98      inference(cnf_transformation,[],[f89]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2677,plain,
% 3.63/0.98      ( r2_hidden(sK6,k7_relset_1(sK2,sK3,sK5,sK4)) = iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3845,plain,
% 3.63/0.98      ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) = iProver_top ),
% 3.63/0.98      inference(demodulation,[status(thm)],[c_3534,c_2677]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_14,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.63/0.98      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.63/0.98      | ~ v1_relat_1(X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2685,plain,
% 3.63/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.63/0.98      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.63/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_19,plain,
% 3.63/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.63/0.98      | ~ v1_funct_1(X2)
% 3.63/0.98      | ~ v1_relat_1(X2)
% 3.63/0.98      | k1_funct_1(X2,X0) = X1 ),
% 3.63/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_35,negated_conjecture,
% 3.63/0.98      ( v1_funct_1(sK5) ),
% 3.63/0.98      inference(cnf_transformation,[],[f86]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_490,plain,
% 3.63/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 3.63/0.98      | ~ v1_relat_1(X2)
% 3.63/0.98      | k1_funct_1(X2,X0) = X1
% 3.63/0.98      | sK5 != X2 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_19,c_35]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_491,plain,
% 3.63/0.98      ( ~ r2_hidden(k4_tarski(X0,X1),sK5)
% 3.63/0.98      | ~ v1_relat_1(sK5)
% 3.63/0.98      | k1_funct_1(sK5,X0) = X1 ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_490]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2673,plain,
% 3.63/0.98      ( k1_funct_1(sK5,X0) = X1
% 3.63/0.98      | r2_hidden(k4_tarski(X0,X1),sK5) != iProver_top
% 3.63/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_491]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4720,plain,
% 3.63/0.98      ( k1_funct_1(sK5,sK1(X0,X1,sK5)) = X0
% 3.63/0.98      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.63/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_2685,c_2673]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_5145,plain,
% 3.63/0.98      ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6
% 3.63/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_3845,c_4720]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6239,plain,
% 3.63/0.98      ( k1_funct_1(sK5,sK1(sK6,sK4,sK5)) = sK6 ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_6237,c_5145]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_18,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.63/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.63/0.98      | ~ v1_funct_1(X1)
% 3.63/0.98      | ~ v1_relat_1(X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f91]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_475,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 3.63/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 3.63/0.98      | ~ v1_relat_1(X1)
% 3.63/0.98      | sK5 != X1 ),
% 3.63/0.98      inference(resolution_lifted,[status(thm)],[c_18,c_35]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_476,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,k1_relat_1(sK5))
% 3.63/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5)
% 3.63/0.98      | ~ v1_relat_1(sK5) ),
% 3.63/0.98      inference(unflattening,[status(thm)],[c_475]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2674,plain,
% 3.63/0.98      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.63/0.98      | r2_hidden(k4_tarski(X0,k1_funct_1(sK5,X0)),sK5) = iProver_top
% 3.63/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_476]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_16,plain,
% 3.63/0.98      ( r2_hidden(X0,k2_relat_1(X1))
% 3.63/0.98      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.63/0.98      | ~ v1_relat_1(X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2683,plain,
% 3.63/0.98      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 3.63/0.98      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 3.63/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_4103,plain,
% 3.63/0.98      ( r2_hidden(X0,k1_relat_1(sK5)) != iProver_top
% 3.63/0.98      | r2_hidden(k1_funct_1(sK5,X0),k2_relat_1(sK5)) = iProver_top
% 3.63/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_2674,c_2683]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6383,plain,
% 3.63/0.98      ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) != iProver_top
% 3.63/0.98      | r2_hidden(sK6,k2_relat_1(sK5)) = iProver_top
% 3.63/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_6239,c_4103]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7183,plain,
% 3.63/0.98      ( r2_hidden(sK6,k2_relat_1(sK5)) = iProver_top
% 3.63/0.98      | r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) != iProver_top ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_6383,c_6237]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7184,plain,
% 3.63/0.98      ( r2_hidden(sK1(sK6,sK4,sK5),k1_relat_1(sK5)) != iProver_top
% 3.63/0.98      | r2_hidden(sK6,k2_relat_1(sK5)) = iProver_top ),
% 3.63/0.98      inference(renaming,[status(thm)],[c_7183]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7191,plain,
% 3.63/0.98      ( sK3 = k1_xboole_0
% 3.63/0.98      | r2_hidden(sK1(sK6,sK4,sK5),sK2) != iProver_top
% 3.63/0.98      | r2_hidden(sK6,k2_relat_1(sK5)) = iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_3797,c_7184]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7189,plain,
% 3.63/0.98      ( r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
% 3.63/0.98      | r2_hidden(sK6,k2_relat_1(sK5)) = iProver_top
% 3.63/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_2684,c_7184]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7207,plain,
% 3.63/0.98      ( r2_hidden(sK6,k2_relat_1(sK5)) = iProver_top ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_7191,c_3845,c_6237,c_7189]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 3.63/0.98      inference(cnf_transformation,[],[f55]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2693,plain,
% 3.63/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.63/0.98      | r2_hidden(X0,X2) = iProver_top
% 3.63/0.98      | r1_tarski(X1,X2) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7212,plain,
% 3.63/0.98      ( r2_hidden(sK6,X0) = iProver_top
% 3.63/0.98      | r1_tarski(k2_relat_1(sK5),X0) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_7207,c_2693]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7310,plain,
% 3.63/0.98      ( r2_hidden(sK6,sK3) = iProver_top
% 3.63/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_3061,c_7212]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7318,plain,
% 3.63/0.98      ( r2_hidden(sK6,sK3) = iProver_top ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_7310,c_6237]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_21,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.63/0.98      inference(cnf_transformation,[],[f76]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2681,plain,
% 3.63/0.98      ( r2_hidden(X0,X1) != iProver_top
% 3.63/0.98      | r1_tarski(X1,X0) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_7324,plain,
% 3.63/0.98      ( r1_tarski(sK3,sK6) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_7318,c_2681]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_15061,plain,
% 3.63/0.98      ( r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top
% 3.63/0.98      | m1_subset_1(sK1(X0,X1,sK5),sK2) = iProver_top ),
% 3.63/0.98      inference(global_propositional_subsumption,
% 3.63/0.98                [status(thm)],
% 3.63/0.98                [c_4520,c_3147,c_5540,c_6237,c_7324]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_15062,plain,
% 3.63/0.98      ( m1_subset_1(sK1(X0,X1,sK5),sK2) = iProver_top
% 3.63/0.98      | r2_hidden(X0,k9_relat_1(sK5,X1)) != iProver_top ),
% 3.63/0.98      inference(renaming,[status(thm)],[c_15061]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_31,negated_conjecture,
% 3.63/0.98      ( ~ m1_subset_1(X0,sK2)
% 3.63/0.98      | ~ r2_hidden(X0,sK4)
% 3.63/0.98      | k1_funct_1(sK5,X0) != sK6 ),
% 3.63/0.98      inference(cnf_transformation,[],[f90]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_2678,plain,
% 3.63/0.98      ( k1_funct_1(sK5,X0) != sK6
% 3.63/0.98      | m1_subset_1(X0,sK2) != iProver_top
% 3.63/0.98      | r2_hidden(X0,sK4) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_6387,plain,
% 3.63/0.98      ( m1_subset_1(sK1(sK6,sK4,sK5),sK2) != iProver_top
% 3.63/0.98      | r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_6239,c_2678]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_15069,plain,
% 3.63/0.98      ( r2_hidden(sK1(sK6,sK4,sK5),sK4) != iProver_top
% 3.63/0.98      | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top ),
% 3.63/0.98      inference(superposition,[status(thm)],[c_15062,c_6387]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_13,plain,
% 3.63/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.63/0.98      | r2_hidden(sK1(X0,X2,X1),X2)
% 3.63/0.98      | ~ v1_relat_1(X1) ),
% 3.63/0.98      inference(cnf_transformation,[],[f69]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_3272,plain,
% 3.63/0.98      ( r2_hidden(sK1(sK6,X0,X1),X0)
% 3.63/0.98      | ~ r2_hidden(sK6,k9_relat_1(X1,X0))
% 3.63/0.98      | ~ v1_relat_1(X1) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_13]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8256,plain,
% 3.63/0.98      ( r2_hidden(sK1(sK6,sK4,sK5),sK4)
% 3.63/0.98      | ~ r2_hidden(sK6,k9_relat_1(sK5,sK4))
% 3.63/0.98      | ~ v1_relat_1(sK5) ),
% 3.63/0.98      inference(instantiation,[status(thm)],[c_3272]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(c_8257,plain,
% 3.63/0.98      ( r2_hidden(sK1(sK6,sK4,sK5),sK4) = iProver_top
% 3.63/0.98      | r2_hidden(sK6,k9_relat_1(sK5,sK4)) != iProver_top
% 3.63/0.98      | v1_relat_1(sK5) != iProver_top ),
% 3.63/0.98      inference(predicate_to_equality,[status(thm)],[c_8256]) ).
% 3.63/0.98  
% 3.63/0.98  cnf(contradiction,plain,
% 3.63/0.98      ( $false ),
% 3.63/0.98      inference(minisat,[status(thm)],[c_15069,c_8257,c_6237,c_3845]) ).
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.63/0.98  
% 3.63/0.98  ------                               Statistics
% 3.63/0.98  
% 3.63/0.98  ------ General
% 3.63/0.98  
% 3.63/0.98  abstr_ref_over_cycles:                  0
% 3.63/0.98  abstr_ref_under_cycles:                 0
% 3.63/0.98  gc_basic_clause_elim:                   0
% 3.63/0.98  forced_gc_time:                         0
% 3.63/0.98  parsing_time:                           0.005
% 3.63/0.98  unif_index_cands_time:                  0.
% 3.63/0.98  unif_index_add_time:                    0.
% 3.63/0.98  orderings_time:                         0.
% 3.63/0.98  out_proof_time:                         0.01
% 3.63/0.98  total_time:                             0.324
% 3.63/0.98  num_of_symbols:                         55
% 3.63/0.98  num_of_terms:                           11045
% 3.63/0.98  
% 3.63/0.98  ------ Preprocessing
% 3.63/0.98  
% 3.63/0.98  num_of_splits:                          0
% 3.63/0.98  num_of_split_atoms:                     0
% 3.63/0.98  num_of_reused_defs:                     0
% 3.63/0.98  num_eq_ax_congr_red:                    35
% 3.63/0.98  num_of_sem_filtered_clauses:            1
% 3.63/0.98  num_of_subtypes:                        0
% 3.63/0.98  monotx_restored_types:                  0
% 3.63/0.98  sat_num_of_epr_types:                   0
% 3.63/0.98  sat_num_of_non_cyclic_types:            0
% 3.63/0.98  sat_guarded_non_collapsed_types:        0
% 3.63/0.98  num_pure_diseq_elim:                    0
% 3.63/0.98  simp_replaced_by:                       0
% 3.63/0.98  res_preprocessed:                       142
% 3.63/0.98  prep_upred:                             0
% 3.63/0.98  prep_unflattend:                        135
% 3.63/0.98  smt_new_axioms:                         0
% 3.63/0.98  pred_elim_cands:                        4
% 3.63/0.98  pred_elim:                              3
% 3.63/0.98  pred_elim_cl:                           7
% 3.63/0.98  pred_elim_cycles:                       7
% 3.63/0.98  merged_defs:                            8
% 3.63/0.98  merged_defs_ncl:                        0
% 3.63/0.98  bin_hyper_res:                          10
% 3.63/0.98  prep_cycles:                            4
% 3.63/0.98  pred_elim_time:                         0.015
% 3.63/0.98  splitting_time:                         0.
% 3.63/0.98  sem_filter_time:                        0.
% 3.63/0.98  monotx_time:                            0.
% 3.63/0.98  subtype_inf_time:                       0.
% 3.63/0.98  
% 3.63/0.98  ------ Problem properties
% 3.63/0.98  
% 3.63/0.98  clauses:                                27
% 3.63/0.98  conjectures:                            3
% 3.63/0.98  epr:                                    5
% 3.63/0.98  horn:                                   24
% 3.63/0.98  ground:                                 5
% 3.63/0.98  unary:                                  4
% 3.63/0.98  binary:                                 9
% 3.63/0.98  lits:                                   67
% 3.63/0.98  lits_eq:                                11
% 3.63/0.98  fd_pure:                                0
% 3.63/0.98  fd_pseudo:                              0
% 3.63/0.98  fd_cond:                                0
% 3.63/0.98  fd_pseudo_cond:                         1
% 3.63/0.98  ac_symbols:                             0
% 3.63/0.98  
% 3.63/0.98  ------ Propositional Solver
% 3.63/0.98  
% 3.63/0.98  prop_solver_calls:                      31
% 3.63/0.98  prop_fast_solver_calls:                 1511
% 3.63/0.98  smt_solver_calls:                       0
% 3.63/0.98  smt_fast_solver_calls:                  0
% 3.63/0.98  prop_num_of_clauses:                    4962
% 3.63/0.98  prop_preprocess_simplified:             9580
% 3.63/0.98  prop_fo_subsumed:                       64
% 3.63/0.98  prop_solver_time:                       0.
% 3.63/0.98  smt_solver_time:                        0.
% 3.63/0.98  smt_fast_solver_time:                   0.
% 3.63/0.98  prop_fast_solver_time:                  0.
% 3.63/0.98  prop_unsat_core_time:                   0.
% 3.63/0.98  
% 3.63/0.98  ------ QBF
% 3.63/0.98  
% 3.63/0.98  qbf_q_res:                              0
% 3.63/0.98  qbf_num_tautologies:                    0
% 3.63/0.98  qbf_prep_cycles:                        0
% 3.63/0.98  
% 3.63/0.98  ------ BMC1
% 3.63/0.98  
% 3.63/0.98  bmc1_current_bound:                     -1
% 3.63/0.98  bmc1_last_solved_bound:                 -1
% 3.63/0.98  bmc1_unsat_core_size:                   -1
% 3.63/0.98  bmc1_unsat_core_parents_size:           -1
% 3.63/0.98  bmc1_merge_next_fun:                    0
% 3.63/0.98  bmc1_unsat_core_clauses_time:           0.
% 3.63/0.98  
% 3.63/0.98  ------ Instantiation
% 3.63/0.98  
% 3.63/0.98  inst_num_of_clauses:                    1066
% 3.63/0.98  inst_num_in_passive:                    1
% 3.63/0.98  inst_num_in_active:                     745
% 3.63/0.98  inst_num_in_unprocessed:                320
% 3.63/0.98  inst_num_of_loops:                      880
% 3.63/0.98  inst_num_of_learning_restarts:          0
% 3.63/0.98  inst_num_moves_active_passive:          130
% 3.63/0.98  inst_lit_activity:                      0
% 3.63/0.98  inst_lit_activity_moves:                0
% 3.63/0.98  inst_num_tautologies:                   0
% 3.63/0.98  inst_num_prop_implied:                  0
% 3.63/0.98  inst_num_existing_simplified:           0
% 3.63/0.98  inst_num_eq_res_simplified:             0
% 3.63/0.98  inst_num_child_elim:                    0
% 3.63/0.98  inst_num_of_dismatching_blockings:      572
% 3.63/0.98  inst_num_of_non_proper_insts:           1452
% 3.63/0.98  inst_num_of_duplicates:                 0
% 3.63/0.98  inst_inst_num_from_inst_to_res:         0
% 3.63/0.98  inst_dismatching_checking_time:         0.
% 3.63/0.98  
% 3.63/0.98  ------ Resolution
% 3.63/0.98  
% 3.63/0.98  res_num_of_clauses:                     0
% 3.63/0.98  res_num_in_passive:                     0
% 3.63/0.98  res_num_in_active:                      0
% 3.63/0.98  res_num_of_loops:                       146
% 3.63/0.98  res_forward_subset_subsumed:            73
% 3.63/0.98  res_backward_subset_subsumed:           2
% 3.63/0.98  res_forward_subsumed:                   0
% 3.63/0.98  res_backward_subsumed:                  1
% 3.63/0.98  res_forward_subsumption_resolution:     0
% 3.63/0.98  res_backward_subsumption_resolution:    1
% 3.63/0.98  res_clause_to_clause_subsumption:       1793
% 3.63/0.98  res_orphan_elimination:                 0
% 3.63/0.98  res_tautology_del:                      232
% 3.63/0.98  res_num_eq_res_simplified:              0
% 3.63/0.98  res_num_sel_changes:                    0
% 3.63/0.98  res_moves_from_active_to_pass:          0
% 3.63/0.98  
% 3.63/0.98  ------ Superposition
% 3.63/0.98  
% 3.63/0.98  sup_time_total:                         0.
% 3.63/0.98  sup_time_generating:                    0.
% 3.63/0.98  sup_time_sim_full:                      0.
% 3.63/0.98  sup_time_sim_immed:                     0.
% 3.63/0.98  
% 3.63/0.98  sup_num_of_clauses:                     446
% 3.63/0.98  sup_num_in_active:                      170
% 3.63/0.98  sup_num_in_passive:                     276
% 3.63/0.98  sup_num_of_loops:                       174
% 3.63/0.98  sup_fw_superposition:                   238
% 3.63/0.98  sup_bw_superposition:                   395
% 3.63/0.98  sup_immediate_simplified:               78
% 3.63/0.98  sup_given_eliminated:                   0
% 3.63/0.98  comparisons_done:                       0
% 3.63/0.98  comparisons_avoided:                    3
% 3.63/0.98  
% 3.63/0.98  ------ Simplifications
% 3.63/0.98  
% 3.63/0.98  
% 3.63/0.98  sim_fw_subset_subsumed:                 66
% 3.63/0.98  sim_bw_subset_subsumed:                 23
% 3.63/0.98  sim_fw_subsumed:                        10
% 3.63/0.98  sim_bw_subsumed:                        3
% 3.63/0.98  sim_fw_subsumption_res:                 3
% 3.63/0.98  sim_bw_subsumption_res:                 0
% 3.63/0.98  sim_tautology_del:                      13
% 3.63/0.98  sim_eq_tautology_del:                   2
% 3.63/0.98  sim_eq_res_simp:                        0
% 3.63/0.98  sim_fw_demodulated:                     0
% 3.63/0.98  sim_bw_demodulated:                     3
% 3.63/0.98  sim_light_normalised:                   0
% 3.63/0.98  sim_joinable_taut:                      0
% 3.63/0.98  sim_joinable_simp:                      0
% 3.63/0.98  sim_ac_normalised:                      0
% 3.63/0.98  sim_smt_subsumption:                    0
% 3.63/0.98  
%------------------------------------------------------------------------------
