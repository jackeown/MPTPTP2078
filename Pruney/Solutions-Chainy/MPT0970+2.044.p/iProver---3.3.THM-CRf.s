%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:54 EST 2020

% Result     : Theorem 15.28s
% Output     : CNFRefutation 15.28s
% Verified   : 
% Statistics : Number of formulae       :  177 (1112 expanded)
%              Number of clauses        :  102 ( 401 expanded)
%              Number of leaves         :   21 ( 246 expanded)
%              Depth                    :   20
%              Number of atoms          :  568 (4521 expanded)
%              Number of equality atoms :  232 (1336 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f29,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f28])).

fof(f46,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK4,sK5,sK6) != sK5
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK6,X4) = X3
              & r2_hidden(X4,sK4) )
          | ~ r2_hidden(X3,sK5) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f29,f46,f45])).

fof(f79,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f47])).

fof(f13,axiom,(
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

fof(f26,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

fof(f44,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f78,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f80,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f48,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f81,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f34])).

fof(f54,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f82,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f47])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f56,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f42,f41,f40])).

fof(f64,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f85,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f86,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f77,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f62,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f84,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f52])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_32,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1364,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_28,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1367,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2518,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1364,c_1367])).

cnf(c_33,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_36,plain,
    ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_3104,plain,
    ( sK5 = k1_xboole_0
    | k1_relset_1(sK4,sK5,sK6) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2518,c_36])).

cnf(c_3105,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3104])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1374,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_2700,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1364,c_1374])).

cnf(c_3106,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_3105,c_2700])).

cnf(c_31,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1365,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1390,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_3533,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1365,c_1390])).

cnf(c_20,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_1375,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2422,plain,
    ( v5_relat_1(sK6,sK5) = iProver_top ),
    inference(superposition,[status(thm)],[c_1364,c_1375])).

cnf(c_12,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1383,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r1_tarski(k2_relat_1(X0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1391,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_30,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1366,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_2048,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1391,c_1366])).

cnf(c_4,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r1_tarski(X1,X0)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1388,plain,
    ( X0 = X1
    | r1_tarski(X1,X0) != iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2717,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | sK5 = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2048,c_1388])).

cnf(c_3197,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(X0)))) = sK0(sK5,k2_relat_1(X0))
    | k2_relat_1(X0) = sK5
    | v5_relat_1(X0,sK5) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1383,c_2717])).

cnf(c_3395,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6))
    | k2_relat_1(sK6) = sK5
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2422,c_3197])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1373,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_2539,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1364,c_1373])).

cnf(c_29,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_2966,plain,
    ( k2_relat_1(sK6) != sK5 ),
    inference(demodulation,[status(thm)],[c_2539,c_29])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1385,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_1915,plain,
    ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1364,c_1385])).

cnf(c_10,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_7,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_231,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_7])).

cnf(c_232,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_231])).

cnf(c_300,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_10,c_232])).

cnf(c_1360,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_300])).

cnf(c_10372,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_1915,c_1360])).

cnf(c_13,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1382,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_11106,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_10372,c_1382])).

cnf(c_12258,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_3395,c_2966,c_11106])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1378,plain,
    ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_12262,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_12258,c_1378])).

cnf(c_34,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_35,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_51527,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12262,c_35,c_11106])).

cnf(c_51533,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3533,c_51527])).

cnf(c_37,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1697,plain,
    ( v5_relat_1(sK6,sK5)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(instantiation,[status(thm)],[c_20])).

cnf(c_1698,plain,
    ( v5_relat_1(sK6,sK5) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1697])).

cnf(c_1801,plain,
    ( ~ v5_relat_1(sK6,sK5)
    | r1_tarski(k2_relat_1(sK6),sK5)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1802,plain,
    ( v5_relat_1(sK6,sK5) != iProver_top
    | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1801])).

cnf(c_2174,plain,
    ( ~ r1_tarski(X0,sK5)
    | ~ r1_tarski(sK5,X0)
    | X0 = sK5 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_5692,plain,
    ( ~ r1_tarski(k2_relat_1(sK6),sK5)
    | ~ r1_tarski(sK5,k2_relat_1(sK6))
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_2174])).

cnf(c_5693,plain,
    ( k2_relat_1(sK6) = sK5
    | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5692])).

cnf(c_15664,plain,
    ( r2_hidden(sK0(X0,k2_relat_1(sK6)),X0)
    | r1_tarski(X0,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_41364,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5)
    | r1_tarski(sK5,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_15664])).

cnf(c_41370,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) = iProver_top
    | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41364])).

cnf(c_52046,plain,
    ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_51533,c_37,c_1698,c_1802,c_2966,c_5693,c_11106,c_41370])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1376,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_5304,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_3106,c_1376])).

cnf(c_6,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_109,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_3,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1712,plain,
    ( ~ r1_tarski(k2_relset_1(sK4,sK5,sK6),sK5)
    | ~ r1_tarski(sK5,k2_relset_1(sK4,sK5,sK6))
    | k2_relset_1(sK4,sK5,sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_4])).

cnf(c_1745,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1828,plain,
    ( r2_hidden(sK0(sK5,k2_relset_1(sK4,sK5,sK6)),sK5)
    | r1_tarski(sK5,k2_relset_1(sK4,sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_299,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X2)
    | ~ v1_xboole_0(X2) ),
    inference(bin_hyper_res,[status(thm)],[c_9,c_232])).

cnf(c_2635,plain,
    ( ~ r2_hidden(sK0(sK5,k2_relset_1(sK4,sK5,sK6)),sK5)
    | ~ r1_tarski(sK5,X0)
    | ~ v1_xboole_0(X0) ),
    inference(instantiation,[status(thm)],[c_299])).

cnf(c_2637,plain,
    ( ~ r2_hidden(sK0(sK5,k2_relset_1(sK4,sK5,sK6)),sK5)
    | ~ r1_tarski(sK5,k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_2635])).

cnf(c_612,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_2025,plain,
    ( ~ r1_tarski(X0,sK5)
    | r1_tarski(k2_relset_1(sK4,sK5,sK6),sK5)
    | k2_relset_1(sK4,sK5,sK6) != X0 ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_2961,plain,
    ( r1_tarski(k2_relset_1(sK4,sK5,sK6),sK5)
    | ~ r1_tarski(k2_relat_1(sK6),sK5)
    | k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2025])).

cnf(c_11107,plain,
    ( v1_relat_1(sK6) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_11106])).

cnf(c_12549,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK5,X1)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_612])).

cnf(c_12551,plain,
    ( r1_tarski(sK5,k1_xboole_0)
    | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12549])).

cnf(c_22296,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5304,c_35,c_32,c_29,c_109,c_3,c_1697,c_1712,c_1745,c_1801,c_1828,c_2637,c_2961,c_11106,c_11107,c_12551])).

cnf(c_22304,plain,
    ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r2_hidden(sK3(sK6,X0),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_22296,c_1390])).

cnf(c_24044,plain,
    ( k1_funct_1(sK6,sK7(sK3(sK6,X0))) = sK3(sK6,X0)
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_22304,c_1366])).

cnf(c_52062,plain,
    ( k1_funct_1(sK6,sK7(sK3(sK6,sK0(sK5,k2_relat_1(sK6))))) = sK3(sK6,sK0(sK5,k2_relat_1(sK6)))
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_52046,c_24044])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1392,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_52052,plain,
    ( r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_52046,c_1392])).

cnf(c_52207,plain,
    ( r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_52062,c_37,c_1698,c_1802,c_2966,c_5693,c_11106,c_52052])).

cnf(c_52213,plain,
    ( sK5 = k1_xboole_0
    | r1_tarski(sK4,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_3106,c_52207])).

cnf(c_13868,plain,
    ( r1_tarski(sK4,sK4) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_13871,plain,
    ( r1_tarski(sK4,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13868])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_52213,c_13871,c_12551,c_11107,c_2961,c_2637,c_1828,c_1801,c_1745,c_1712,c_1697,c_3,c_109,c_29,c_32])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:46:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 15.28/2.50  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 15.28/2.50  
% 15.28/2.50  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 15.28/2.50  
% 15.28/2.50  ------  iProver source info
% 15.28/2.50  
% 15.28/2.50  git: date: 2020-06-30 10:37:57 +0100
% 15.28/2.50  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 15.28/2.50  git: non_committed_changes: false
% 15.28/2.50  git: last_make_outside_of_git: false
% 15.28/2.50  
% 15.28/2.50  ------ 
% 15.28/2.50  ------ Parsing...
% 15.28/2.50  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 15.28/2.50  
% 15.28/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 15.28/2.50  
% 15.28/2.50  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 15.28/2.50  
% 15.28/2.50  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 15.28/2.50  ------ Proving...
% 15.28/2.50  ------ Problem Properties 
% 15.28/2.50  
% 15.28/2.50  
% 15.28/2.50  clauses                                 34
% 15.28/2.50  conjectures                             6
% 15.28/2.50  EPR                                     8
% 15.28/2.50  Horn                                    27
% 15.28/2.50  unary                                   7
% 15.28/2.50  binary                                  9
% 15.28/2.50  lits                                    92
% 15.28/2.50  lits eq                                 20
% 15.28/2.50  fd_pure                                 0
% 15.28/2.50  fd_pseudo                               0
% 15.28/2.50  fd_cond                                 3
% 15.28/2.50  fd_pseudo_cond                          4
% 15.28/2.50  AC symbols                              0
% 15.28/2.50  
% 15.28/2.50  ------ Input Options Time Limit: Unbounded
% 15.28/2.50  
% 15.28/2.50  
% 15.28/2.50  ------ 
% 15.28/2.50  Current options:
% 15.28/2.50  ------ 
% 15.28/2.50  
% 15.28/2.50  
% 15.28/2.50  
% 15.28/2.50  
% 15.28/2.50  ------ Proving...
% 15.28/2.50  
% 15.28/2.50  
% 15.28/2.50  % SZS status Theorem for theBenchmark.p
% 15.28/2.50  
% 15.28/2.50  % SZS output start CNFRefutation for theBenchmark.p
% 15.28/2.50  
% 15.28/2.50  fof(f14,conjecture,(
% 15.28/2.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f15,negated_conjecture,(
% 15.28/2.50    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 15.28/2.50    inference(negated_conjecture,[],[f14])).
% 15.28/2.50  
% 15.28/2.50  fof(f28,plain,(
% 15.28/2.50    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 15.28/2.50    inference(ennf_transformation,[],[f15])).
% 15.28/2.50  
% 15.28/2.50  fof(f29,plain,(
% 15.28/2.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 15.28/2.50    inference(flattening,[],[f28])).
% 15.28/2.50  
% 15.28/2.50  fof(f46,plain,(
% 15.28/2.50    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 15.28/2.50    introduced(choice_axiom,[])).
% 15.28/2.50  
% 15.28/2.50  fof(f45,plain,(
% 15.28/2.50    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 15.28/2.50    introduced(choice_axiom,[])).
% 15.28/2.50  
% 15.28/2.50  fof(f47,plain,(
% 15.28/2.50    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 15.28/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f29,f46,f45])).
% 15.28/2.50  
% 15.28/2.50  fof(f79,plain,(
% 15.28/2.50    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 15.28/2.50    inference(cnf_transformation,[],[f47])).
% 15.28/2.50  
% 15.28/2.50  fof(f13,axiom,(
% 15.28/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f26,plain,(
% 15.28/2.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.28/2.50    inference(ennf_transformation,[],[f13])).
% 15.28/2.50  
% 15.28/2.50  fof(f27,plain,(
% 15.28/2.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.28/2.50    inference(flattening,[],[f26])).
% 15.28/2.50  
% 15.28/2.50  fof(f44,plain,(
% 15.28/2.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.28/2.50    inference(nnf_transformation,[],[f27])).
% 15.28/2.50  
% 15.28/2.50  fof(f71,plain,(
% 15.28/2.50    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.28/2.50    inference(cnf_transformation,[],[f44])).
% 15.28/2.50  
% 15.28/2.50  fof(f78,plain,(
% 15.28/2.50    v1_funct_2(sK6,sK4,sK5)),
% 15.28/2.50    inference(cnf_transformation,[],[f47])).
% 15.28/2.50  
% 15.28/2.50  fof(f11,axiom,(
% 15.28/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f24,plain,(
% 15.28/2.50    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.28/2.50    inference(ennf_transformation,[],[f11])).
% 15.28/2.50  
% 15.28/2.50  fof(f69,plain,(
% 15.28/2.50    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.28/2.50    inference(cnf_transformation,[],[f24])).
% 15.28/2.50  
% 15.28/2.50  fof(f80,plain,(
% 15.28/2.50    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f47])).
% 15.28/2.50  
% 15.28/2.50  fof(f1,axiom,(
% 15.28/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f17,plain,(
% 15.28/2.50    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 15.28/2.50    inference(ennf_transformation,[],[f1])).
% 15.28/2.50  
% 15.28/2.50  fof(f30,plain,(
% 15.28/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 15.28/2.50    inference(nnf_transformation,[],[f17])).
% 15.28/2.50  
% 15.28/2.50  fof(f31,plain,(
% 15.28/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.28/2.50    inference(rectify,[],[f30])).
% 15.28/2.50  
% 15.28/2.50  fof(f32,plain,(
% 15.28/2.50    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 15.28/2.50    introduced(choice_axiom,[])).
% 15.28/2.50  
% 15.28/2.50  fof(f33,plain,(
% 15.28/2.50    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 15.28/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 15.28/2.50  
% 15.28/2.50  fof(f48,plain,(
% 15.28/2.50    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f33])).
% 15.28/2.50  
% 15.28/2.50  fof(f10,axiom,(
% 15.28/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f16,plain,(
% 15.28/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 15.28/2.50    inference(pure_predicate_removal,[],[f10])).
% 15.28/2.50  
% 15.28/2.50  fof(f23,plain,(
% 15.28/2.50    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.28/2.50    inference(ennf_transformation,[],[f16])).
% 15.28/2.50  
% 15.28/2.50  fof(f68,plain,(
% 15.28/2.50    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.28/2.50    inference(cnf_transformation,[],[f23])).
% 15.28/2.50  
% 15.28/2.50  fof(f7,axiom,(
% 15.28/2.50    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f20,plain,(
% 15.28/2.50    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 15.28/2.50    inference(ennf_transformation,[],[f7])).
% 15.28/2.50  
% 15.28/2.50  fof(f37,plain,(
% 15.28/2.50    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 15.28/2.50    inference(nnf_transformation,[],[f20])).
% 15.28/2.50  
% 15.28/2.50  fof(f59,plain,(
% 15.28/2.50    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f37])).
% 15.28/2.50  
% 15.28/2.50  fof(f49,plain,(
% 15.28/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f33])).
% 15.28/2.50  
% 15.28/2.50  fof(f81,plain,(
% 15.28/2.50    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f47])).
% 15.28/2.50  
% 15.28/2.50  fof(f3,axiom,(
% 15.28/2.50    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f34,plain,(
% 15.28/2.50    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.28/2.50    inference(nnf_transformation,[],[f3])).
% 15.28/2.50  
% 15.28/2.50  fof(f35,plain,(
% 15.28/2.50    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 15.28/2.50    inference(flattening,[],[f34])).
% 15.28/2.50  
% 15.28/2.50  fof(f54,plain,(
% 15.28/2.50    ( ! [X0,X1] : (X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f35])).
% 15.28/2.50  
% 15.28/2.50  fof(f12,axiom,(
% 15.28/2.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f25,plain,(
% 15.28/2.50    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 15.28/2.50    inference(ennf_transformation,[],[f12])).
% 15.28/2.50  
% 15.28/2.50  fof(f70,plain,(
% 15.28/2.50    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 15.28/2.50    inference(cnf_transformation,[],[f25])).
% 15.28/2.50  
% 15.28/2.50  fof(f82,plain,(
% 15.28/2.50    k2_relset_1(sK4,sK5,sK6) != sK5),
% 15.28/2.50    inference(cnf_transformation,[],[f47])).
% 15.28/2.50  
% 15.28/2.50  fof(f4,axiom,(
% 15.28/2.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f36,plain,(
% 15.28/2.50    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 15.28/2.50    inference(nnf_transformation,[],[f4])).
% 15.28/2.50  
% 15.28/2.50  fof(f55,plain,(
% 15.28/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 15.28/2.50    inference(cnf_transformation,[],[f36])).
% 15.28/2.50  
% 15.28/2.50  fof(f6,axiom,(
% 15.28/2.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f19,plain,(
% 15.28/2.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 15.28/2.50    inference(ennf_transformation,[],[f6])).
% 15.28/2.50  
% 15.28/2.50  fof(f58,plain,(
% 15.28/2.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f19])).
% 15.28/2.50  
% 15.28/2.50  fof(f56,plain,(
% 15.28/2.50    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f36])).
% 15.28/2.50  
% 15.28/2.50  fof(f8,axiom,(
% 15.28/2.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f61,plain,(
% 15.28/2.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 15.28/2.50    inference(cnf_transformation,[],[f8])).
% 15.28/2.50  
% 15.28/2.50  fof(f9,axiom,(
% 15.28/2.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f21,plain,(
% 15.28/2.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 15.28/2.50    inference(ennf_transformation,[],[f9])).
% 15.28/2.50  
% 15.28/2.50  fof(f22,plain,(
% 15.28/2.50    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.28/2.50    inference(flattening,[],[f21])).
% 15.28/2.50  
% 15.28/2.50  fof(f38,plain,(
% 15.28/2.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.28/2.50    inference(nnf_transformation,[],[f22])).
% 15.28/2.50  
% 15.28/2.50  fof(f39,plain,(
% 15.28/2.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.28/2.50    inference(rectify,[],[f38])).
% 15.28/2.50  
% 15.28/2.50  fof(f42,plain,(
% 15.28/2.50    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 15.28/2.50    introduced(choice_axiom,[])).
% 15.28/2.50  
% 15.28/2.50  fof(f41,plain,(
% 15.28/2.50    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 15.28/2.50    introduced(choice_axiom,[])).
% 15.28/2.50  
% 15.28/2.50  fof(f40,plain,(
% 15.28/2.50    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 15.28/2.50    introduced(choice_axiom,[])).
% 15.28/2.50  
% 15.28/2.50  fof(f43,plain,(
% 15.28/2.50    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 15.28/2.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f39,f42,f41,f40])).
% 15.28/2.50  
% 15.28/2.50  fof(f64,plain,(
% 15.28/2.50    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f43])).
% 15.28/2.50  
% 15.28/2.50  fof(f85,plain,(
% 15.28/2.50    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.28/2.50    inference(equality_resolution,[],[f64])).
% 15.28/2.50  
% 15.28/2.50  fof(f86,plain,(
% 15.28/2.50    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.28/2.50    inference(equality_resolution,[],[f85])).
% 15.28/2.50  
% 15.28/2.50  fof(f77,plain,(
% 15.28/2.50    v1_funct_1(sK6)),
% 15.28/2.50    inference(cnf_transformation,[],[f47])).
% 15.28/2.50  
% 15.28/2.50  fof(f62,plain,(
% 15.28/2.50    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f43])).
% 15.28/2.50  
% 15.28/2.50  fof(f88,plain,(
% 15.28/2.50    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 15.28/2.50    inference(equality_resolution,[],[f62])).
% 15.28/2.50  
% 15.28/2.50  fof(f52,plain,(
% 15.28/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | X0 != X1) )),
% 15.28/2.50    inference(cnf_transformation,[],[f35])).
% 15.28/2.50  
% 15.28/2.50  fof(f84,plain,(
% 15.28/2.50    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 15.28/2.50    inference(equality_resolution,[],[f52])).
% 15.28/2.50  
% 15.28/2.50  fof(f2,axiom,(
% 15.28/2.50    v1_xboole_0(k1_xboole_0)),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f51,plain,(
% 15.28/2.50    v1_xboole_0(k1_xboole_0)),
% 15.28/2.50    inference(cnf_transformation,[],[f2])).
% 15.28/2.50  
% 15.28/2.50  fof(f5,axiom,(
% 15.28/2.50    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 15.28/2.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 15.28/2.50  
% 15.28/2.50  fof(f18,plain,(
% 15.28/2.50    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 15.28/2.50    inference(ennf_transformation,[],[f5])).
% 15.28/2.50  
% 15.28/2.50  fof(f57,plain,(
% 15.28/2.50    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f18])).
% 15.28/2.50  
% 15.28/2.50  fof(f50,plain,(
% 15.28/2.50    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 15.28/2.50    inference(cnf_transformation,[],[f33])).
% 15.28/2.50  
% 15.28/2.50  cnf(c_32,negated_conjecture,
% 15.28/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 15.28/2.50      inference(cnf_transformation,[],[f79]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1364,plain,
% 15.28/2.50      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_28,plain,
% 15.28/2.50      ( ~ v1_funct_2(X0,X1,X2)
% 15.28/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.50      | k1_relset_1(X1,X2,X0) = X1
% 15.28/2.50      | k1_xboole_0 = X2 ),
% 15.28/2.50      inference(cnf_transformation,[],[f71]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1367,plain,
% 15.28/2.50      ( k1_relset_1(X0,X1,X2) = X0
% 15.28/2.50      | k1_xboole_0 = X1
% 15.28/2.50      | v1_funct_2(X2,X0,X1) != iProver_top
% 15.28/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2518,plain,
% 15.28/2.50      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 15.28/2.50      | sK5 = k1_xboole_0
% 15.28/2.50      | v1_funct_2(sK6,sK4,sK5) != iProver_top ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_1364,c_1367]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_33,negated_conjecture,
% 15.28/2.50      ( v1_funct_2(sK6,sK4,sK5) ),
% 15.28/2.50      inference(cnf_transformation,[],[f78]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_36,plain,
% 15.28/2.50      ( v1_funct_2(sK6,sK4,sK5) = iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_3104,plain,
% 15.28/2.50      ( sK5 = k1_xboole_0 | k1_relset_1(sK4,sK5,sK6) = sK4 ),
% 15.28/2.50      inference(global_propositional_subsumption,
% 15.28/2.50                [status(thm)],
% 15.28/2.50                [c_2518,c_36]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_3105,plain,
% 15.28/2.50      ( k1_relset_1(sK4,sK5,sK6) = sK4 | sK5 = k1_xboole_0 ),
% 15.28/2.50      inference(renaming,[status(thm)],[c_3104]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_21,plain,
% 15.28/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.50      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 15.28/2.50      inference(cnf_transformation,[],[f69]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1374,plain,
% 15.28/2.50      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 15.28/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2700,plain,
% 15.28/2.50      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_1364,c_1374]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_3106,plain,
% 15.28/2.50      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 15.28/2.50      inference(demodulation,[status(thm)],[c_3105,c_2700]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_31,negated_conjecture,
% 15.28/2.50      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 15.28/2.50      inference(cnf_transformation,[],[f80]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1365,plain,
% 15.28/2.50      ( r2_hidden(X0,sK5) != iProver_top
% 15.28/2.50      | r2_hidden(sK7(X0),sK4) = iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2,plain,
% 15.28/2.50      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 15.28/2.50      inference(cnf_transformation,[],[f48]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1390,plain,
% 15.28/2.50      ( r2_hidden(X0,X1) != iProver_top
% 15.28/2.50      | r2_hidden(X0,X2) = iProver_top
% 15.28/2.50      | r1_tarski(X1,X2) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_3533,plain,
% 15.28/2.50      ( r2_hidden(X0,sK5) != iProver_top
% 15.28/2.50      | r2_hidden(sK7(X0),X1) = iProver_top
% 15.28/2.50      | r1_tarski(sK4,X1) != iProver_top ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_1365,c_1390]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_20,plain,
% 15.28/2.50      ( v5_relat_1(X0,X1)
% 15.28/2.50      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 15.28/2.50      inference(cnf_transformation,[],[f68]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1375,plain,
% 15.28/2.50      ( v5_relat_1(X0,X1) = iProver_top
% 15.28/2.50      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2422,plain,
% 15.28/2.50      ( v5_relat_1(sK6,sK5) = iProver_top ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_1364,c_1375]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_12,plain,
% 15.28/2.50      ( ~ v5_relat_1(X0,X1)
% 15.28/2.50      | r1_tarski(k2_relat_1(X0),X1)
% 15.28/2.50      | ~ v1_relat_1(X0) ),
% 15.28/2.50      inference(cnf_transformation,[],[f59]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1383,plain,
% 15.28/2.50      ( v5_relat_1(X0,X1) != iProver_top
% 15.28/2.50      | r1_tarski(k2_relat_1(X0),X1) = iProver_top
% 15.28/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1,plain,
% 15.28/2.50      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 15.28/2.50      inference(cnf_transformation,[],[f49]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1391,plain,
% 15.28/2.50      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 15.28/2.50      | r1_tarski(X0,X1) = iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_30,negated_conjecture,
% 15.28/2.50      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 15.28/2.50      inference(cnf_transformation,[],[f81]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1366,plain,
% 15.28/2.50      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2048,plain,
% 15.28/2.50      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 15.28/2.50      | r1_tarski(sK5,X0) = iProver_top ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_1391,c_1366]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_4,plain,
% 15.28/2.50      ( ~ r1_tarski(X0,X1) | ~ r1_tarski(X1,X0) | X1 = X0 ),
% 15.28/2.50      inference(cnf_transformation,[],[f54]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1388,plain,
% 15.28/2.50      ( X0 = X1
% 15.28/2.50      | r1_tarski(X1,X0) != iProver_top
% 15.28/2.50      | r1_tarski(X0,X1) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2717,plain,
% 15.28/2.50      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 15.28/2.50      | sK5 = X0
% 15.28/2.50      | r1_tarski(X0,sK5) != iProver_top ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_2048,c_1388]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_3197,plain,
% 15.28/2.50      ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(X0)))) = sK0(sK5,k2_relat_1(X0))
% 15.28/2.50      | k2_relat_1(X0) = sK5
% 15.28/2.50      | v5_relat_1(X0,sK5) != iProver_top
% 15.28/2.50      | v1_relat_1(X0) != iProver_top ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_1383,c_2717]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_3395,plain,
% 15.28/2.50      ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6))
% 15.28/2.50      | k2_relat_1(sK6) = sK5
% 15.28/2.50      | v1_relat_1(sK6) != iProver_top ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_2422,c_3197]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_22,plain,
% 15.28/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 15.28/2.50      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 15.28/2.50      inference(cnf_transformation,[],[f70]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1373,plain,
% 15.28/2.50      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 15.28/2.50      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 15.28/2.50      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2539,plain,
% 15.28/2.50      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 15.28/2.50      inference(superposition,[status(thm)],[c_1364,c_1373]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_29,negated_conjecture,
% 15.28/2.50      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 15.28/2.50      inference(cnf_transformation,[],[f82]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_2966,plain,
% 15.28/2.50      ( k2_relat_1(sK6) != sK5 ),
% 15.28/2.50      inference(demodulation,[status(thm)],[c_2539,c_29]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_8,plain,
% 15.28/2.50      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 15.28/2.50      inference(cnf_transformation,[],[f55]) ).
% 15.28/2.50  
% 15.28/2.50  cnf(c_1385,plain,
% 15.28/2.50      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 15.28/2.51      | r1_tarski(X0,X1) = iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1915,plain,
% 15.28/2.51      ( r1_tarski(sK6,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_1364,c_1385]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_10,plain,
% 15.28/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.28/2.51      | ~ v1_relat_1(X1)
% 15.28/2.51      | v1_relat_1(X0) ),
% 15.28/2.51      inference(cnf_transformation,[],[f58]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_7,plain,
% 15.28/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.28/2.51      inference(cnf_transformation,[],[f56]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_231,plain,
% 15.28/2.51      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 15.28/2.51      inference(prop_impl,[status(thm)],[c_7]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_232,plain,
% 15.28/2.51      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 15.28/2.51      inference(renaming,[status(thm)],[c_231]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_300,plain,
% 15.28/2.51      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 15.28/2.51      inference(bin_hyper_res,[status(thm)],[c_10,c_232]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1360,plain,
% 15.28/2.51      ( r1_tarski(X0,X1) != iProver_top
% 15.28/2.51      | v1_relat_1(X1) != iProver_top
% 15.28/2.51      | v1_relat_1(X0) = iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_300]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_10372,plain,
% 15.28/2.51      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 15.28/2.51      | v1_relat_1(sK6) = iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_1915,c_1360]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_13,plain,
% 15.28/2.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 15.28/2.51      inference(cnf_transformation,[],[f61]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1382,plain,
% 15.28/2.51      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_11106,plain,
% 15.28/2.51      ( v1_relat_1(sK6) = iProver_top ),
% 15.28/2.51      inference(forward_subsumption_resolution,
% 15.28/2.51                [status(thm)],
% 15.28/2.51                [c_10372,c_1382]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_12258,plain,
% 15.28/2.51      ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6)) ),
% 15.28/2.51      inference(global_propositional_subsumption,
% 15.28/2.51                [status(thm)],
% 15.28/2.51                [c_3395,c_2966,c_11106]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_17,plain,
% 15.28/2.51      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 15.28/2.51      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 15.28/2.51      | ~ v1_funct_1(X1)
% 15.28/2.51      | ~ v1_relat_1(X1) ),
% 15.28/2.51      inference(cnf_transformation,[],[f86]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1378,plain,
% 15.28/2.51      ( r2_hidden(X0,k1_relat_1(X1)) != iProver_top
% 15.28/2.51      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1)) = iProver_top
% 15.28/2.51      | v1_funct_1(X1) != iProver_top
% 15.28/2.51      | v1_relat_1(X1) != iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_12262,plain,
% 15.28/2.51      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 15.28/2.51      | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top
% 15.28/2.51      | v1_funct_1(sK6) != iProver_top
% 15.28/2.51      | v1_relat_1(sK6) != iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_12258,c_1378]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_34,negated_conjecture,
% 15.28/2.51      ( v1_funct_1(sK6) ),
% 15.28/2.51      inference(cnf_transformation,[],[f77]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_35,plain,
% 15.28/2.51      ( v1_funct_1(sK6) = iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_51527,plain,
% 15.28/2.51      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 15.28/2.51      | r2_hidden(sK7(sK0(sK5,k2_relat_1(sK6))),k1_relat_1(sK6)) != iProver_top ),
% 15.28/2.51      inference(global_propositional_subsumption,
% 15.28/2.51                [status(thm)],
% 15.28/2.51                [c_12262,c_35,c_11106]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_51533,plain,
% 15.28/2.51      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 15.28/2.51      | r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) != iProver_top
% 15.28/2.51      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_3533,c_51527]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_37,plain,
% 15.28/2.51      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1697,plain,
% 15.28/2.51      ( v5_relat_1(sK6,sK5)
% 15.28/2.51      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_20]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1698,plain,
% 15.28/2.51      ( v5_relat_1(sK6,sK5) = iProver_top
% 15.28/2.51      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_1697]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1801,plain,
% 15.28/2.51      ( ~ v5_relat_1(sK6,sK5)
% 15.28/2.51      | r1_tarski(k2_relat_1(sK6),sK5)
% 15.28/2.51      | ~ v1_relat_1(sK6) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_12]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1802,plain,
% 15.28/2.51      ( v5_relat_1(sK6,sK5) != iProver_top
% 15.28/2.51      | r1_tarski(k2_relat_1(sK6),sK5) = iProver_top
% 15.28/2.51      | v1_relat_1(sK6) != iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_1801]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_2174,plain,
% 15.28/2.51      ( ~ r1_tarski(X0,sK5) | ~ r1_tarski(sK5,X0) | X0 = sK5 ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_4]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_5692,plain,
% 15.28/2.51      ( ~ r1_tarski(k2_relat_1(sK6),sK5)
% 15.28/2.51      | ~ r1_tarski(sK5,k2_relat_1(sK6))
% 15.28/2.51      | k2_relat_1(sK6) = sK5 ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_2174]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_5693,plain,
% 15.28/2.51      ( k2_relat_1(sK6) = sK5
% 15.28/2.51      | r1_tarski(k2_relat_1(sK6),sK5) != iProver_top
% 15.28/2.51      | r1_tarski(sK5,k2_relat_1(sK6)) != iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_5692]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_15664,plain,
% 15.28/2.51      ( r2_hidden(sK0(X0,k2_relat_1(sK6)),X0)
% 15.28/2.51      | r1_tarski(X0,k2_relat_1(sK6)) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_1]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_41364,plain,
% 15.28/2.51      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5)
% 15.28/2.51      | r1_tarski(sK5,k2_relat_1(sK6)) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_15664]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_41370,plain,
% 15.28/2.51      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),sK5) = iProver_top
% 15.28/2.51      | r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_41364]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_52046,plain,
% 15.28/2.51      ( r2_hidden(sK0(sK5,k2_relat_1(sK6)),k2_relat_1(sK6)) = iProver_top
% 15.28/2.51      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 15.28/2.51      inference(global_propositional_subsumption,
% 15.28/2.51                [status(thm)],
% 15.28/2.51                [c_51533,c_37,c_1698,c_1802,c_2966,c_5693,c_11106,
% 15.28/2.51                 c_41370]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_19,plain,
% 15.28/2.51      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 15.28/2.51      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 15.28/2.51      | ~ v1_funct_1(X1)
% 15.28/2.51      | ~ v1_relat_1(X1) ),
% 15.28/2.51      inference(cnf_transformation,[],[f88]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1376,plain,
% 15.28/2.51      ( r2_hidden(X0,k2_relat_1(X1)) != iProver_top
% 15.28/2.51      | r2_hidden(sK3(X1,X0),k1_relat_1(X1)) = iProver_top
% 15.28/2.51      | v1_funct_1(X1) != iProver_top
% 15.28/2.51      | v1_relat_1(X1) != iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_5304,plain,
% 15.28/2.51      ( sK5 = k1_xboole_0
% 15.28/2.51      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 15.28/2.51      | r2_hidden(sK3(sK6,X0),sK4) = iProver_top
% 15.28/2.51      | v1_funct_1(sK6) != iProver_top
% 15.28/2.51      | v1_relat_1(sK6) != iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_3106,c_1376]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_6,plain,
% 15.28/2.51      ( r1_tarski(X0,X0) ),
% 15.28/2.51      inference(cnf_transformation,[],[f84]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_109,plain,
% 15.28/2.51      ( r1_tarski(k1_xboole_0,k1_xboole_0) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_6]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_3,plain,
% 15.28/2.51      ( v1_xboole_0(k1_xboole_0) ),
% 15.28/2.51      inference(cnf_transformation,[],[f51]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1712,plain,
% 15.28/2.51      ( ~ r1_tarski(k2_relset_1(sK4,sK5,sK6),sK5)
% 15.28/2.51      | ~ r1_tarski(sK5,k2_relset_1(sK4,sK5,sK6))
% 15.28/2.51      | k2_relset_1(sK4,sK5,sK6) = sK5 ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_4]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1745,plain,
% 15.28/2.51      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 15.28/2.51      | k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_22]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1828,plain,
% 15.28/2.51      ( r2_hidden(sK0(sK5,k2_relset_1(sK4,sK5,sK6)),sK5)
% 15.28/2.51      | r1_tarski(sK5,k2_relset_1(sK4,sK5,sK6)) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_1]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_9,plain,
% 15.28/2.51      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 15.28/2.51      | ~ r2_hidden(X2,X0)
% 15.28/2.51      | ~ v1_xboole_0(X1) ),
% 15.28/2.51      inference(cnf_transformation,[],[f57]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_299,plain,
% 15.28/2.51      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X2) | ~ v1_xboole_0(X2) ),
% 15.28/2.51      inference(bin_hyper_res,[status(thm)],[c_9,c_232]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_2635,plain,
% 15.28/2.51      ( ~ r2_hidden(sK0(sK5,k2_relset_1(sK4,sK5,sK6)),sK5)
% 15.28/2.51      | ~ r1_tarski(sK5,X0)
% 15.28/2.51      | ~ v1_xboole_0(X0) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_299]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_2637,plain,
% 15.28/2.51      ( ~ r2_hidden(sK0(sK5,k2_relset_1(sK4,sK5,sK6)),sK5)
% 15.28/2.51      | ~ r1_tarski(sK5,k1_xboole_0)
% 15.28/2.51      | ~ v1_xboole_0(k1_xboole_0) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_2635]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_612,plain,
% 15.28/2.51      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 15.28/2.51      theory(equality) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_2025,plain,
% 15.28/2.51      ( ~ r1_tarski(X0,sK5)
% 15.28/2.51      | r1_tarski(k2_relset_1(sK4,sK5,sK6),sK5)
% 15.28/2.51      | k2_relset_1(sK4,sK5,sK6) != X0 ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_612]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_2961,plain,
% 15.28/2.51      ( r1_tarski(k2_relset_1(sK4,sK5,sK6),sK5)
% 15.28/2.51      | ~ r1_tarski(k2_relat_1(sK6),sK5)
% 15.28/2.51      | k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_2025]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_11107,plain,
% 15.28/2.51      ( v1_relat_1(sK6) ),
% 15.28/2.51      inference(predicate_to_equality_rev,[status(thm)],[c_11106]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_12549,plain,
% 15.28/2.51      ( ~ r1_tarski(X0,X1) | r1_tarski(sK5,X1) | sK5 != X0 ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_612]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_12551,plain,
% 15.28/2.51      ( r1_tarski(sK5,k1_xboole_0)
% 15.28/2.51      | ~ r1_tarski(k1_xboole_0,k1_xboole_0)
% 15.28/2.51      | sK5 != k1_xboole_0 ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_12549]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_22296,plain,
% 15.28/2.51      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 15.28/2.51      | r2_hidden(sK3(sK6,X0),sK4) = iProver_top ),
% 15.28/2.51      inference(global_propositional_subsumption,
% 15.28/2.51                [status(thm)],
% 15.28/2.51                [c_5304,c_35,c_32,c_29,c_109,c_3,c_1697,c_1712,c_1745,
% 15.28/2.51                 c_1801,c_1828,c_2637,c_2961,c_11106,c_11107,c_12551]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_22304,plain,
% 15.28/2.51      ( r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 15.28/2.51      | r2_hidden(sK3(sK6,X0),X1) = iProver_top
% 15.28/2.51      | r1_tarski(sK4,X1) != iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_22296,c_1390]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_24044,plain,
% 15.28/2.51      ( k1_funct_1(sK6,sK7(sK3(sK6,X0))) = sK3(sK6,X0)
% 15.28/2.51      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 15.28/2.51      | r1_tarski(sK4,sK5) != iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_22304,c_1366]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_52062,plain,
% 15.28/2.51      ( k1_funct_1(sK6,sK7(sK3(sK6,sK0(sK5,k2_relat_1(sK6))))) = sK3(sK6,sK0(sK5,k2_relat_1(sK6)))
% 15.28/2.51      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top
% 15.28/2.51      | r1_tarski(sK4,sK5) != iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_52046,c_24044]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_0,plain,
% 15.28/2.51      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 15.28/2.51      inference(cnf_transformation,[],[f50]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_1392,plain,
% 15.28/2.51      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 15.28/2.51      | r1_tarski(X0,X1) = iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_52052,plain,
% 15.28/2.51      ( r1_tarski(sK5,k2_relat_1(sK6)) = iProver_top
% 15.28/2.51      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_52046,c_1392]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_52207,plain,
% 15.28/2.51      ( r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 15.28/2.51      inference(global_propositional_subsumption,
% 15.28/2.51                [status(thm)],
% 15.28/2.51                [c_52062,c_37,c_1698,c_1802,c_2966,c_5693,c_11106,
% 15.28/2.51                 c_52052]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_52213,plain,
% 15.28/2.51      ( sK5 = k1_xboole_0 | r1_tarski(sK4,sK4) != iProver_top ),
% 15.28/2.51      inference(superposition,[status(thm)],[c_3106,c_52207]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_13868,plain,
% 15.28/2.51      ( r1_tarski(sK4,sK4) ),
% 15.28/2.51      inference(instantiation,[status(thm)],[c_6]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(c_13871,plain,
% 15.28/2.51      ( r1_tarski(sK4,sK4) = iProver_top ),
% 15.28/2.51      inference(predicate_to_equality,[status(thm)],[c_13868]) ).
% 15.28/2.51  
% 15.28/2.51  cnf(contradiction,plain,
% 15.28/2.51      ( $false ),
% 15.28/2.51      inference(minisat,
% 15.28/2.51                [status(thm)],
% 15.28/2.51                [c_52213,c_13871,c_12551,c_11107,c_2961,c_2637,c_1828,
% 15.28/2.51                 c_1801,c_1745,c_1712,c_1697,c_3,c_109,c_29,c_32]) ).
% 15.28/2.51  
% 15.28/2.51  
% 15.28/2.51  % SZS output end CNFRefutation for theBenchmark.p
% 15.28/2.51  
% 15.28/2.51  ------                               Statistics
% 15.28/2.51  
% 15.28/2.51  ------ Selected
% 15.28/2.51  
% 15.28/2.51  total_time:                             1.725
% 15.28/2.51  
%------------------------------------------------------------------------------
