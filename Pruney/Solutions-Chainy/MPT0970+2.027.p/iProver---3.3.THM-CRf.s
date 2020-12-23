%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:50 EST 2020

% Result     : Theorem 43.37s
% Output     : CNFRefutation 43.37s
% Verified   : 
% Statistics : Number of formulae       :  218 (1044 expanded)
%              Number of clauses        :  155 ( 388 expanded)
%              Number of leaves         :   24 ( 278 expanded)
%              Depth                    :   25
%              Number of atoms          :  791 (5194 expanded)
%              Number of equality atoms :  458 (1822 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f9,conjecture,(
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

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f20,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

fof(f39,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK9(X3)) = X3
        & r2_hidden(sK9(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,
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
   => ( k2_relset_1(sK6,sK7,sK8) != sK7
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK8,X4) = X3
              & r2_hidden(X4,sK6) )
          | ~ r2_hidden(X3,sK7) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_2(sK8,sK6,sK7)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( k2_relset_1(sK6,sK7,sK8) != sK7
    & ! [X3] :
        ( ( k1_funct_1(sK8,sK9(X3)) = X3
          & r2_hidden(sK9(X3),sK6) )
        | ~ r2_hidden(X3,sK7) )
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_2(sK8,sK6,sK7)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f21,f39,f38])).

fof(f68,plain,(
    v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f8,axiom,(
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

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f69,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f40])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ! [X3] :
            ~ ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( ! [X3] :
            ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
            | ~ r2_hidden(X3,X1) )
      <=> k2_relset_1(X0,X1,X2) = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X3] :
              ( ! [X4] : ~ r2_hidden(k4_tarski(X4,X3),X2)
              & r2_hidden(X3,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ? [X5] :
              ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
              & r2_hidden(X5,X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(rectify,[],[f32])).

fof(f35,plain,(
    ! [X2,X1] :
      ( ? [X5] :
          ( ! [X6] : ~ r2_hidden(k4_tarski(X6,X5),X2)
          & r2_hidden(X5,X1) )
     => ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2)
        & r2_hidden(sK5(X1,X2),X1) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X3,X2] :
      ( ? [X4] : r2_hidden(k4_tarski(X4,X3),X2)
     => r2_hidden(k4_tarski(sK4(X2,X3),X3),X2) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( ( ! [X3] :
              ( r2_hidden(k4_tarski(sK4(X2,X3),X3),X2)
              | ~ r2_hidden(X3,X1) )
          | k2_relset_1(X0,X1,X2) != X1 )
        & ( k2_relset_1(X0,X1,X2) = X1
          | ( ! [X6] : ~ r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2)
            & r2_hidden(sK5(X1,X2),X1) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f35,f34])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | r2_hidden(sK5(X1,X2),X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f72,plain,(
    k2_relset_1(sK6,sK7,sK8) != sK7 ),
    inference(cnf_transformation,[],[f40])).

fof(f71,plain,(
    ! [X3] :
      ( k1_funct_1(sK8,sK9(X3)) = X3
      | ~ r2_hidden(X3,sK7) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f70,plain,(
    ! [X3] :
      ( r2_hidden(sK9(X3),sK6)
      | ~ r2_hidden(X3,sK7) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( k9_relat_1(X0,X1) = X2
        <=> ! [X3] :
              ( r2_hidden(X3,X2)
            <=> ? [X4] :
                  ( k1_funct_1(X0,X4) = X3
                  & r2_hidden(X4,X1)
                  & r2_hidden(X4,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f12])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X3] :
                ( ( r2_hidden(X3,X2)
                  | ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) ) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X3
                      & r2_hidden(X4,X1)
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ? [X3] :
                ( ( ! [X4] :
                      ( k1_funct_1(X0,X4) != X3
                      | ~ r2_hidden(X4,X1)
                      | ~ r2_hidden(X4,k1_relat_1(X0)) )
                  | ~ r2_hidden(X3,X2) )
                & ( ? [X5] :
                      ( k1_funct_1(X0,X5) = X3
                      & r2_hidden(X5,X1)
                      & r2_hidden(X5,k1_relat_1(X0)) )
                  | r2_hidden(X3,X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ? [X8] :
                      ( k1_funct_1(X0,X8) = X6
                      & r2_hidden(X8,X1)
                      & r2_hidden(X8,k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f26])).

fof(f30,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( ( ! [X4] :
                ( k1_funct_1(X0,X4) != X3
                | ~ r2_hidden(X4,X1)
                | ~ r2_hidden(X4,k1_relat_1(X0)) )
            | ~ r2_hidden(X3,X2) )
          & ( ? [X5] :
                ( k1_funct_1(X0,X5) = X3
                & r2_hidden(X5,X1)
                & r2_hidden(X5,k1_relat_1(X0)) )
            | r2_hidden(X3,X2) ) )
     => ( ( ! [X4] :
              ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK1(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK1(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2)
                  & r2_hidden(sK2(X0,X1,X2),X1)
                  & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
                    & r2_hidden(sK3(X0,X1,X6),X1)
                    & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f30,f29,f28])).

fof(f50,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f73,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f50])).

fof(f74,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f73])).

fof(f67,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f40])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f22,plain,(
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
    inference(nnf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(rectify,[],[f22])).

fof(f24,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK0(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
            & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ r2_hidden(X3,X1)
      | ~ r2_hidden(k4_tarski(X3,X0),X2)
      | ~ r2_hidden(X3,k1_relat_1(X2))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ! [X6,X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f82,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f62])).

fof(f2,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f80,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f65])).

cnf(c_1402,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3767,plain,
    ( k1_relset_1(sK6,sK7,sK8) != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = k1_relset_1(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_14655,plain,
    ( k1_relset_1(sK6,sK7,sK8) != k1_relset_1(X0,X1,X2)
    | k1_xboole_0 != k1_relset_1(X0,X1,X2)
    | k1_xboole_0 = k1_relset_1(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_3767])).

cnf(c_136101,plain,
    ( k1_relset_1(sK6,sK7,sK8) != k1_relset_1(k1_xboole_0,sK7,sK8)
    | k1_xboole_0 = k1_relset_1(sK6,sK7,sK8)
    | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_14655])).

cnf(c_1415,plain,
    ( X0 != X1
    | X2 != X3
    | X4 != X5
    | k1_relset_1(X0,X2,X4) = k1_relset_1(X1,X3,X5) ),
    theory(equality)).

cnf(c_14656,plain,
    ( k1_relset_1(sK6,sK7,sK8) = k1_relset_1(X0,X1,X2)
    | sK8 != X2
    | sK7 != X1
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_1415])).

cnf(c_41459,plain,
    ( k1_relset_1(sK6,sK7,sK8) = k1_relset_1(X0,sK7,X1)
    | sK8 != X1
    | sK7 != sK7
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_14656])).

cnf(c_114878,plain,
    ( k1_relset_1(sK6,sK7,sK8) = k1_relset_1(X0,sK7,sK8)
    | sK8 != sK8
    | sK7 != sK7
    | sK6 != X0 ),
    inference(instantiation,[status(thm)],[c_41459])).

cnf(c_114879,plain,
    ( k1_relset_1(sK6,sK7,sK8) = k1_relset_1(k1_xboole_0,sK7,sK8)
    | sK8 != sK8
    | sK7 != sK7
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_114878])).

cnf(c_2428,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_4277,plain,
    ( X0 != k1_relset_1(sK6,sK7,sK8)
    | X0 = sK6
    | sK6 != k1_relset_1(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_2428])).

cnf(c_78063,plain,
    ( k1_relat_1(sK8) != k1_relset_1(sK6,sK7,sK8)
    | k1_relat_1(sK8) = sK6
    | sK6 != k1_relset_1(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_4277])).

cnf(c_1404,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_2343,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK9(sK5(sK7,sK8)),sK6)
    | X0 != sK9(sK5(sK7,sK8))
    | X1 != sK6 ),
    inference(instantiation,[status(thm)],[c_1404])).

cnf(c_2936,plain,
    ( r2_hidden(sK9(sK5(sK7,sK8)),X0)
    | ~ r2_hidden(sK9(sK5(sK7,sK8)),sK6)
    | X0 != sK6
    | sK9(sK5(sK7,sK8)) != sK9(sK5(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_2343])).

cnf(c_62514,plain,
    ( r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8))
    | ~ r2_hidden(sK9(sK5(sK7,sK8)),sK6)
    | sK9(sK5(sK7,sK8)) != sK9(sK5(sK7,sK8))
    | k1_relat_1(sK8) != sK6 ),
    inference(instantiation,[status(thm)],[c_2936])).

cnf(c_2153,plain,
    ( X0 != X1
    | sK6 != X1
    | sK6 = X0 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_60018,plain,
    ( k1_relset_1(sK6,sK7,sK8) != X0
    | sK6 != X0
    | sK6 = k1_relset_1(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_2153])).

cnf(c_60019,plain,
    ( k1_relset_1(sK6,sK7,sK8) != k1_xboole_0
    | sK6 = k1_relset_1(sK6,sK7,sK8)
    | sK6 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_60018])).

cnf(c_14651,plain,
    ( X0 != X1
    | k1_relset_1(sK6,sK7,sK8) != X1
    | k1_relset_1(sK6,sK7,sK8) = X0 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_41270,plain,
    ( X0 != k1_relset_1(sK6,sK7,sK8)
    | k1_relset_1(sK6,sK7,sK8) = X0
    | k1_relset_1(sK6,sK7,sK8) != k1_relset_1(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_14651])).

cnf(c_41271,plain,
    ( k1_relset_1(sK6,sK7,sK8) != k1_relset_1(sK6,sK7,sK8)
    | k1_relset_1(sK6,sK7,sK8) = k1_xboole_0
    | k1_xboole_0 != k1_relset_1(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_41270])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK8,sK6,sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_336,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_25,c_29])).

cnf(c_337,plain,
    ( ~ v1_funct_2(sK8,X0,X1)
    | k1_relset_1(X0,X1,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_336])).

cnf(c_995,plain,
    ( k1_relset_1(X0,X1,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != sK8
    | sK7 != X1
    | sK6 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_337])).

cnf(c_996,plain,
    ( k1_relset_1(sK6,sK7,sK8) = sK6
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | k1_xboole_0 = sK7 ),
    inference(unflattening,[status(thm)],[c_995])).

cnf(c_1067,plain,
    ( k1_relset_1(sK6,sK7,sK8) = sK6
    | k1_xboole_0 = sK7 ),
    inference(equality_resolution_simp,[status(thm)],[c_996])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_429,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_15,c_29])).

cnf(c_430,plain,
    ( k1_relset_1(X0,X1,sK8) = k1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_429])).

cnf(c_2035,plain,
    ( k1_relset_1(sK6,sK7,sK8) = k1_relat_1(sK8) ),
    inference(equality_resolution,[status(thm)],[c_430])).

cnf(c_2231,plain,
    ( k1_relat_1(sK8) = sK6
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1067,c_2035])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK5(X2,X0),X2)
    | k2_relset_1(X1,X2,X0) = X2 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_372,plain,
    ( r2_hidden(sK5(X0,X1),X0)
    | k2_relset_1(X2,X0,X1) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X2,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_29])).

cnf(c_373,plain,
    ( r2_hidden(sK5(X0,sK8),X0)
    | k2_relset_1(X1,X0,sK8) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_372])).

cnf(c_1752,plain,
    ( k2_relset_1(X0,X1,sK8) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | r2_hidden(sK5(X1,sK8),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_373])).

cnf(c_3243,plain,
    ( k2_relset_1(sK6,sK7,sK8) = sK7
    | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1752])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_420,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_29])).

cnf(c_421,plain,
    ( k2_relset_1(X0,X1,sK8) = k2_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1996,plain,
    ( k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) ),
    inference(equality_resolution,[status(thm)],[c_421])).

cnf(c_3244,plain,
    ( k2_relat_1(sK8) = sK7
    | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3243,c_1996])).

cnf(c_26,negated_conjecture,
    ( k2_relset_1(sK6,sK7,sK8) != sK7 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1401,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2013,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) = k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_2106,plain,
    ( r2_hidden(sK5(sK7,sK8),sK7)
    | k2_relset_1(sK6,sK7,sK8) = sK7
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_373])).

cnf(c_2107,plain,
    ( k2_relset_1(sK6,sK7,sK8) = sK7
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2106])).

cnf(c_22598,plain,
    ( r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3244,c_26,c_2013,c_2107])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,sK9(X0)) = X0 ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1754,plain,
    ( k1_funct_1(sK8,sK9(X0)) = X0
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22605,plain,
    ( k1_funct_1(sK8,sK9(sK5(sK7,sK8))) = sK5(sK7,sK8) ),
    inference(superposition,[status(thm)],[c_22598,c_1754])).

cnf(c_28,negated_conjecture,
    ( ~ r2_hidden(X0,sK7)
    | r2_hidden(sK9(X0),sK6) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1753,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(sK9(X0),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f67])).

cnf(c_617,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_relat_1(X2)
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_31])).

cnf(c_618,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
    | ~ v1_relat_1(sK8) ),
    inference(unflattening,[status(thm)],[c_617])).

cnf(c_1745,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_618])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_438,plain,
    ( v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_29])).

cnf(c_439,plain,
    ( v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_438])).

cnf(c_2016,plain,
    ( v1_relat_1(sK8)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_439])).

cnf(c_2040,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | ~ r2_hidden(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_618,c_2013,c_2016])).

cnf(c_2041,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(sK8))
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) ),
    inference(renaming,[status(thm)],[c_2040])).

cnf(c_2042,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2041])).

cnf(c_3088,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1745,c_2042])).

cnf(c_3089,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top ),
    inference(renaming,[status(thm)],[c_3088])).

cnf(c_3,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1755,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1756,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,k9_relat_1(X3,X1))
    | ~ r2_hidden(X0,k1_relat_1(X3))
    | ~ r2_hidden(k4_tarski(X0,X2),X3)
    | ~ v1_relat_1(X3) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1758,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
    | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
    | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
    | v1_relat_1(X3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_3028,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k9_relat_1(X1,X3)) = iProver_top
    | r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1756,c_1758])).

cnf(c_101,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_8324,plain,
    ( r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
    | r2_hidden(X0,k9_relat_1(X1,X3)) = iProver_top
    | r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3028,c_101])).

cnf(c_8325,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k9_relat_1(X1,X3)) = iProver_top
    | r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_8324])).

cnf(c_8333,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k9_relat_1(X1,k1_relat_1(X1))) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1755,c_8325])).

cnf(c_8566,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_8333])).

cnf(c_2017,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2016])).

cnf(c_9309,plain,
    ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8566,c_2013,c_2017])).

cnf(c_9310,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
    | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top ),
    inference(renaming,[status(thm)],[c_9309])).

cnf(c_9321,plain,
    ( r2_hidden(X0,sK7) != iProver_top
    | r2_hidden(k1_funct_1(sK8,sK9(X0)),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
    | r2_hidden(sK9(X0),k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1753,c_9310])).

cnf(c_22914,plain,
    ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
    | r2_hidden(sK5(sK7,sK8),sK7) != iProver_top
    | r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) != iProver_top ),
    inference(superposition,[status(thm)],[c_22605,c_9321])).

cnf(c_24087,plain,
    ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
    | r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22914,c_26,c_2013,c_2107])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r2_hidden(k4_tarski(X3,sK5(X2,X0)),X0)
    | k2_relset_1(X1,X2,X0) = X2 ),
    inference(cnf_transformation,[],[f59])).

cnf(c_387,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK5(X1,X2)),X2)
    | k2_relset_1(X3,X1,X2) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X3,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_18,c_29])).

cnf(c_388,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK5(X1,sK8)),sK8)
    | k2_relset_1(X2,X1,sK8) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_387])).

cnf(c_1751,plain,
    ( k2_relset_1(X0,X1,sK8) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | r2_hidden(k4_tarski(X2,sK5(X1,sK8)),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_388])).

cnf(c_2754,plain,
    ( k2_relset_1(sK6,sK7,sK8) = sK7
    | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
    inference(equality_resolution,[status(thm)],[c_1751])).

cnf(c_2755,plain,
    ( k2_relat_1(sK8) = sK7
    | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_2754,c_1996])).

cnf(c_2109,plain,
    ( ~ r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8)
    | k2_relset_1(sK6,sK7,sK8) = sK7
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_388])).

cnf(c_2110,plain,
    ( k2_relset_1(sK6,sK7,sK8) = sK7
    | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2109])).

cnf(c_4405,plain,
    ( r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2755,c_26,c_2013,c_2110])).

cnf(c_4412,plain,
    ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,X0)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1756,c_4405])).

cnf(c_6132,plain,
    ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,X0)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4412,c_2013,c_2017])).

cnf(c_24093,plain,
    ( r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_24087,c_6132])).

cnf(c_24095,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(sK9(sK5(sK7,sK8)),sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_2231,c_24093])).

cnf(c_24094,plain,
    ( ~ r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_24093])).

cnf(c_14687,plain,
    ( k1_relset_1(sK6,sK7,sK8) = k1_relset_1(sK6,sK7,sK8) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_1408,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_12448,plain,
    ( k2_relat_1(sK8) = k2_relat_1(X0)
    | sK8 != X0 ),
    inference(instantiation,[status(thm)],[c_1408])).

cnf(c_12450,plain,
    ( k2_relat_1(sK8) = k2_relat_1(k1_xboole_0)
    | sK8 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_12448])).

cnf(c_3995,plain,
    ( X0 != X1
    | X0 = k2_relat_1(sK8)
    | k2_relat_1(sK8) != X1 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_12447,plain,
    ( X0 != k2_relat_1(X1)
    | X0 = k2_relat_1(sK8)
    | k2_relat_1(sK8) != k2_relat_1(X1) ),
    inference(instantiation,[status(thm)],[c_3995])).

cnf(c_12449,plain,
    ( k2_relat_1(sK8) != k2_relat_1(k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK8)
    | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_12447])).

cnf(c_3725,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1402,c_1401])).

cnf(c_2406,plain,
    ( k1_relset_1(sK6,sK7,sK8) = k1_relat_1(sK8) ),
    inference(resolution,[status(thm)],[c_430,c_1401])).

cnf(c_10209,plain,
    ( k1_relat_1(sK8) = k1_relset_1(sK6,sK7,sK8) ),
    inference(resolution,[status(thm)],[c_3725,c_2406])).

cnf(c_1414,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_24,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_485,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_24,c_29])).

cnf(c_486,plain,
    ( ~ v1_funct_2(sK8,k1_xboole_0,X0)
    | k1_relset_1(k1_xboole_0,X0,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(unflattening,[status(thm)],[c_485])).

cnf(c_1020,plain,
    ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != sK8
    | sK7 != X0
    | sK6 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_486])).

cnf(c_1021,plain,
    ( k1_relset_1(k1_xboole_0,sK7,sK8) = k1_xboole_0
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK6 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_1020])).

cnf(c_2788,plain,
    ( k1_relset_1(k1_xboole_0,sK7,sK8) = k1_xboole_0
    | k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(sK6,sK7)
    | sK6 != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1414,c_1021])).

cnf(c_1436,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_2149,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_2219,plain,
    ( sK6 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK6 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_2220,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2219])).

cnf(c_1413,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_2178,plain,
    ( X0 != sK7
    | X1 != sK6
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK6,sK7) ),
    inference(instantiation,[status(thm)],[c_1413])).

cnf(c_2326,plain,
    ( X0 != sK6
    | k2_zfmisc_1(X0,sK7) = k2_zfmisc_1(sK6,sK7)
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_2178])).

cnf(c_2327,plain,
    ( k2_zfmisc_1(k1_xboole_0,sK7) = k2_zfmisc_1(sK6,sK7)
    | sK7 != sK7
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2326])).

cnf(c_3960,plain,
    ( k1_relset_1(k1_xboole_0,sK7,sK8) = k1_xboole_0
    | sK6 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2788,c_1436,c_2149,c_2220,c_2327])).

cnf(c_10200,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK7,sK8) ),
    inference(resolution,[status(thm)],[c_3725,c_3960])).

cnf(c_4,plain,
    ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f46])).

cnf(c_10168,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3725,c_4])).

cnf(c_2021,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK6,sK7)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_1414])).

cnf(c_7797,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) != k2_zfmisc_1(sK6,sK7)
    | k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
    inference(instantiation,[status(thm)],[c_2021])).

cnf(c_3074,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_2532,plain,
    ( X0 != X1
    | k2_relset_1(sK6,sK7,sK8) != X1
    | k2_relset_1(sK6,sK7,sK8) = X0 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_3054,plain,
    ( X0 != k2_relat_1(sK8)
    | k2_relset_1(sK6,sK7,sK8) = X0
    | k2_relset_1(sK6,sK7,sK8) != k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_2532])).

cnf(c_3055,plain,
    ( k2_relset_1(sK6,sK7,sK8) != k2_relat_1(sK8)
    | k2_relset_1(sK6,sK7,sK8) = k1_xboole_0
    | k1_xboole_0 != k2_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_3054])).

cnf(c_2937,plain,
    ( sK9(sK5(sK7,sK8)) = sK9(sK5(sK7,sK8)) ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_2556,plain,
    ( X0 != sK7
    | k2_zfmisc_1(sK6,X0) = k2_zfmisc_1(sK6,sK7)
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2178])).

cnf(c_2557,plain,
    ( k2_zfmisc_1(sK6,k1_xboole_0) = k2_zfmisc_1(sK6,sK7)
    | sK6 != sK6
    | k1_xboole_0 != sK7 ),
    inference(instantiation,[status(thm)],[c_2556])).

cnf(c_2214,plain,
    ( sK7 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK7 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_2215,plain,
    ( sK7 != k1_xboole_0
    | k1_xboole_0 = sK7
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_2206,plain,
    ( ~ r2_hidden(sK5(sK7,sK8),sK7)
    | r2_hidden(sK9(sK5(sK7,sK8)),sK6) ),
    inference(instantiation,[status(thm)],[c_28])).

cnf(c_2207,plain,
    ( r2_hidden(sK5(sK7,sK8),sK7) != iProver_top
    | r2_hidden(sK9(sK5(sK7,sK8)),sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2206])).

cnf(c_2152,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1401])).

cnf(c_2032,plain,
    ( sK6 != X0
    | sK6 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_2151,plain,
    ( sK6 != sK6
    | sK6 = k1_xboole_0
    | k1_xboole_0 != sK6 ),
    inference(instantiation,[status(thm)],[c_2032])).

cnf(c_2025,plain,
    ( k2_relset_1(sK6,sK7,sK8) != X0
    | k2_relset_1(sK6,sK7,sK8) = sK7
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_1402])).

cnf(c_2026,plain,
    ( k2_relset_1(sK6,sK7,sK8) = sK7
    | k2_relset_1(sK6,sK7,sK8) != k1_xboole_0
    | sK7 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2025])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_467,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_21,c_29])).

cnf(c_468,plain,
    ( ~ v1_funct_2(sK8,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK8 ),
    inference(unflattening,[status(thm)],[c_467])).

cnf(c_1006,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 != sK8
    | sK8 = k1_xboole_0
    | sK7 != k1_xboole_0
    | sK6 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_30,c_468])).

cnf(c_1007,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
    | sK8 = k1_xboole_0
    | sK7 != k1_xboole_0
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_1006])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_136101,c_114879,c_78063,c_62514,c_60019,c_41271,c_24095,c_24094,c_14687,c_12450,c_12449,c_10209,c_10200,c_10168,c_7797,c_3074,c_3055,c_2937,c_2557,c_2215,c_2207,c_2206,c_2152,c_2151,c_2149,c_2107,c_2106,c_2026,c_2013,c_1996,c_1436,c_1007,c_26])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:27:37 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 43.37/6.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 43.37/6.00  
% 43.37/6.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 43.37/6.00  
% 43.37/6.00  ------  iProver source info
% 43.37/6.00  
% 43.37/6.00  git: date: 2020-06-30 10:37:57 +0100
% 43.37/6.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 43.37/6.00  git: non_committed_changes: false
% 43.37/6.00  git: last_make_outside_of_git: false
% 43.37/6.00  
% 43.37/6.00  ------ 
% 43.37/6.00  ------ Parsing...
% 43.37/6.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 43.37/6.00  
% 43.37/6.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 43.37/6.00  ------ Proving...
% 43.37/6.00  ------ Problem Properties 
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  clauses                                 26
% 43.37/6.00  conjectures                             3
% 43.37/6.00  EPR                                     0
% 43.37/6.00  Horn                                    20
% 43.37/6.00  unary                                   3
% 43.37/6.00  binary                                  6
% 43.37/6.00  lits                                    77
% 43.37/6.00  lits eq                                 31
% 43.37/6.00  fd_pure                                 0
% 43.37/6.00  fd_pseudo                               0
% 43.37/6.00  fd_cond                                 0
% 43.37/6.00  fd_pseudo_cond                          4
% 43.37/6.00  AC symbols                              0
% 43.37/6.00  
% 43.37/6.00  ------ Input Options Time Limit: Unbounded
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ 
% 43.37/6.00  Current options:
% 43.37/6.00  ------ 
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  ------ Proving...
% 43.37/6.00  
% 43.37/6.00  
% 43.37/6.00  % SZS status Theorem for theBenchmark.p
% 43.37/6.00  
% 43.37/6.00  % SZS output start CNFRefutation for theBenchmark.p
% 43.37/6.00  
% 43.37/6.00  fof(f9,conjecture,(
% 43.37/6.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f10,negated_conjecture,(
% 43.37/6.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 43.37/6.00    inference(negated_conjecture,[],[f9])).
% 43.37/6.00  
% 43.37/6.00  fof(f20,plain,(
% 43.37/6.00    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 43.37/6.00    inference(ennf_transformation,[],[f10])).
% 43.37/6.00  
% 43.37/6.00  fof(f21,plain,(
% 43.37/6.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 43.37/6.00    inference(flattening,[],[f20])).
% 43.37/6.00  
% 43.37/6.00  fof(f39,plain,(
% 43.37/6.00    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK9(X3)) = X3 & r2_hidden(sK9(X3),X0)))) )),
% 43.37/6.00    introduced(choice_axiom,[])).
% 43.37/6.00  
% 43.37/6.00  fof(f38,plain,(
% 43.37/6.00    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK6,sK7,sK8) != sK7 & ! [X3] : (? [X4] : (k1_funct_1(sK8,X4) = X3 & r2_hidden(X4,sK6)) | ~r2_hidden(X3,sK7)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8))),
% 43.37/6.00    introduced(choice_axiom,[])).
% 43.37/6.00  
% 43.37/6.00  fof(f40,plain,(
% 43.37/6.00    k2_relset_1(sK6,sK7,sK8) != sK7 & ! [X3] : ((k1_funct_1(sK8,sK9(X3)) = X3 & r2_hidden(sK9(X3),sK6)) | ~r2_hidden(X3,sK7)) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_2(sK8,sK6,sK7) & v1_funct_1(sK8)),
% 43.37/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9])],[f21,f39,f38])).
% 43.37/6.00  
% 43.37/6.00  fof(f68,plain,(
% 43.37/6.00    v1_funct_2(sK8,sK6,sK7)),
% 43.37/6.00    inference(cnf_transformation,[],[f40])).
% 43.37/6.00  
% 43.37/6.00  fof(f8,axiom,(
% 43.37/6.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f18,plain,(
% 43.37/6.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.37/6.00    inference(ennf_transformation,[],[f8])).
% 43.37/6.00  
% 43.37/6.00  fof(f19,plain,(
% 43.37/6.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.37/6.00    inference(flattening,[],[f18])).
% 43.37/6.00  
% 43.37/6.00  fof(f37,plain,(
% 43.37/6.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.37/6.00    inference(nnf_transformation,[],[f19])).
% 43.37/6.00  
% 43.37/6.00  fof(f61,plain,(
% 43.37/6.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.37/6.00    inference(cnf_transformation,[],[f37])).
% 43.37/6.00  
% 43.37/6.00  fof(f69,plain,(
% 43.37/6.00    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 43.37/6.00    inference(cnf_transformation,[],[f40])).
% 43.37/6.00  
% 43.37/6.00  fof(f5,axiom,(
% 43.37/6.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f15,plain,(
% 43.37/6.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.37/6.00    inference(ennf_transformation,[],[f5])).
% 43.37/6.00  
% 43.37/6.00  fof(f56,plain,(
% 43.37/6.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.37/6.00    inference(cnf_transformation,[],[f15])).
% 43.37/6.00  
% 43.37/6.00  fof(f7,axiom,(
% 43.37/6.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (! [X3] : ~(! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f17,plain,(
% 43.37/6.00    ! [X0,X1,X2] : ((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) <=> k2_relset_1(X0,X1,X2) = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.37/6.00    inference(ennf_transformation,[],[f7])).
% 43.37/6.00  
% 43.37/6.00  fof(f32,plain,(
% 43.37/6.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X3] : (! [X4] : ~r2_hidden(k4_tarski(X4,X3),X2) & r2_hidden(X3,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.37/6.00    inference(nnf_transformation,[],[f17])).
% 43.37/6.00  
% 43.37/6.00  fof(f33,plain,(
% 43.37/6.00    ! [X0,X1,X2] : (((! [X3] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | ? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.37/6.00    inference(rectify,[],[f32])).
% 43.37/6.00  
% 43.37/6.00  fof(f35,plain,(
% 43.37/6.00    ! [X2,X1] : (? [X5] : (! [X6] : ~r2_hidden(k4_tarski(X6,X5),X2) & r2_hidden(X5,X1)) => (! [X6] : ~r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2) & r2_hidden(sK5(X1,X2),X1)))),
% 43.37/6.00    introduced(choice_axiom,[])).
% 43.37/6.00  
% 43.37/6.00  fof(f34,plain,(
% 43.37/6.00    ! [X3,X2] : (? [X4] : r2_hidden(k4_tarski(X4,X3),X2) => r2_hidden(k4_tarski(sK4(X2,X3),X3),X2))),
% 43.37/6.00    introduced(choice_axiom,[])).
% 43.37/6.00  
% 43.37/6.00  fof(f36,plain,(
% 43.37/6.00    ! [X0,X1,X2] : (((! [X3] : (r2_hidden(k4_tarski(sK4(X2,X3),X3),X2) | ~r2_hidden(X3,X1)) | k2_relset_1(X0,X1,X2) != X1) & (k2_relset_1(X0,X1,X2) = X1 | (! [X6] : ~r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2) & r2_hidden(sK5(X1,X2),X1)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.37/6.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5])],[f33,f35,f34])).
% 43.37/6.00  
% 43.37/6.00  fof(f58,plain,(
% 43.37/6.00    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | r2_hidden(sK5(X1,X2),X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.37/6.00    inference(cnf_transformation,[],[f36])).
% 43.37/6.00  
% 43.37/6.00  fof(f6,axiom,(
% 43.37/6.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 43.37/6.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.00  
% 43.37/6.00  fof(f16,plain,(
% 43.37/6.00    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.37/6.00    inference(ennf_transformation,[],[f6])).
% 43.37/6.00  
% 43.37/6.00  fof(f57,plain,(
% 43.37/6.00    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.37/6.00    inference(cnf_transformation,[],[f16])).
% 43.37/6.00  
% 43.37/6.00  fof(f72,plain,(
% 43.37/6.00    k2_relset_1(sK6,sK7,sK8) != sK7),
% 43.37/6.00    inference(cnf_transformation,[],[f40])).
% 43.37/6.00  
% 43.37/6.00  fof(f71,plain,(
% 43.37/6.00    ( ! [X3] : (k1_funct_1(sK8,sK9(X3)) = X3 | ~r2_hidden(X3,sK7)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f40])).
% 43.37/6.00  
% 43.37/6.00  fof(f70,plain,(
% 43.37/6.00    ( ! [X3] : (r2_hidden(sK9(X3),sK6) | ~r2_hidden(X3,sK7)) )),
% 43.37/6.00    inference(cnf_transformation,[],[f40])).
% 43.37/6.00  
% 43.37/6.00  fof(f3,axiom,(
% 43.37/6.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 43.37/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.01  
% 43.37/6.01  fof(f12,plain,(
% 43.37/6.01    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 43.37/6.01    inference(ennf_transformation,[],[f3])).
% 43.37/6.01  
% 43.37/6.01  fof(f13,plain,(
% 43.37/6.01    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 43.37/6.01    inference(flattening,[],[f12])).
% 43.37/6.01  
% 43.37/6.01  fof(f26,plain,(
% 43.37/6.01    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 43.37/6.01    inference(nnf_transformation,[],[f13])).
% 43.37/6.01  
% 43.37/6.01  fof(f27,plain,(
% 43.37/6.01    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 43.37/6.01    inference(rectify,[],[f26])).
% 43.37/6.01  
% 43.37/6.01  fof(f30,plain,(
% 43.37/6.01    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 43.37/6.01    introduced(choice_axiom,[])).
% 43.37/6.01  
% 43.37/6.01  fof(f29,plain,(
% 43.37/6.01    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 43.37/6.01    introduced(choice_axiom,[])).
% 43.37/6.01  
% 43.37/6.01  fof(f28,plain,(
% 43.37/6.01    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 43.37/6.01    introduced(choice_axiom,[])).
% 43.37/6.01  
% 43.37/6.01  fof(f31,plain,(
% 43.37/6.01    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 43.37/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f27,f30,f29,f28])).
% 43.37/6.01  
% 43.37/6.01  fof(f50,plain,(
% 43.37/6.01    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 43.37/6.01    inference(cnf_transformation,[],[f31])).
% 43.37/6.01  
% 43.37/6.01  fof(f73,plain,(
% 43.37/6.01    ( ! [X2,X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),X2) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 43.37/6.01    inference(equality_resolution,[],[f50])).
% 43.37/6.01  
% 43.37/6.01  fof(f74,plain,(
% 43.37/6.01    ( ! [X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 43.37/6.01    inference(equality_resolution,[],[f73])).
% 43.37/6.01  
% 43.37/6.01  fof(f67,plain,(
% 43.37/6.01    v1_funct_1(sK8)),
% 43.37/6.01    inference(cnf_transformation,[],[f40])).
% 43.37/6.01  
% 43.37/6.01  fof(f4,axiom,(
% 43.37/6.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 43.37/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.01  
% 43.37/6.01  fof(f14,plain,(
% 43.37/6.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 43.37/6.01    inference(ennf_transformation,[],[f4])).
% 43.37/6.01  
% 43.37/6.01  fof(f55,plain,(
% 43.37/6.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.37/6.01    inference(cnf_transformation,[],[f14])).
% 43.37/6.01  
% 43.37/6.01  fof(f1,axiom,(
% 43.37/6.01    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 43.37/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.01  
% 43.37/6.01  fof(f11,plain,(
% 43.37/6.01    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 43.37/6.01    inference(ennf_transformation,[],[f1])).
% 43.37/6.01  
% 43.37/6.01  fof(f22,plain,(
% 43.37/6.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 43.37/6.01    inference(nnf_transformation,[],[f11])).
% 43.37/6.01  
% 43.37/6.01  fof(f23,plain,(
% 43.37/6.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 43.37/6.01    inference(rectify,[],[f22])).
% 43.37/6.01  
% 43.37/6.01  fof(f24,plain,(
% 43.37/6.01    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 43.37/6.01    introduced(choice_axiom,[])).
% 43.37/6.01  
% 43.37/6.01  fof(f25,plain,(
% 43.37/6.01    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 43.37/6.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f23,f24])).
% 43.37/6.01  
% 43.37/6.01  fof(f41,plain,(
% 43.37/6.01    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 43.37/6.01    inference(cnf_transformation,[],[f25])).
% 43.37/6.01  
% 43.37/6.01  fof(f42,plain,(
% 43.37/6.01    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 43.37/6.01    inference(cnf_transformation,[],[f25])).
% 43.37/6.01  
% 43.37/6.01  fof(f44,plain,(
% 43.37/6.01    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,k9_relat_1(X2,X1)) | ~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)) | ~v1_relat_1(X2)) )),
% 43.37/6.01    inference(cnf_transformation,[],[f25])).
% 43.37/6.01  
% 43.37/6.01  fof(f59,plain,(
% 43.37/6.01    ( ! [X6,X2,X0,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_hidden(k4_tarski(X6,sK5(X1,X2)),X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.37/6.01    inference(cnf_transformation,[],[f36])).
% 43.37/6.01  
% 43.37/6.01  fof(f62,plain,(
% 43.37/6.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.37/6.01    inference(cnf_transformation,[],[f37])).
% 43.37/6.01  
% 43.37/6.01  fof(f82,plain,(
% 43.37/6.01    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 43.37/6.01    inference(equality_resolution,[],[f62])).
% 43.37/6.01  
% 43.37/6.01  fof(f2,axiom,(
% 43.37/6.01    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_relat_1(k1_xboole_0) = k1_xboole_0),
% 43.37/6.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 43.37/6.01  
% 43.37/6.01  fof(f46,plain,(
% 43.37/6.01    k1_xboole_0 = k2_relat_1(k1_xboole_0)),
% 43.37/6.01    inference(cnf_transformation,[],[f2])).
% 43.37/6.01  
% 43.37/6.01  fof(f65,plain,(
% 43.37/6.01    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 43.37/6.01    inference(cnf_transformation,[],[f37])).
% 43.37/6.01  
% 43.37/6.01  fof(f80,plain,(
% 43.37/6.01    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 43.37/6.01    inference(equality_resolution,[],[f65])).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1402,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3767,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) != X0
% 43.37/6.01      | k1_xboole_0 != X0
% 43.37/6.01      | k1_xboole_0 = k1_relset_1(sK6,sK7,sK8) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1402]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_14655,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) != k1_relset_1(X0,X1,X2)
% 43.37/6.01      | k1_xboole_0 != k1_relset_1(X0,X1,X2)
% 43.37/6.01      | k1_xboole_0 = k1_relset_1(sK6,sK7,sK8) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_3767]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_136101,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) != k1_relset_1(k1_xboole_0,sK7,sK8)
% 43.37/6.01      | k1_xboole_0 = k1_relset_1(sK6,sK7,sK8)
% 43.37/6.01      | k1_xboole_0 != k1_relset_1(k1_xboole_0,sK7,sK8) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_14655]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1415,plain,
% 43.37/6.01      ( X0 != X1
% 43.37/6.01      | X2 != X3
% 43.37/6.01      | X4 != X5
% 43.37/6.01      | k1_relset_1(X0,X2,X4) = k1_relset_1(X1,X3,X5) ),
% 43.37/6.01      theory(equality) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_14656,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) = k1_relset_1(X0,X1,X2)
% 43.37/6.01      | sK8 != X2
% 43.37/6.01      | sK7 != X1
% 43.37/6.01      | sK6 != X0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1415]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_41459,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) = k1_relset_1(X0,sK7,X1)
% 43.37/6.01      | sK8 != X1
% 43.37/6.01      | sK7 != sK7
% 43.37/6.01      | sK6 != X0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_14656]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_114878,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) = k1_relset_1(X0,sK7,sK8)
% 43.37/6.01      | sK8 != sK8
% 43.37/6.01      | sK7 != sK7
% 43.37/6.01      | sK6 != X0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_41459]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_114879,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) = k1_relset_1(k1_xboole_0,sK7,sK8)
% 43.37/6.01      | sK8 != sK8
% 43.37/6.01      | sK7 != sK7
% 43.37/6.01      | sK6 != k1_xboole_0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_114878]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2428,plain,
% 43.37/6.01      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1402]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_4277,plain,
% 43.37/6.01      ( X0 != k1_relset_1(sK6,sK7,sK8)
% 43.37/6.01      | X0 = sK6
% 43.37/6.01      | sK6 != k1_relset_1(sK6,sK7,sK8) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2428]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_78063,plain,
% 43.37/6.01      ( k1_relat_1(sK8) != k1_relset_1(sK6,sK7,sK8)
% 43.37/6.01      | k1_relat_1(sK8) = sK6
% 43.37/6.01      | sK6 != k1_relset_1(sK6,sK7,sK8) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_4277]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1404,plain,
% 43.37/6.01      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 43.37/6.01      theory(equality) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2343,plain,
% 43.37/6.01      ( r2_hidden(X0,X1)
% 43.37/6.01      | ~ r2_hidden(sK9(sK5(sK7,sK8)),sK6)
% 43.37/6.01      | X0 != sK9(sK5(sK7,sK8))
% 43.37/6.01      | X1 != sK6 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1404]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2936,plain,
% 43.37/6.01      ( r2_hidden(sK9(sK5(sK7,sK8)),X0)
% 43.37/6.01      | ~ r2_hidden(sK9(sK5(sK7,sK8)),sK6)
% 43.37/6.01      | X0 != sK6
% 43.37/6.01      | sK9(sK5(sK7,sK8)) != sK9(sK5(sK7,sK8)) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2343]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_62514,plain,
% 43.37/6.01      ( r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8))
% 43.37/6.01      | ~ r2_hidden(sK9(sK5(sK7,sK8)),sK6)
% 43.37/6.01      | sK9(sK5(sK7,sK8)) != sK9(sK5(sK7,sK8))
% 43.37/6.01      | k1_relat_1(sK8) != sK6 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2936]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2153,plain,
% 43.37/6.01      ( X0 != X1 | sK6 != X1 | sK6 = X0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1402]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_60018,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) != X0
% 43.37/6.01      | sK6 != X0
% 43.37/6.01      | sK6 = k1_relset_1(sK6,sK7,sK8) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2153]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_60019,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) != k1_xboole_0
% 43.37/6.01      | sK6 = k1_relset_1(sK6,sK7,sK8)
% 43.37/6.01      | sK6 != k1_xboole_0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_60018]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_14651,plain,
% 43.37/6.01      ( X0 != X1
% 43.37/6.01      | k1_relset_1(sK6,sK7,sK8) != X1
% 43.37/6.01      | k1_relset_1(sK6,sK7,sK8) = X0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1402]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_41270,plain,
% 43.37/6.01      ( X0 != k1_relset_1(sK6,sK7,sK8)
% 43.37/6.01      | k1_relset_1(sK6,sK7,sK8) = X0
% 43.37/6.01      | k1_relset_1(sK6,sK7,sK8) != k1_relset_1(sK6,sK7,sK8) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_14651]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_41271,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) != k1_relset_1(sK6,sK7,sK8)
% 43.37/6.01      | k1_relset_1(sK6,sK7,sK8) = k1_xboole_0
% 43.37/6.01      | k1_xboole_0 != k1_relset_1(sK6,sK7,sK8) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_41270]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_30,negated_conjecture,
% 43.37/6.01      ( v1_funct_2(sK8,sK6,sK7) ),
% 43.37/6.01      inference(cnf_transformation,[],[f68]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_25,plain,
% 43.37/6.01      ( ~ v1_funct_2(X0,X1,X2)
% 43.37/6.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.37/6.01      | k1_relset_1(X1,X2,X0) = X1
% 43.37/6.01      | k1_xboole_0 = X2 ),
% 43.37/6.01      inference(cnf_transformation,[],[f61]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_29,negated_conjecture,
% 43.37/6.01      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 43.37/6.01      inference(cnf_transformation,[],[f69]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_336,plain,
% 43.37/6.01      ( ~ v1_funct_2(X0,X1,X2)
% 43.37/6.01      | k1_relset_1(X1,X2,X0) = X1
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK8 != X0
% 43.37/6.01      | k1_xboole_0 = X2 ),
% 43.37/6.01      inference(resolution_lifted,[status(thm)],[c_25,c_29]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_337,plain,
% 43.37/6.01      ( ~ v1_funct_2(sK8,X0,X1)
% 43.37/6.01      | k1_relset_1(X0,X1,sK8) = X0
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | k1_xboole_0 = X1 ),
% 43.37/6.01      inference(unflattening,[status(thm)],[c_336]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_995,plain,
% 43.37/6.01      ( k1_relset_1(X0,X1,sK8) = X0
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK8 != sK8
% 43.37/6.01      | sK7 != X1
% 43.37/6.01      | sK6 != X0
% 43.37/6.01      | k1_xboole_0 = X1 ),
% 43.37/6.01      inference(resolution_lifted,[status(thm)],[c_30,c_337]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_996,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) = sK6
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | k1_xboole_0 = sK7 ),
% 43.37/6.01      inference(unflattening,[status(thm)],[c_995]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1067,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) = sK6 | k1_xboole_0 = sK7 ),
% 43.37/6.01      inference(equality_resolution_simp,[status(thm)],[c_996]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_15,plain,
% 43.37/6.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.37/6.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 43.37/6.01      inference(cnf_transformation,[],[f56]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_429,plain,
% 43.37/6.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK8 != X2 ),
% 43.37/6.01      inference(resolution_lifted,[status(thm)],[c_15,c_29]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_430,plain,
% 43.37/6.01      ( k1_relset_1(X0,X1,sK8) = k1_relat_1(sK8)
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 43.37/6.01      inference(unflattening,[status(thm)],[c_429]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2035,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) = k1_relat_1(sK8) ),
% 43.37/6.01      inference(equality_resolution,[status(thm)],[c_430]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2231,plain,
% 43.37/6.01      ( k1_relat_1(sK8) = sK6 | sK7 = k1_xboole_0 ),
% 43.37/6.01      inference(superposition,[status(thm)],[c_1067,c_2035]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_19,plain,
% 43.37/6.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.37/6.01      | r2_hidden(sK5(X2,X0),X2)
% 43.37/6.01      | k2_relset_1(X1,X2,X0) = X2 ),
% 43.37/6.01      inference(cnf_transformation,[],[f58]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_372,plain,
% 43.37/6.01      ( r2_hidden(sK5(X0,X1),X0)
% 43.37/6.01      | k2_relset_1(X2,X0,X1) = X0
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK8 != X1 ),
% 43.37/6.01      inference(resolution_lifted,[status(thm)],[c_19,c_29]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_373,plain,
% 43.37/6.01      ( r2_hidden(sK5(X0,sK8),X0)
% 43.37/6.01      | k2_relset_1(X1,X0,sK8) = X0
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 43.37/6.01      inference(unflattening,[status(thm)],[c_372]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1752,plain,
% 43.37/6.01      ( k2_relset_1(X0,X1,sK8) = X1
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | r2_hidden(sK5(X1,sK8),X1) = iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_373]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3243,plain,
% 43.37/6.01      ( k2_relset_1(sK6,sK7,sK8) = sK7
% 43.37/6.01      | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
% 43.37/6.01      inference(equality_resolution,[status(thm)],[c_1752]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_16,plain,
% 43.37/6.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.37/6.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 43.37/6.01      inference(cnf_transformation,[],[f57]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_420,plain,
% 43.37/6.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK8 != X2 ),
% 43.37/6.01      inference(resolution_lifted,[status(thm)],[c_16,c_29]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_421,plain,
% 43.37/6.01      ( k2_relset_1(X0,X1,sK8) = k2_relat_1(sK8)
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 43.37/6.01      inference(unflattening,[status(thm)],[c_420]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1996,plain,
% 43.37/6.01      ( k2_relset_1(sK6,sK7,sK8) = k2_relat_1(sK8) ),
% 43.37/6.01      inference(equality_resolution,[status(thm)],[c_421]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3244,plain,
% 43.37/6.01      ( k2_relat_1(sK8) = sK7
% 43.37/6.01      | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
% 43.37/6.01      inference(demodulation,[status(thm)],[c_3243,c_1996]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_26,negated_conjecture,
% 43.37/6.01      ( k2_relset_1(sK6,sK7,sK8) != sK7 ),
% 43.37/6.01      inference(cnf_transformation,[],[f72]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1401,plain,( X0 = X0 ),theory(equality) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2013,plain,
% 43.37/6.01      ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) = k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1401]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2106,plain,
% 43.37/6.01      ( r2_hidden(sK5(sK7,sK8),sK7)
% 43.37/6.01      | k2_relset_1(sK6,sK7,sK8) = sK7
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_373]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2107,plain,
% 43.37/6.01      ( k2_relset_1(sK6,sK7,sK8) = sK7
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_2106]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_22598,plain,
% 43.37/6.01      ( r2_hidden(sK5(sK7,sK8),sK7) = iProver_top ),
% 43.37/6.01      inference(global_propositional_subsumption,
% 43.37/6.01                [status(thm)],
% 43.37/6.01                [c_3244,c_26,c_2013,c_2107]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_27,negated_conjecture,
% 43.37/6.01      ( ~ r2_hidden(X0,sK7) | k1_funct_1(sK8,sK9(X0)) = X0 ),
% 43.37/6.01      inference(cnf_transformation,[],[f71]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1754,plain,
% 43.37/6.01      ( k1_funct_1(sK8,sK9(X0)) = X0 | r2_hidden(X0,sK7) != iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_22605,plain,
% 43.37/6.01      ( k1_funct_1(sK8,sK9(sK5(sK7,sK8))) = sK5(sK7,sK8) ),
% 43.37/6.01      inference(superposition,[status(thm)],[c_22598,c_1754]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_28,negated_conjecture,
% 43.37/6.01      ( ~ r2_hidden(X0,sK7) | r2_hidden(sK9(X0),sK6) ),
% 43.37/6.01      inference(cnf_transformation,[],[f70]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1753,plain,
% 43.37/6.01      ( r2_hidden(X0,sK7) != iProver_top
% 43.37/6.01      | r2_hidden(sK9(X0),sK6) = iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_10,plain,
% 43.37/6.01      ( ~ r2_hidden(X0,X1)
% 43.37/6.01      | ~ r2_hidden(X0,k1_relat_1(X2))
% 43.37/6.01      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 43.37/6.01      | ~ v1_funct_1(X2)
% 43.37/6.01      | ~ v1_relat_1(X2) ),
% 43.37/6.01      inference(cnf_transformation,[],[f74]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_31,negated_conjecture,
% 43.37/6.01      ( v1_funct_1(sK8) ),
% 43.37/6.01      inference(cnf_transformation,[],[f67]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_617,plain,
% 43.37/6.01      ( ~ r2_hidden(X0,X1)
% 43.37/6.01      | ~ r2_hidden(X0,k1_relat_1(X2))
% 43.37/6.01      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 43.37/6.01      | ~ v1_relat_1(X2)
% 43.37/6.01      | sK8 != X2 ),
% 43.37/6.01      inference(resolution_lifted,[status(thm)],[c_10,c_31]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_618,plain,
% 43.37/6.01      ( ~ r2_hidden(X0,X1)
% 43.37/6.01      | ~ r2_hidden(X0,k1_relat_1(sK8))
% 43.37/6.01      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
% 43.37/6.01      | ~ v1_relat_1(sK8) ),
% 43.37/6.01      inference(unflattening,[status(thm)],[c_617]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1745,plain,
% 43.37/6.01      ( r2_hidden(X0,X1) != iProver_top
% 43.37/6.01      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 43.37/6.01      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
% 43.37/6.01      | v1_relat_1(sK8) != iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_618]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_14,plain,
% 43.37/6.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.37/6.01      | v1_relat_1(X0) ),
% 43.37/6.01      inference(cnf_transformation,[],[f55]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_438,plain,
% 43.37/6.01      ( v1_relat_1(X0)
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK8 != X0 ),
% 43.37/6.01      inference(resolution_lifted,[status(thm)],[c_14,c_29]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_439,plain,
% 43.37/6.01      ( v1_relat_1(sK8)
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 43.37/6.01      inference(unflattening,[status(thm)],[c_438]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2016,plain,
% 43.37/6.01      ( v1_relat_1(sK8)
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_439]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2040,plain,
% 43.37/6.01      ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1))
% 43.37/6.01      | ~ r2_hidden(X0,k1_relat_1(sK8))
% 43.37/6.01      | ~ r2_hidden(X0,X1) ),
% 43.37/6.01      inference(global_propositional_subsumption,
% 43.37/6.01                [status(thm)],
% 43.37/6.01                [c_618,c_2013,c_2016]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2041,plain,
% 43.37/6.01      ( ~ r2_hidden(X0,X1)
% 43.37/6.01      | ~ r2_hidden(X0,k1_relat_1(sK8))
% 43.37/6.01      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) ),
% 43.37/6.01      inference(renaming,[status(thm)],[c_2040]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2042,plain,
% 43.37/6.01      ( r2_hidden(X0,X1) != iProver_top
% 43.37/6.01      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 43.37/6.01      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_2041]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3088,plain,
% 43.37/6.01      ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top
% 43.37/6.01      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 43.37/6.01      | r2_hidden(X0,X1) != iProver_top ),
% 43.37/6.01      inference(global_propositional_subsumption,
% 43.37/6.01                [status(thm)],
% 43.37/6.01                [c_1745,c_2042]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3089,plain,
% 43.37/6.01      ( r2_hidden(X0,X1) != iProver_top
% 43.37/6.01      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 43.37/6.01      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,X1)) = iProver_top ),
% 43.37/6.01      inference(renaming,[status(thm)],[c_3088]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3,plain,
% 43.37/6.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 43.37/6.01      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 43.37/6.01      | ~ v1_relat_1(X1) ),
% 43.37/6.01      inference(cnf_transformation,[],[f41]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1755,plain,
% 43.37/6.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 43.37/6.01      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 43.37/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2,plain,
% 43.37/6.01      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 43.37/6.01      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 43.37/6.01      | ~ v1_relat_1(X1) ),
% 43.37/6.01      inference(cnf_transformation,[],[f42]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1756,plain,
% 43.37/6.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 43.37/6.01      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 43.37/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_0,plain,
% 43.37/6.01      ( ~ r2_hidden(X0,X1)
% 43.37/6.01      | r2_hidden(X2,k9_relat_1(X3,X1))
% 43.37/6.01      | ~ r2_hidden(X0,k1_relat_1(X3))
% 43.37/6.01      | ~ r2_hidden(k4_tarski(X0,X2),X3)
% 43.37/6.01      | ~ v1_relat_1(X3) ),
% 43.37/6.01      inference(cnf_transformation,[],[f44]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1758,plain,
% 43.37/6.01      ( r2_hidden(X0,X1) != iProver_top
% 43.37/6.01      | r2_hidden(X2,k9_relat_1(X3,X1)) = iProver_top
% 43.37/6.01      | r2_hidden(X0,k1_relat_1(X3)) != iProver_top
% 43.37/6.01      | r2_hidden(k4_tarski(X0,X2),X3) != iProver_top
% 43.37/6.01      | v1_relat_1(X3) != iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3028,plain,
% 43.37/6.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 43.37/6.01      | r2_hidden(X0,k9_relat_1(X1,X3)) = iProver_top
% 43.37/6.01      | r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
% 43.37/6.01      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) != iProver_top
% 43.37/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.37/6.01      inference(superposition,[status(thm)],[c_1756,c_1758]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_101,plain,
% 43.37/6.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 43.37/6.01      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 43.37/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_8324,plain,
% 43.37/6.01      ( r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
% 43.37/6.01      | r2_hidden(X0,k9_relat_1(X1,X3)) = iProver_top
% 43.37/6.01      | r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 43.37/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.37/6.01      inference(global_propositional_subsumption,
% 43.37/6.01                [status(thm)],
% 43.37/6.01                [c_3028,c_101]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_8325,plain,
% 43.37/6.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 43.37/6.01      | r2_hidden(X0,k9_relat_1(X1,X3)) = iProver_top
% 43.37/6.01      | r2_hidden(sK0(X0,X2,X1),X3) != iProver_top
% 43.37/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.37/6.01      inference(renaming,[status(thm)],[c_8324]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_8333,plain,
% 43.37/6.01      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 43.37/6.01      | r2_hidden(X0,k9_relat_1(X1,k1_relat_1(X1))) = iProver_top
% 43.37/6.01      | v1_relat_1(X1) != iProver_top ),
% 43.37/6.01      inference(superposition,[status(thm)],[c_1755,c_8325]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_8566,plain,
% 43.37/6.01      ( r2_hidden(X0,X1) != iProver_top
% 43.37/6.01      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 43.37/6.01      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
% 43.37/6.01      | v1_relat_1(sK8) != iProver_top ),
% 43.37/6.01      inference(superposition,[status(thm)],[c_3089,c_8333]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2017,plain,
% 43.37/6.01      ( k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | v1_relat_1(sK8) = iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_2016]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_9309,plain,
% 43.37/6.01      ( r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
% 43.37/6.01      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 43.37/6.01      | r2_hidden(X0,X1) != iProver_top ),
% 43.37/6.01      inference(global_propositional_subsumption,
% 43.37/6.01                [status(thm)],
% 43.37/6.01                [c_8566,c_2013,c_2017]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_9310,plain,
% 43.37/6.01      ( r2_hidden(X0,X1) != iProver_top
% 43.37/6.01      | r2_hidden(X0,k1_relat_1(sK8)) != iProver_top
% 43.37/6.01      | r2_hidden(k1_funct_1(sK8,X0),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top ),
% 43.37/6.01      inference(renaming,[status(thm)],[c_9309]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_9321,plain,
% 43.37/6.01      ( r2_hidden(X0,sK7) != iProver_top
% 43.37/6.01      | r2_hidden(k1_funct_1(sK8,sK9(X0)),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
% 43.37/6.01      | r2_hidden(sK9(X0),k1_relat_1(sK8)) != iProver_top ),
% 43.37/6.01      inference(superposition,[status(thm)],[c_1753,c_9310]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_22914,plain,
% 43.37/6.01      ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
% 43.37/6.01      | r2_hidden(sK5(sK7,sK8),sK7) != iProver_top
% 43.37/6.01      | r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) != iProver_top ),
% 43.37/6.01      inference(superposition,[status(thm)],[c_22605,c_9321]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_24087,plain,
% 43.37/6.01      ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
% 43.37/6.01      | r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) != iProver_top ),
% 43.37/6.01      inference(global_propositional_subsumption,
% 43.37/6.01                [status(thm)],
% 43.37/6.01                [c_22914,c_26,c_2013,c_2107]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_18,plain,
% 43.37/6.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 43.37/6.01      | ~ r2_hidden(k4_tarski(X3,sK5(X2,X0)),X0)
% 43.37/6.01      | k2_relset_1(X1,X2,X0) = X2 ),
% 43.37/6.01      inference(cnf_transformation,[],[f59]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_387,plain,
% 43.37/6.01      ( ~ r2_hidden(k4_tarski(X0,sK5(X1,X2)),X2)
% 43.37/6.01      | k2_relset_1(X3,X1,X2) = X1
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X3,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK8 != X2 ),
% 43.37/6.01      inference(resolution_lifted,[status(thm)],[c_18,c_29]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_388,plain,
% 43.37/6.01      ( ~ r2_hidden(k4_tarski(X0,sK5(X1,sK8)),sK8)
% 43.37/6.01      | k2_relset_1(X2,X1,sK8) = X1
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 43.37/6.01      inference(unflattening,[status(thm)],[c_387]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1751,plain,
% 43.37/6.01      ( k2_relset_1(X0,X1,sK8) = X1
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | r2_hidden(k4_tarski(X2,sK5(X1,sK8)),sK8) != iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_388]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2754,plain,
% 43.37/6.01      ( k2_relset_1(sK6,sK7,sK8) = sK7
% 43.37/6.01      | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
% 43.37/6.01      inference(equality_resolution,[status(thm)],[c_1751]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2755,plain,
% 43.37/6.01      ( k2_relat_1(sK8) = sK7
% 43.37/6.01      | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
% 43.37/6.01      inference(demodulation,[status(thm)],[c_2754,c_1996]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2109,plain,
% 43.37/6.01      ( ~ r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8)
% 43.37/6.01      | k2_relset_1(sK6,sK7,sK8) = sK7
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_388]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2110,plain,
% 43.37/6.01      ( k2_relset_1(sK6,sK7,sK8) = sK7
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_2109]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_4405,plain,
% 43.37/6.01      ( r2_hidden(k4_tarski(X0,sK5(sK7,sK8)),sK8) != iProver_top ),
% 43.37/6.01      inference(global_propositional_subsumption,
% 43.37/6.01                [status(thm)],
% 43.37/6.01                [c_2755,c_26,c_2013,c_2110]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_4412,plain,
% 43.37/6.01      ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,X0)) != iProver_top
% 43.37/6.01      | v1_relat_1(sK8) != iProver_top ),
% 43.37/6.01      inference(superposition,[status(thm)],[c_1756,c_4405]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_6132,plain,
% 43.37/6.01      ( r2_hidden(sK5(sK7,sK8),k9_relat_1(sK8,X0)) != iProver_top ),
% 43.37/6.01      inference(global_propositional_subsumption,
% 43.37/6.01                [status(thm)],
% 43.37/6.01                [c_4412,c_2013,c_2017]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_24093,plain,
% 43.37/6.01      ( r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) != iProver_top ),
% 43.37/6.01      inference(forward_subsumption_resolution,
% 43.37/6.01                [status(thm)],
% 43.37/6.01                [c_24087,c_6132]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_24095,plain,
% 43.37/6.01      ( sK7 = k1_xboole_0
% 43.37/6.01      | r2_hidden(sK9(sK5(sK7,sK8)),sK6) != iProver_top ),
% 43.37/6.01      inference(superposition,[status(thm)],[c_2231,c_24093]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_24094,plain,
% 43.37/6.01      ( ~ r2_hidden(sK9(sK5(sK7,sK8)),k1_relat_1(sK8)) ),
% 43.37/6.01      inference(predicate_to_equality_rev,[status(thm)],[c_24093]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_14687,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) = k1_relset_1(sK6,sK7,sK8) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1401]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1408,plain,
% 43.37/6.01      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 43.37/6.01      theory(equality) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_12448,plain,
% 43.37/6.01      ( k2_relat_1(sK8) = k2_relat_1(X0) | sK8 != X0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1408]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_12450,plain,
% 43.37/6.01      ( k2_relat_1(sK8) = k2_relat_1(k1_xboole_0) | sK8 != k1_xboole_0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_12448]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3995,plain,
% 43.37/6.01      ( X0 != X1 | X0 = k2_relat_1(sK8) | k2_relat_1(sK8) != X1 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1402]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_12447,plain,
% 43.37/6.01      ( X0 != k2_relat_1(X1)
% 43.37/6.01      | X0 = k2_relat_1(sK8)
% 43.37/6.01      | k2_relat_1(sK8) != k2_relat_1(X1) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_3995]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_12449,plain,
% 43.37/6.01      ( k2_relat_1(sK8) != k2_relat_1(k1_xboole_0)
% 43.37/6.01      | k1_xboole_0 = k2_relat_1(sK8)
% 43.37/6.01      | k1_xboole_0 != k2_relat_1(k1_xboole_0) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_12447]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3725,plain,
% 43.37/6.01      ( X0 != X1 | X1 = X0 ),
% 43.37/6.01      inference(resolution,[status(thm)],[c_1402,c_1401]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2406,plain,
% 43.37/6.01      ( k1_relset_1(sK6,sK7,sK8) = k1_relat_1(sK8) ),
% 43.37/6.01      inference(resolution,[status(thm)],[c_430,c_1401]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_10209,plain,
% 43.37/6.01      ( k1_relat_1(sK8) = k1_relset_1(sK6,sK7,sK8) ),
% 43.37/6.01      inference(resolution,[status(thm)],[c_3725,c_2406]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1414,plain,
% 43.37/6.01      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 43.37/6.01      theory(equality) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_24,plain,
% 43.37/6.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 43.37/6.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 43.37/6.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 43.37/6.01      inference(cnf_transformation,[],[f82]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_485,plain,
% 43.37/6.01      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 43.37/6.01      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK8 != X0 ),
% 43.37/6.01      inference(resolution_lifted,[status(thm)],[c_24,c_29]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_486,plain,
% 43.37/6.01      ( ~ v1_funct_2(sK8,k1_xboole_0,X0)
% 43.37/6.01      | k1_relset_1(k1_xboole_0,X0,sK8) = k1_xboole_0
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 43.37/6.01      inference(unflattening,[status(thm)],[c_485]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1020,plain,
% 43.37/6.01      ( k1_relset_1(k1_xboole_0,X0,sK8) = k1_xboole_0
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK8 != sK8
% 43.37/6.01      | sK7 != X0
% 43.37/6.01      | sK6 != k1_xboole_0 ),
% 43.37/6.01      inference(resolution_lifted,[status(thm)],[c_30,c_486]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1021,plain,
% 43.37/6.01      ( k1_relset_1(k1_xboole_0,sK7,sK8) = k1_xboole_0
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK7)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK6 != k1_xboole_0 ),
% 43.37/6.01      inference(unflattening,[status(thm)],[c_1020]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2788,plain,
% 43.37/6.01      ( k1_relset_1(k1_xboole_0,sK7,sK8) = k1_xboole_0
% 43.37/6.01      | k2_zfmisc_1(k1_xboole_0,sK7) != k2_zfmisc_1(sK6,sK7)
% 43.37/6.01      | sK6 != k1_xboole_0 ),
% 43.37/6.01      inference(resolution,[status(thm)],[c_1414,c_1021]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1436,plain,
% 43.37/6.01      ( k1_xboole_0 = k1_xboole_0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1401]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2149,plain,
% 43.37/6.01      ( sK7 = sK7 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1401]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2219,plain,
% 43.37/6.01      ( sK6 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK6 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1402]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2220,plain,
% 43.37/6.01      ( sK6 != k1_xboole_0
% 43.37/6.01      | k1_xboole_0 = sK6
% 43.37/6.01      | k1_xboole_0 != k1_xboole_0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2219]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1413,plain,
% 43.37/6.01      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 43.37/6.01      theory(equality) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2178,plain,
% 43.37/6.01      ( X0 != sK7
% 43.37/6.01      | X1 != sK6
% 43.37/6.01      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK6,sK7) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1413]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2326,plain,
% 43.37/6.01      ( X0 != sK6
% 43.37/6.01      | k2_zfmisc_1(X0,sK7) = k2_zfmisc_1(sK6,sK7)
% 43.37/6.01      | sK7 != sK7 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2178]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2327,plain,
% 43.37/6.01      ( k2_zfmisc_1(k1_xboole_0,sK7) = k2_zfmisc_1(sK6,sK7)
% 43.37/6.01      | sK7 != sK7
% 43.37/6.01      | k1_xboole_0 != sK6 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2326]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3960,plain,
% 43.37/6.01      ( k1_relset_1(k1_xboole_0,sK7,sK8) = k1_xboole_0
% 43.37/6.01      | sK6 != k1_xboole_0 ),
% 43.37/6.01      inference(global_propositional_subsumption,
% 43.37/6.01                [status(thm)],
% 43.37/6.01                [c_2788,c_1436,c_2149,c_2220,c_2327]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_10200,plain,
% 43.37/6.01      ( sK6 != k1_xboole_0
% 43.37/6.01      | k1_xboole_0 = k1_relset_1(k1_xboole_0,sK7,sK8) ),
% 43.37/6.01      inference(resolution,[status(thm)],[c_3725,c_3960]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_4,plain,
% 43.37/6.01      ( k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 43.37/6.01      inference(cnf_transformation,[],[f46]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_10168,plain,
% 43.37/6.01      ( k1_xboole_0 = k2_relat_1(k1_xboole_0) ),
% 43.37/6.01      inference(resolution,[status(thm)],[c_3725,c_4]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2021,plain,
% 43.37/6.01      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK6,sK7)
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1414]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_7797,plain,
% 43.37/6.01      ( k2_zfmisc_1(sK6,k1_xboole_0) != k2_zfmisc_1(sK6,sK7)
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2021]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3074,plain,
% 43.37/6.01      ( sK8 = sK8 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1401]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2532,plain,
% 43.37/6.01      ( X0 != X1
% 43.37/6.01      | k2_relset_1(sK6,sK7,sK8) != X1
% 43.37/6.01      | k2_relset_1(sK6,sK7,sK8) = X0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1402]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3054,plain,
% 43.37/6.01      ( X0 != k2_relat_1(sK8)
% 43.37/6.01      | k2_relset_1(sK6,sK7,sK8) = X0
% 43.37/6.01      | k2_relset_1(sK6,sK7,sK8) != k2_relat_1(sK8) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2532]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_3055,plain,
% 43.37/6.01      ( k2_relset_1(sK6,sK7,sK8) != k2_relat_1(sK8)
% 43.37/6.01      | k2_relset_1(sK6,sK7,sK8) = k1_xboole_0
% 43.37/6.01      | k1_xboole_0 != k2_relat_1(sK8) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_3054]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2937,plain,
% 43.37/6.01      ( sK9(sK5(sK7,sK8)) = sK9(sK5(sK7,sK8)) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1401]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2556,plain,
% 43.37/6.01      ( X0 != sK7
% 43.37/6.01      | k2_zfmisc_1(sK6,X0) = k2_zfmisc_1(sK6,sK7)
% 43.37/6.01      | sK6 != sK6 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2178]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2557,plain,
% 43.37/6.01      ( k2_zfmisc_1(sK6,k1_xboole_0) = k2_zfmisc_1(sK6,sK7)
% 43.37/6.01      | sK6 != sK6
% 43.37/6.01      | k1_xboole_0 != sK7 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2556]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2214,plain,
% 43.37/6.01      ( sK7 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK7 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1402]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2215,plain,
% 43.37/6.01      ( sK7 != k1_xboole_0
% 43.37/6.01      | k1_xboole_0 = sK7
% 43.37/6.01      | k1_xboole_0 != k1_xboole_0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2214]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2206,plain,
% 43.37/6.01      ( ~ r2_hidden(sK5(sK7,sK8),sK7)
% 43.37/6.01      | r2_hidden(sK9(sK5(sK7,sK8)),sK6) ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_28]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2207,plain,
% 43.37/6.01      ( r2_hidden(sK5(sK7,sK8),sK7) != iProver_top
% 43.37/6.01      | r2_hidden(sK9(sK5(sK7,sK8)),sK6) = iProver_top ),
% 43.37/6.01      inference(predicate_to_equality,[status(thm)],[c_2206]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2152,plain,
% 43.37/6.01      ( sK6 = sK6 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1401]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2032,plain,
% 43.37/6.01      ( sK6 != X0 | sK6 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1402]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2151,plain,
% 43.37/6.01      ( sK6 != sK6 | sK6 = k1_xboole_0 | k1_xboole_0 != sK6 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2032]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2025,plain,
% 43.37/6.01      ( k2_relset_1(sK6,sK7,sK8) != X0
% 43.37/6.01      | k2_relset_1(sK6,sK7,sK8) = sK7
% 43.37/6.01      | sK7 != X0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_1402]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_2026,plain,
% 43.37/6.01      ( k2_relset_1(sK6,sK7,sK8) = sK7
% 43.37/6.01      | k2_relset_1(sK6,sK7,sK8) != k1_xboole_0
% 43.37/6.01      | sK7 != k1_xboole_0 ),
% 43.37/6.01      inference(instantiation,[status(thm)],[c_2025]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_21,plain,
% 43.37/6.01      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 43.37/6.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 43.37/6.01      | k1_xboole_0 = X1
% 43.37/6.01      | k1_xboole_0 = X0 ),
% 43.37/6.01      inference(cnf_transformation,[],[f80]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_467,plain,
% 43.37/6.01      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK8 != X0
% 43.37/6.01      | k1_xboole_0 = X0
% 43.37/6.01      | k1_xboole_0 = X1 ),
% 43.37/6.01      inference(resolution_lifted,[status(thm)],[c_21,c_29]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_468,plain,
% 43.37/6.01      ( ~ v1_funct_2(sK8,X0,k1_xboole_0)
% 43.37/6.01      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | k1_xboole_0 = X0
% 43.37/6.01      | k1_xboole_0 = sK8 ),
% 43.37/6.01      inference(unflattening,[status(thm)],[c_467]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1006,plain,
% 43.37/6.01      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK8 != sK8
% 43.37/6.01      | sK8 = k1_xboole_0
% 43.37/6.01      | sK7 != k1_xboole_0
% 43.37/6.01      | sK6 != X0
% 43.37/6.01      | k1_xboole_0 = X0 ),
% 43.37/6.01      inference(resolution_lifted,[status(thm)],[c_30,c_468]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(c_1007,plain,
% 43.37/6.01      ( k1_zfmisc_1(k2_zfmisc_1(sK6,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))
% 43.37/6.01      | sK8 = k1_xboole_0
% 43.37/6.01      | sK7 != k1_xboole_0
% 43.37/6.01      | k1_xboole_0 = sK6 ),
% 43.37/6.01      inference(unflattening,[status(thm)],[c_1006]) ).
% 43.37/6.01  
% 43.37/6.01  cnf(contradiction,plain,
% 43.37/6.01      ( $false ),
% 43.37/6.01      inference(minisat,
% 43.37/6.01                [status(thm)],
% 43.37/6.01                [c_136101,c_114879,c_78063,c_62514,c_60019,c_41271,
% 43.37/6.01                 c_24095,c_24094,c_14687,c_12450,c_12449,c_10209,c_10200,
% 43.37/6.01                 c_10168,c_7797,c_3074,c_3055,c_2937,c_2557,c_2215,
% 43.37/6.01                 c_2207,c_2206,c_2152,c_2151,c_2149,c_2107,c_2106,c_2026,
% 43.37/6.01                 c_2013,c_1996,c_1436,c_1007,c_26]) ).
% 43.37/6.01  
% 43.37/6.01  
% 43.37/6.01  % SZS output end CNFRefutation for theBenchmark.p
% 43.37/6.01  
% 43.37/6.01  ------                               Statistics
% 43.37/6.01  
% 43.37/6.01  ------ Selected
% 43.37/6.01  
% 43.37/6.01  total_time:                             5.078
% 43.37/6.01  
%------------------------------------------------------------------------------
