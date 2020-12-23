%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:04 EST 2020

% Result     : Theorem 3.14s
% Output     : CNFRefutation 3.14s
% Verified   : 
% Statistics : Number of formulae       :  129 ( 386 expanded)
%              Number of clauses        :   63 ( 118 expanded)
%              Number of leaves         :   19 (  96 expanded)
%              Depth                    :   22
%              Number of atoms          :  493 (2041 expanded)
%              Number of equality atoms :  179 ( 505 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f13,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,negated_conjecture,(
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
    inference(negated_conjecture,[],[f13])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK9
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,
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
              ( k1_funct_1(sK8,X5) != X4
              | ~ r2_hidden(X5,sK7)
              | ~ m1_subset_1(X5,sK5) )
          & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7)) )
      & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK8,sK5,sK6)
      & v1_funct_1(sK8) ) ),
    introduced(choice_axiom,[])).

fof(f47,plain,
    ( ! [X5] :
        ( k1_funct_1(sK8,X5) != sK9
        | ~ r2_hidden(X5,sK7)
        | ~ m1_subset_1(X5,sK5) )
    & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f28,f46,f45])).

fof(f81,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f47])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f72,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f82,plain,(
    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f47])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f17])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f36,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f48,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f39,plain,(
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
    inference(rectify,[],[f38])).

fof(f42,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
        & r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
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
              ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK2(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK2(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK2(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK2(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK2(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2)
                  & r2_hidden(sK3(X0,X1,X2),X1)
                  & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK2(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
                    & r2_hidden(sK4(X0,X1,X6),X1)
                    & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).

fof(f61,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f87,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f61])).

fof(f12,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f12])).

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
    inference(flattening,[],[f25])).

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
    inference(nnf_transformation,[],[f26])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f80,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f47])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f60,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f88,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f60])).

fof(f79,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f47])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f62,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f86,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f62])).

fof(f83,plain,(
    ! [X5] :
      ( k1_funct_1(sK8,X5) != sK9
      | ~ r2_hidden(X5,sK7)
      | ~ m1_subset_1(X5,sK5) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f7,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f50,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f49,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_1048,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1057,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2484,plain,
    ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(superposition,[status(thm)],[c_1048,c_1057])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1049,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2708,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2484,c_1049])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1071,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1079,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_4274,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1071,c_1079])).

cnf(c_8518,plain,
    ( v1_relat_1(sK8) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2708,c_4274])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1063,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1051,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1561,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_1051])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1562,plain,
    ( ~ v1_funct_2(sK8,sK5,sK6)
    | k1_relset_1(sK5,sK6,sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1561])).

cnf(c_1917,plain,
    ( sK6 = k1_xboole_0
    | k1_relset_1(sK5,sK6,sK8) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1561,c_34,c_1562])).

cnf(c_1918,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1917])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1058,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2083,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1048,c_1058])).

cnf(c_2085,plain,
    ( k1_relat_1(sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1918,c_2083])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1062,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4583,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2085,c_1062])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_36,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1419,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_21])).

cnf(c_1420,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1419])).

cnf(c_5084,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4583,c_36,c_38,c_1420])).

cnf(c_7,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1074,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_5094,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK4(sK8,X0,X1),sK5) = iProver_top
    | r2_hidden(X1,k9_relat_1(sK8,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5084,c_1074])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1064,plain,
    ( k1_funct_1(X0,sK4(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4522,plain,
    ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2708,c_1064])).

cnf(c_4803,plain,
    ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4522,c_36,c_38,c_1420])).

cnf(c_31,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,X0) != sK9 ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1050,plain,
    ( k1_funct_1(sK8,X0) != sK9
    | m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4806,plain,
    ( m1_subset_1(sK4(sK8,sK7,sK9),sK5) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4803,c_1050])).

cnf(c_5199,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5094,c_4806])).

cnf(c_5212,plain,
    ( r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
    | sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5199,c_2708])).

cnf(c_5213,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
    inference(renaming,[status(thm)],[c_5212])).

cnf(c_5218,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1063,c_5213])).

cnf(c_6346,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5218,c_36,c_38,c_1420,c_2708])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1059,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_xboole_0(X2) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_3092,plain,
    ( v1_xboole_0(sK6) != iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1048,c_1059])).

cnf(c_6349,plain,
    ( v1_xboole_0(sK8) = iProver_top
    | v1_xboole_0(k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6346,c_3092])).

cnf(c_20,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_2,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_1579,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_2])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1834,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_1579,c_0])).

cnf(c_1835,plain,
    ( v1_xboole_0(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1834])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_8518,c_6349,c_1835,c_1420,c_38])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:19:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.14/1.03  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.14/1.03  
% 3.14/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.14/1.03  
% 3.14/1.03  ------  iProver source info
% 3.14/1.03  
% 3.14/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.14/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.14/1.03  git: non_committed_changes: false
% 3.14/1.03  git: last_make_outside_of_git: false
% 3.14/1.03  
% 3.14/1.03  ------ 
% 3.14/1.03  ------ Parsing...
% 3.14/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.14/1.03  
% 3.14/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.14/1.03  
% 3.14/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.14/1.03  
% 3.14/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.14/1.03  ------ Proving...
% 3.14/1.03  ------ Problem Properties 
% 3.14/1.03  
% 3.14/1.03  
% 3.14/1.03  clauses                                 35
% 3.14/1.03  conjectures                             5
% 3.14/1.03  EPR                                     9
% 3.14/1.03  Horn                                    26
% 3.14/1.03  unary                                   5
% 3.14/1.03  binary                                  7
% 3.14/1.03  lits                                    108
% 3.14/1.03  lits eq                                 19
% 3.14/1.03  fd_pure                                 0
% 3.14/1.03  fd_pseudo                               0
% 3.14/1.03  fd_cond                                 3
% 3.14/1.03  fd_pseudo_cond                          4
% 3.14/1.03  AC symbols                              0
% 3.14/1.03  
% 3.14/1.03  ------ Input Options Time Limit: Unbounded
% 3.14/1.03  
% 3.14/1.03  
% 3.14/1.03  ------ 
% 3.14/1.03  Current options:
% 3.14/1.03  ------ 
% 3.14/1.03  
% 3.14/1.03  
% 3.14/1.03  
% 3.14/1.03  
% 3.14/1.03  ------ Proving...
% 3.14/1.03  
% 3.14/1.03  
% 3.14/1.03  % SZS status Theorem for theBenchmark.p
% 3.14/1.03  
% 3.14/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.14/1.03  
% 3.14/1.03  fof(f13,conjecture,(
% 3.14/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.03  
% 3.14/1.03  fof(f14,negated_conjecture,(
% 3.14/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.14/1.03    inference(negated_conjecture,[],[f13])).
% 3.14/1.03  
% 3.14/1.03  fof(f27,plain,(
% 3.14/1.03    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.14/1.03    inference(ennf_transformation,[],[f14])).
% 3.14/1.03  
% 3.14/1.03  fof(f28,plain,(
% 3.14/1.03    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.14/1.03    inference(flattening,[],[f27])).
% 3.14/1.03  
% 3.14/1.03  fof(f46,plain,(
% 3.14/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK9 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.14/1.03    introduced(choice_axiom,[])).
% 3.14/1.03  
% 3.14/1.03  fof(f45,plain,(
% 3.14/1.03    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK8,X5) != X4 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8))),
% 3.14/1.03    introduced(choice_axiom,[])).
% 3.14/1.03  
% 3.14/1.03  fof(f47,plain,(
% 3.14/1.03    (! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)),
% 3.14/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f28,f46,f45])).
% 3.14/1.03  
% 3.14/1.03  fof(f81,plain,(
% 3.14/1.03    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 3.14/1.03    inference(cnf_transformation,[],[f47])).
% 3.14/1.03  
% 3.14/1.03  fof(f11,axiom,(
% 3.14/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.03  
% 3.14/1.03  fof(f24,plain,(
% 3.14/1.03    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.03    inference(ennf_transformation,[],[f11])).
% 3.14/1.03  
% 3.14/1.03  fof(f72,plain,(
% 3.14/1.03    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.03    inference(cnf_transformation,[],[f24])).
% 3.14/1.03  
% 3.14/1.03  fof(f82,plain,(
% 3.14/1.03    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))),
% 3.14/1.03    inference(cnf_transformation,[],[f47])).
% 3.14/1.03  
% 3.14/1.03  fof(f5,axiom,(
% 3.14/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.03  
% 3.14/1.03  fof(f17,plain,(
% 3.14/1.03    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.14/1.03    inference(ennf_transformation,[],[f5])).
% 3.14/1.03  
% 3.14/1.03  fof(f34,plain,(
% 3.14/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.14/1.03    inference(nnf_transformation,[],[f17])).
% 3.14/1.03  
% 3.14/1.03  fof(f35,plain,(
% 3.14/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.14/1.03    inference(rectify,[],[f34])).
% 3.14/1.03  
% 3.14/1.03  fof(f36,plain,(
% 3.14/1.03    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 3.14/1.03    introduced(choice_axiom,[])).
% 3.14/1.03  
% 3.14/1.03  fof(f37,plain,(
% 3.14/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.14/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f35,f36])).
% 3.14/1.03  
% 3.14/1.03  fof(f57,plain,(
% 3.14/1.03    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.14/1.03    inference(cnf_transformation,[],[f37])).
% 3.14/1.03  
% 3.14/1.03  fof(f1,axiom,(
% 3.14/1.03    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 3.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.03  
% 3.14/1.03  fof(f29,plain,(
% 3.14/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 3.14/1.03    inference(nnf_transformation,[],[f1])).
% 3.14/1.03  
% 3.14/1.03  fof(f30,plain,(
% 3.14/1.03    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.14/1.03    inference(rectify,[],[f29])).
% 3.14/1.03  
% 3.14/1.03  fof(f31,plain,(
% 3.14/1.03    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 3.14/1.03    introduced(choice_axiom,[])).
% 3.14/1.03  
% 3.14/1.03  fof(f32,plain,(
% 3.14/1.03    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 3.14/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 3.14/1.03  
% 3.14/1.03  fof(f48,plain,(
% 3.14/1.03    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 3.14/1.03    inference(cnf_transformation,[],[f32])).
% 3.14/1.03  
% 3.14/1.03  fof(f6,axiom,(
% 3.14/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 3.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.03  
% 3.14/1.03  fof(f18,plain,(
% 3.14/1.03    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.14/1.03    inference(ennf_transformation,[],[f6])).
% 3.14/1.03  
% 3.14/1.03  fof(f19,plain,(
% 3.14/1.03    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/1.03    inference(flattening,[],[f18])).
% 3.14/1.03  
% 3.14/1.03  fof(f38,plain,(
% 3.14/1.03    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/1.03    inference(nnf_transformation,[],[f19])).
% 3.14/1.03  
% 3.14/1.03  fof(f39,plain,(
% 3.14/1.03    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/1.03    inference(rectify,[],[f38])).
% 3.14/1.03  
% 3.14/1.03  fof(f42,plain,(
% 3.14/1.03    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 & r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))))),
% 3.14/1.03    introduced(choice_axiom,[])).
% 3.14/1.03  
% 3.14/1.03  fof(f41,plain,(
% 3.14/1.03    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))))) )),
% 3.14/1.03    introduced(choice_axiom,[])).
% 3.14/1.03  
% 3.14/1.03  fof(f40,plain,(
% 3.14/1.03    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK2(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK2(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 3.14/1.03    introduced(choice_axiom,[])).
% 3.14/1.03  
% 3.14/1.03  fof(f43,plain,(
% 3.14/1.03    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK2(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X1,X6)) = X6 & r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.14/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f39,f42,f41,f40])).
% 3.14/1.03  
% 3.14/1.03  fof(f61,plain,(
% 3.14/1.03    ( ! [X6,X2,X0,X1] : (r2_hidden(sK4(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.03    inference(cnf_transformation,[],[f43])).
% 3.14/1.03  
% 3.14/1.03  fof(f87,plain,(
% 3.14/1.03    ( ! [X6,X0,X1] : (r2_hidden(sK4(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.03    inference(equality_resolution,[],[f61])).
% 3.14/1.03  
% 3.14/1.03  fof(f12,axiom,(
% 3.14/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.03  
% 3.14/1.03  fof(f25,plain,(
% 3.14/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.03    inference(ennf_transformation,[],[f12])).
% 3.14/1.03  
% 3.14/1.03  fof(f26,plain,(
% 3.14/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.03    inference(flattening,[],[f25])).
% 3.14/1.03  
% 3.14/1.03  fof(f44,plain,(
% 3.14/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.03    inference(nnf_transformation,[],[f26])).
% 3.14/1.03  
% 3.14/1.03  fof(f73,plain,(
% 3.14/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.03    inference(cnf_transformation,[],[f44])).
% 3.14/1.03  
% 3.14/1.03  fof(f80,plain,(
% 3.14/1.03    v1_funct_2(sK8,sK5,sK6)),
% 3.14/1.03    inference(cnf_transformation,[],[f47])).
% 3.14/1.03  
% 3.14/1.03  fof(f10,axiom,(
% 3.14/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.03  
% 3.14/1.03  fof(f23,plain,(
% 3.14/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.03    inference(ennf_transformation,[],[f10])).
% 3.14/1.03  
% 3.14/1.03  fof(f71,plain,(
% 3.14/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.03    inference(cnf_transformation,[],[f23])).
% 3.14/1.03  
% 3.14/1.03  fof(f60,plain,(
% 3.14/1.03    ( ! [X6,X2,X0,X1] : (r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.03    inference(cnf_transformation,[],[f43])).
% 3.14/1.03  
% 3.14/1.03  fof(f88,plain,(
% 3.14/1.03    ( ! [X6,X0,X1] : (r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.03    inference(equality_resolution,[],[f60])).
% 3.14/1.03  
% 3.14/1.03  fof(f79,plain,(
% 3.14/1.03    v1_funct_1(sK8)),
% 3.14/1.03    inference(cnf_transformation,[],[f47])).
% 3.14/1.03  
% 3.14/1.03  fof(f8,axiom,(
% 3.14/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.03  
% 3.14/1.03  fof(f21,plain,(
% 3.14/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.14/1.03    inference(ennf_transformation,[],[f8])).
% 3.14/1.03  
% 3.14/1.03  fof(f69,plain,(
% 3.14/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.14/1.03    inference(cnf_transformation,[],[f21])).
% 3.14/1.03  
% 3.14/1.03  fof(f4,axiom,(
% 3.14/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.03  
% 3.14/1.03  fof(f16,plain,(
% 3.14/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.14/1.03    inference(ennf_transformation,[],[f4])).
% 3.14/1.03  
% 3.14/1.03  fof(f55,plain,(
% 3.14/1.03    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.14/1.03    inference(cnf_transformation,[],[f16])).
% 3.14/1.03  
% 3.14/1.03  fof(f62,plain,(
% 3.14/1.03    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.03    inference(cnf_transformation,[],[f43])).
% 3.14/1.03  
% 3.14/1.03  fof(f86,plain,(
% 3.14/1.03    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.14/1.03    inference(equality_resolution,[],[f62])).
% 3.14/1.03  
% 3.14/1.03  fof(f83,plain,(
% 3.14/1.03    ( ! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) )),
% 3.14/1.03    inference(cnf_transformation,[],[f47])).
% 3.14/1.03  
% 3.14/1.03  fof(f9,axiom,(
% 3.14/1.03    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 3.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.03  
% 3.14/1.03  fof(f22,plain,(
% 3.14/1.03    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 3.14/1.03    inference(ennf_transformation,[],[f9])).
% 3.14/1.03  
% 3.14/1.03  fof(f70,plain,(
% 3.14/1.03    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 3.14/1.03    inference(cnf_transformation,[],[f22])).
% 3.14/1.03  
% 3.14/1.03  fof(f7,axiom,(
% 3.14/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.03  
% 3.14/1.03  fof(f20,plain,(
% 3.14/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.14/1.03    inference(ennf_transformation,[],[f7])).
% 3.14/1.03  
% 3.14/1.03  fof(f68,plain,(
% 3.14/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.14/1.03    inference(cnf_transformation,[],[f20])).
% 3.14/1.03  
% 3.14/1.03  fof(f2,axiom,(
% 3.14/1.03    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.14/1.03    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.14/1.03  
% 3.14/1.03  fof(f50,plain,(
% 3.14/1.03    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.14/1.03    inference(cnf_transformation,[],[f2])).
% 3.14/1.03  
% 3.14/1.03  fof(f49,plain,(
% 3.14/1.03    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 3.14/1.03    inference(cnf_transformation,[],[f32])).
% 3.14/1.03  
% 3.14/1.03  cnf(c_33,negated_conjecture,
% 3.14/1.03      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 3.14/1.03      inference(cnf_transformation,[],[f81]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1048,plain,
% 3.14/1.03      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_24,plain,
% 3.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.03      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.14/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1057,plain,
% 3.14/1.03      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.14/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2484,plain,
% 3.14/1.03      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_1048,c_1057]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_32,negated_conjecture,
% 3.14/1.03      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 3.14/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1049,plain,
% 3.14/1.03      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2708,plain,
% 3.14/1.03      ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 3.14/1.03      inference(demodulation,[status(thm)],[c_2484,c_1049]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_10,plain,
% 3.14/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.14/1.03      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 3.14/1.03      | ~ v1_relat_1(X1) ),
% 3.14/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1071,plain,
% 3.14/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.14/1.03      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 3.14/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1,plain,
% 3.14/1.03      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 3.14/1.03      inference(cnf_transformation,[],[f48]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1079,plain,
% 3.14/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.14/1.03      | v1_xboole_0(X1) != iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_4274,plain,
% 3.14/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.14/1.03      | v1_relat_1(X1) != iProver_top
% 3.14/1.03      | v1_xboole_0(X1) != iProver_top ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_1071,c_1079]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_8518,plain,
% 3.14/1.03      ( v1_relat_1(sK8) != iProver_top
% 3.14/1.03      | v1_xboole_0(sK8) != iProver_top ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_2708,c_4274]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_18,plain,
% 3.14/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.14/1.03      | r2_hidden(sK4(X1,X2,X0),X2)
% 3.14/1.03      | ~ v1_funct_1(X1)
% 3.14/1.03      | ~ v1_relat_1(X1) ),
% 3.14/1.03      inference(cnf_transformation,[],[f87]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1063,plain,
% 3.14/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.14/1.03      | r2_hidden(sK4(X1,X2,X0),X2) = iProver_top
% 3.14/1.03      | v1_funct_1(X1) != iProver_top
% 3.14/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_30,plain,
% 3.14/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.14/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.14/1.03      | k1_xboole_0 = X2 ),
% 3.14/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1051,plain,
% 3.14/1.03      ( k1_relset_1(X0,X1,X2) = X0
% 3.14/1.03      | k1_xboole_0 = X1
% 3.14/1.03      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.14/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1561,plain,
% 3.14/1.03      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 3.14/1.03      | sK6 = k1_xboole_0
% 3.14/1.03      | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_1048,c_1051]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_34,negated_conjecture,
% 3.14/1.03      ( v1_funct_2(sK8,sK5,sK6) ),
% 3.14/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1562,plain,
% 3.14/1.03      ( ~ v1_funct_2(sK8,sK5,sK6)
% 3.14/1.03      | k1_relset_1(sK5,sK6,sK8) = sK5
% 3.14/1.03      | sK6 = k1_xboole_0 ),
% 3.14/1.03      inference(predicate_to_equality_rev,[status(thm)],[c_1561]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1917,plain,
% 3.14/1.03      ( sK6 = k1_xboole_0 | k1_relset_1(sK5,sK6,sK8) = sK5 ),
% 3.14/1.03      inference(global_propositional_subsumption,
% 3.14/1.03                [status(thm)],
% 3.14/1.03                [c_1561,c_34,c_1562]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1918,plain,
% 3.14/1.03      ( k1_relset_1(sK5,sK6,sK8) = sK5 | sK6 = k1_xboole_0 ),
% 3.14/1.03      inference(renaming,[status(thm)],[c_1917]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_23,plain,
% 3.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.14/1.03      inference(cnf_transformation,[],[f71]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1058,plain,
% 3.14/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.14/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2083,plain,
% 3.14/1.03      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_1048,c_1058]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2085,plain,
% 3.14/1.03      ( k1_relat_1(sK8) = sK5 | sK6 = k1_xboole_0 ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_1918,c_2083]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_19,plain,
% 3.14/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.14/1.03      | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1))
% 3.14/1.03      | ~ v1_funct_1(X1)
% 3.14/1.03      | ~ v1_relat_1(X1) ),
% 3.14/1.03      inference(cnf_transformation,[],[f88]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1062,plain,
% 3.14/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.14/1.03      | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1)) = iProver_top
% 3.14/1.03      | v1_funct_1(X1) != iProver_top
% 3.14/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_4583,plain,
% 3.14/1.03      ( sK6 = k1_xboole_0
% 3.14/1.03      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.14/1.03      | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top
% 3.14/1.03      | v1_funct_1(sK8) != iProver_top
% 3.14/1.03      | v1_relat_1(sK8) != iProver_top ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_2085,c_1062]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_35,negated_conjecture,
% 3.14/1.03      ( v1_funct_1(sK8) ),
% 3.14/1.03      inference(cnf_transformation,[],[f79]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_36,plain,
% 3.14/1.03      ( v1_funct_1(sK8) = iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_38,plain,
% 3.14/1.03      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_21,plain,
% 3.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.03      | v1_relat_1(X0) ),
% 3.14/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1419,plain,
% 3.14/1.03      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 3.14/1.03      | v1_relat_1(sK8) ),
% 3.14/1.03      inference(instantiation,[status(thm)],[c_21]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1420,plain,
% 3.14/1.03      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 3.14/1.03      | v1_relat_1(sK8) = iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_1419]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_5084,plain,
% 3.14/1.03      ( sK6 = k1_xboole_0
% 3.14/1.03      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 3.14/1.03      | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top ),
% 3.14/1.03      inference(global_propositional_subsumption,
% 3.14/1.03                [status(thm)],
% 3.14/1.03                [c_4583,c_36,c_38,c_1420]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_7,plain,
% 3.14/1.03      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 3.14/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1074,plain,
% 3.14/1.03      ( m1_subset_1(X0,X1) = iProver_top
% 3.14/1.03      | r2_hidden(X0,X1) != iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_5094,plain,
% 3.14/1.03      ( sK6 = k1_xboole_0
% 3.14/1.03      | m1_subset_1(sK4(sK8,X0,X1),sK5) = iProver_top
% 3.14/1.03      | r2_hidden(X1,k9_relat_1(sK8,X0)) != iProver_top ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_5084,c_1074]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_17,plain,
% 3.14/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.14/1.03      | ~ v1_funct_1(X1)
% 3.14/1.03      | ~ v1_relat_1(X1)
% 3.14/1.03      | k1_funct_1(X1,sK4(X1,X2,X0)) = X0 ),
% 3.14/1.03      inference(cnf_transformation,[],[f86]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1064,plain,
% 3.14/1.03      ( k1_funct_1(X0,sK4(X0,X1,X2)) = X2
% 3.14/1.03      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 3.14/1.03      | v1_funct_1(X0) != iProver_top
% 3.14/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_4522,plain,
% 3.14/1.03      ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9
% 3.14/1.03      | v1_funct_1(sK8) != iProver_top
% 3.14/1.03      | v1_relat_1(sK8) != iProver_top ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_2708,c_1064]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_4803,plain,
% 3.14/1.03      ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9 ),
% 3.14/1.03      inference(global_propositional_subsumption,
% 3.14/1.03                [status(thm)],
% 3.14/1.03                [c_4522,c_36,c_38,c_1420]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_31,negated_conjecture,
% 3.14/1.03      ( ~ m1_subset_1(X0,sK5)
% 3.14/1.03      | ~ r2_hidden(X0,sK7)
% 3.14/1.03      | k1_funct_1(sK8,X0) != sK9 ),
% 3.14/1.03      inference(cnf_transformation,[],[f83]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1050,plain,
% 3.14/1.03      ( k1_funct_1(sK8,X0) != sK9
% 3.14/1.03      | m1_subset_1(X0,sK5) != iProver_top
% 3.14/1.03      | r2_hidden(X0,sK7) != iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_4806,plain,
% 3.14/1.03      ( m1_subset_1(sK4(sK8,sK7,sK9),sK5) != iProver_top
% 3.14/1.03      | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_4803,c_1050]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_5199,plain,
% 3.14/1.03      ( sK6 = k1_xboole_0
% 3.14/1.03      | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
% 3.14/1.03      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_5094,c_4806]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_5212,plain,
% 3.14/1.03      ( r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
% 3.14/1.03      | sK6 = k1_xboole_0 ),
% 3.14/1.03      inference(global_propositional_subsumption,
% 3.14/1.03                [status(thm)],
% 3.14/1.03                [c_5199,c_2708]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_5213,plain,
% 3.14/1.03      ( sK6 = k1_xboole_0
% 3.14/1.03      | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
% 3.14/1.03      inference(renaming,[status(thm)],[c_5212]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_5218,plain,
% 3.14/1.03      ( sK6 = k1_xboole_0
% 3.14/1.03      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 3.14/1.03      | v1_funct_1(sK8) != iProver_top
% 3.14/1.03      | v1_relat_1(sK8) != iProver_top ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_1063,c_5213]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_6346,plain,
% 3.14/1.03      ( sK6 = k1_xboole_0 ),
% 3.14/1.03      inference(global_propositional_subsumption,
% 3.14/1.03                [status(thm)],
% 3.14/1.03                [c_5218,c_36,c_38,c_1420,c_2708]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_22,plain,
% 3.14/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.14/1.03      | ~ v1_xboole_0(X2)
% 3.14/1.03      | v1_xboole_0(X0) ),
% 3.14/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1059,plain,
% 3.14/1.03      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.14/1.03      | v1_xboole_0(X2) != iProver_top
% 3.14/1.03      | v1_xboole_0(X0) = iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_3092,plain,
% 3.14/1.03      ( v1_xboole_0(sK6) != iProver_top
% 3.14/1.03      | v1_xboole_0(sK8) = iProver_top ),
% 3.14/1.03      inference(superposition,[status(thm)],[c_1048,c_1059]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_6349,plain,
% 3.14/1.03      ( v1_xboole_0(sK8) = iProver_top
% 3.14/1.03      | v1_xboole_0(k1_xboole_0) != iProver_top ),
% 3.14/1.03      inference(demodulation,[status(thm)],[c_6346,c_3092]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_20,plain,
% 3.14/1.03      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 3.14/1.03      inference(cnf_transformation,[],[f68]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_2,plain,
% 3.14/1.03      ( r1_tarski(k1_xboole_0,X0) ),
% 3.14/1.03      inference(cnf_transformation,[],[f50]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1579,plain,
% 3.14/1.03      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 3.14/1.03      inference(resolution,[status(thm)],[c_20,c_2]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_0,plain,
% 3.14/1.03      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 3.14/1.03      inference(cnf_transformation,[],[f49]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1834,plain,
% 3.14/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 3.14/1.03      inference(resolution,[status(thm)],[c_1579,c_0]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(c_1835,plain,
% 3.14/1.03      ( v1_xboole_0(k1_xboole_0) = iProver_top ),
% 3.14/1.03      inference(predicate_to_equality,[status(thm)],[c_1834]) ).
% 3.14/1.03  
% 3.14/1.03  cnf(contradiction,plain,
% 3.14/1.03      ( $false ),
% 3.14/1.03      inference(minisat,[status(thm)],[c_8518,c_6349,c_1835,c_1420,c_38]) ).
% 3.14/1.03  
% 3.14/1.03  
% 3.14/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.14/1.03  
% 3.14/1.03  ------                               Statistics
% 3.14/1.03  
% 3.14/1.03  ------ Selected
% 3.14/1.03  
% 3.14/1.03  total_time:                             0.341
% 3.14/1.03  
%------------------------------------------------------------------------------
