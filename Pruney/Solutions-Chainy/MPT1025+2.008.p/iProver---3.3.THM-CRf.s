%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:01 EST 2020

% Result     : Theorem 7.75s
% Output     : CNFRefutation 7.75s
% Verified   : 
% Statistics : Number of formulae       :  206 (6170 expanded)
%              Number of clauses        :  129 (1939 expanded)
%              Number of leaves         :   22 (1513 expanded)
%              Depth                    :   32
%              Number of atoms          :  728 (33994 expanded)
%              Number of equality atoms :  327 (9018 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14,conjecture,(
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

fof(f15,negated_conjecture,(
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
    inference(negated_conjecture,[],[f14])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f48,plain,(
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

fof(f47,plain,
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

fof(f49,plain,
    ( ! [X5] :
        ( k1_funct_1(sK8,X5) != sK9
        | ~ r2_hidden(X5,sK7)
        | ~ m1_subset_1(X5,sK5) )
    & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))
    & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK8,sK5,sK6)
    & v1_funct_1(sK8) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f30,f48,f47])).

fof(f83,plain,(
    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f49])).

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
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f82,plain,(
    v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f49])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f8,axiom,(
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

fof(f21,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

fof(f40,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f41,plain,(
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
    inference(rectify,[],[f40])).

fof(f44,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
        & r2_hidden(sK4(X0,X1,X6),X1)
        & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X2)) = X3
        & r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,(
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

fof(f45,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f44,f43,f42])).

fof(f63,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f90,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f81,plain,(
    v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f49])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f17])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f84,plain,(
    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f49])).

fof(f65,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f88,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK4(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f85,plain,(
    ! [X5] :
      ( k1_funct_1(sK8,X5) != sK9
      | ~ r2_hidden(X5,sK7)
      | ~ m1_subset_1(X5,sK5) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f64,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f89,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK4(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f64])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f31])).

fof(f33,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f93,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f79])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f95,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f76])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f37,plain,(
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
    inference(rectify,[],[f36])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f9,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK1(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X6,X2,X0,X7,X1] :
      ( r2_hidden(X6,X2)
      | k1_funct_1(X0,X7) != X6
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f86,plain,(
    ! [X2,X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),X2)
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f87,plain,(
    ! [X0,X7,X1] :
      ( r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1))
      | ~ r2_hidden(X7,X1)
      | ~ r2_hidden(X7,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f86])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_33,negated_conjecture,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f83])).

cnf(c_1198,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_30,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1201,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_1716,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | sK6 = k1_xboole_0
    | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1198,c_1201])).

cnf(c_34,negated_conjecture,
    ( v1_funct_2(sK8,sK5,sK6) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1717,plain,
    ( ~ v1_funct_2(sK8,sK5,sK6)
    | k1_relset_1(sK5,sK6,sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1716])).

cnf(c_2280,plain,
    ( sK6 = k1_xboole_0
    | k1_relset_1(sK5,sK6,sK8) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1716,c_34,c_1717])).

cnf(c_2281,plain,
    ( k1_relset_1(sK5,sK6,sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2280])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_1208,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_2594,plain,
    ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
    inference(superposition,[status(thm)],[c_1198,c_1208])).

cnf(c_2985,plain,
    ( k1_relat_1(sK8) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2281,c_2594])).

cnf(c_20,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1211,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_4902,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_1211])).

cnf(c_35,negated_conjecture,
    ( v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_36,plain,
    ( v1_funct_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_38,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_33])).

cnf(c_22,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1568,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_22])).

cnf(c_1569,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1568])).

cnf(c_5105,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4902,c_36,c_38,c_1569])).

cnf(c_4,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1226,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_6,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_1224,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_3422,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X2) != iProver_top
    | r1_tarski(X2,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1226,c_1224])).

cnf(c_11052,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK4(sK8,X0,X1),X2) = iProver_top
    | r2_hidden(X1,k9_relat_1(sK8,X0)) != iProver_top
    | r1_tarski(sK5,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_5105,c_3422])).

cnf(c_24,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1207,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_2608,plain,
    ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
    inference(superposition,[status(thm)],[c_1198,c_1207])).

cnf(c_32,negated_conjecture,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1199,plain,
    ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_2989,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2608,c_1199])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK4(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1213,plain,
    ( k1_funct_1(X0,sK4(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4653,plain,
    ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_2989,c_1213])).

cnf(c_4939,plain,
    ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4653,c_36,c_38,c_1569])).

cnf(c_31,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | ~ r2_hidden(X0,sK7)
    | k1_funct_1(sK8,X0) != sK9 ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1200,plain,
    ( k1_funct_1(sK8,X0) != sK9
    | m1_subset_1(X0,sK5) != iProver_top
    | r2_hidden(X0,sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_4942,plain,
    ( m1_subset_1(sK4(sK8,sK7,sK9),sK5) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_4939,c_1200])).

cnf(c_12378,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_11052,c_4942])).

cnf(c_19,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK4(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_2105,plain,
    ( r2_hidden(sK4(X0,X1,sK9),X1)
    | ~ r2_hidden(sK9,k9_relat_1(X0,X1))
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_19])).

cnf(c_3175,plain,
    ( r2_hidden(sK4(sK8,X0,sK9),X0)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,X0))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_2105])).

cnf(c_10590,plain,
    ( r2_hidden(sK4(sK8,sK7,sK9),sK7)
    | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
    | ~ v1_funct_1(sK8)
    | ~ v1_relat_1(sK8) ),
    inference(instantiation,[status(thm)],[c_3175])).

cnf(c_10592,plain,
    ( r2_hidden(sK4(sK8,sK7,sK9),sK7) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10590])).

cnf(c_12632,plain,
    ( sK6 = k1_xboole_0
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12378,c_36,c_38,c_1569,c_2989,c_10592])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1229,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_1230,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_2418,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_1230])).

cnf(c_12638,plain,
    ( sK6 = k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12632,c_2418])).

cnf(c_12653,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12638,c_1198])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f93])).

cnf(c_1205,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_12991,plain,
    ( sK5 = k1_xboole_0
    | sK8 = k1_xboole_0
    | v1_funct_2(sK8,sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_12653,c_1205])).

cnf(c_37,plain,
    ( v1_funct_2(sK8,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_408,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_435,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_408])).

cnf(c_1896,plain,
    ( sK8 = sK8 ),
    inference(instantiation,[status(thm)],[c_408])).

cnf(c_421,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1686,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK8,sK5,sK6)
    | X2 != sK6
    | X1 != sK5
    | X0 != sK8 ),
    inference(instantiation,[status(thm)],[c_421])).

cnf(c_1895,plain,
    ( v1_funct_2(sK8,X0,X1)
    | ~ v1_funct_2(sK8,sK5,sK6)
    | X1 != sK6
    | X0 != sK5
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_1686])).

cnf(c_2344,plain,
    ( v1_funct_2(sK8,sK5,X0)
    | ~ v1_funct_2(sK8,sK5,sK6)
    | X0 != sK6
    | sK5 != sK5
    | sK8 != sK8 ),
    inference(instantiation,[status(thm)],[c_1895])).

cnf(c_2346,plain,
    ( X0 != sK6
    | sK5 != sK5
    | sK8 != sK8
    | v1_funct_2(sK8,sK5,X0) = iProver_top
    | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2344])).

cnf(c_2348,plain,
    ( sK5 != sK5
    | sK8 != sK8
    | k1_xboole_0 != sK6
    | v1_funct_2(sK8,sK5,sK6) != iProver_top
    | v1_funct_2(sK8,sK5,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_2346])).

cnf(c_2345,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_408])).

cnf(c_409,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_3385,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_409])).

cnf(c_3386,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3385])).

cnf(c_13146,plain,
    ( sK8 = k1_xboole_0
    | sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12991,c_37,c_435,c_1896,c_2348,c_2345,c_3386,c_12638])).

cnf(c_13147,plain,
    ( sK5 = k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_13146])).

cnf(c_13150,plain,
    ( sK8 = k1_xboole_0
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_13147,c_12653])).

cnf(c_29,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1202,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_14622,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
    | sK8 = k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_13150,c_1202])).

cnf(c_1197,plain,
    ( v1_funct_2(sK8,sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_12654,plain,
    ( v1_funct_2(sK8,sK5,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_12638,c_1197])).

cnf(c_13151,plain,
    ( sK8 = k1_xboole_0
    | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_13147,c_12654])).

cnf(c_15086,plain,
    ( sK8 = k1_xboole_0
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14622,c_13151])).

cnf(c_15087,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_15086])).

cnf(c_12650,plain,
    ( k1_relset_1(sK5,k1_xboole_0,sK8) = k1_relat_1(sK8) ),
    inference(demodulation,[status(thm)],[c_12638,c_2594])).

cnf(c_13489,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_relat_1(sK8)
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_13147,c_12650])).

cnf(c_15093,plain,
    ( k1_relat_1(sK8) = k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_15087,c_13489])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1219,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_21,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1210,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_3577,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X1),sK1(X0,X2,X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1219,c_1210])).

cnf(c_17423,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
    | r1_tarski(k1_xboole_0,sK1(X0,X1,sK8)) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_15093,c_3577])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1227,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK1(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1221,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3441,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(X2,sK1(X0,X2,X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1221,c_1210])).

cnf(c_15272,plain,
    ( r2_hidden(X0,k9_relat_1(X1,k1_xboole_0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_3441])).

cnf(c_15291,plain,
    ( r1_tarski(k9_relat_1(X0,k1_xboole_0),X1) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1229,c_15272])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r2_hidden(X0,k1_relat_1(X2))
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1214,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
    | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
    | v1_funct_1(X2) != iProver_top
    | v1_relat_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_5669,plain,
    ( r2_hidden(sK4(sK8,sK7,sK9),X0) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK9),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_4939,c_1214])).

cnf(c_6605,plain,
    ( r2_hidden(sK4(sK8,sK7,sK9),X0) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK9),k1_relat_1(sK8)) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5669,c_36,c_38,c_1569])).

cnf(c_6616,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4(sK8,sK7,sK9),X0) != iProver_top
    | r2_hidden(sK4(sK8,sK7,sK9),sK5) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_2985,c_6605])).

cnf(c_6614,plain,
    ( r2_hidden(sK4(sK8,sK7,sK9),X0) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_6605])).

cnf(c_6655,plain,
    ( r2_hidden(sK4(sK8,sK7,sK9),X0) != iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6616,c_36,c_38,c_1569,c_2989,c_6614])).

cnf(c_6664,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
    | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
    | v1_funct_1(sK8) != iProver_top
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_6655])).

cnf(c_7010,plain,
    ( r2_hidden(sK9,k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6664,c_36,c_38,c_1569,c_2989])).

cnf(c_7017,plain,
    ( r1_tarski(k9_relat_1(sK8,k1_relat_1(sK8)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_7010,c_1210])).

cnf(c_16063,plain,
    ( sK8 = k1_xboole_0
    | r1_tarski(k9_relat_1(sK8,k1_xboole_0),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_15093,c_7017])).

cnf(c_18063,plain,
    ( sK8 = k1_xboole_0
    | v1_relat_1(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_15291,c_16063])).

cnf(c_18684,plain,
    ( sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_17423,c_38,c_1569,c_18063])).

cnf(c_18714,plain,
    ( r2_hidden(sK9,k9_relat_1(k1_xboole_0,sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_18684,c_2989])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1220,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_4444,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(X1,k4_tarski(sK1(X0,X2,X1),X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1220,c_1210])).

cnf(c_17443,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1227,c_4444])).

cnf(c_1733,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_22,c_4])).

cnf(c_1734,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1733])).

cnf(c_1736,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1734])).

cnf(c_1789,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1790,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1789])).

cnf(c_1792,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1790])).

cnf(c_3625,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ r1_tarski(X1,k4_tarski(sK1(X0,X2,X1),X0))
    | ~ v1_relat_1(X1) ),
    inference(resolution,[status(thm)],[c_11,c_21])).

cnf(c_15106,plain,
    ( ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3625,c_3])).

cnf(c_15107,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15106])).

cnf(c_17951,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_17443,c_1736,c_1792,c_15107])).

cnf(c_20186,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_18714,c_17951])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:18:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 7.75/1.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.75/1.48  
% 7.75/1.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 7.75/1.48  
% 7.75/1.48  ------  iProver source info
% 7.75/1.48  
% 7.75/1.48  git: date: 2020-06-30 10:37:57 +0100
% 7.75/1.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 7.75/1.48  git: non_committed_changes: false
% 7.75/1.48  git: last_make_outside_of_git: false
% 7.75/1.48  
% 7.75/1.48  ------ 
% 7.75/1.48  ------ Parsing...
% 7.75/1.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 7.75/1.48  
% 7.75/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 7.75/1.48  
% 7.75/1.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 7.75/1.48  
% 7.75/1.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 7.75/1.48  ------ Proving...
% 7.75/1.48  ------ Problem Properties 
% 7.75/1.48  
% 7.75/1.48  
% 7.75/1.48  clauses                                 36
% 7.75/1.48  conjectures                             5
% 7.75/1.48  EPR                                     6
% 7.75/1.48  Horn                                    28
% 7.75/1.48  unary                                   6
% 7.75/1.48  binary                                  8
% 7.75/1.48  lits                                    108
% 7.75/1.48  lits eq                                 19
% 7.75/1.48  fd_pure                                 0
% 7.75/1.48  fd_pseudo                               0
% 7.75/1.48  fd_cond                                 3
% 7.75/1.48  fd_pseudo_cond                          4
% 7.75/1.48  AC symbols                              0
% 7.75/1.48  
% 7.75/1.48  ------ Input Options Time Limit: Unbounded
% 7.75/1.48  
% 7.75/1.48  
% 7.75/1.48  ------ 
% 7.75/1.48  Current options:
% 7.75/1.48  ------ 
% 7.75/1.48  
% 7.75/1.48  
% 7.75/1.48  
% 7.75/1.48  
% 7.75/1.48  ------ Proving...
% 7.75/1.48  
% 7.75/1.48  
% 7.75/1.48  % SZS status Theorem for theBenchmark.p
% 7.75/1.48  
% 7.75/1.48   Resolution empty clause
% 7.75/1.48  
% 7.75/1.48  % SZS output start CNFRefutation for theBenchmark.p
% 7.75/1.48  
% 7.75/1.48  fof(f14,conjecture,(
% 7.75/1.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.75/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.48  
% 7.75/1.48  fof(f15,negated_conjecture,(
% 7.75/1.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 7.75/1.48    inference(negated_conjecture,[],[f14])).
% 7.75/1.48  
% 7.75/1.48  fof(f29,plain,(
% 7.75/1.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 7.75/1.48    inference(ennf_transformation,[],[f15])).
% 7.75/1.48  
% 7.75/1.48  fof(f30,plain,(
% 7.75/1.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 7.75/1.48    inference(flattening,[],[f29])).
% 7.75/1.48  
% 7.75/1.48  fof(f48,plain,(
% 7.75/1.48    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK9 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK9,k7_relset_1(X0,X1,X3,X2)))) )),
% 7.75/1.48    introduced(choice_axiom,[])).
% 7.75/1.48  
% 7.75/1.48  fof(f47,plain,(
% 7.75/1.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK8,X5) != X4 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(X4,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8))),
% 7.75/1.48    introduced(choice_axiom,[])).
% 7.75/1.48  
% 7.75/1.48  fof(f49,plain,(
% 7.75/1.48    (! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) & r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))) & m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK8,sK5,sK6) & v1_funct_1(sK8)),
% 7.75/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8,sK9])],[f30,f48,f47])).
% 7.75/1.48  
% 7.75/1.48  fof(f83,plain,(
% 7.75/1.48    m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 7.75/1.48    inference(cnf_transformation,[],[f49])).
% 7.75/1.48  
% 7.75/1.48  fof(f13,axiom,(
% 7.75/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 7.75/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.48  
% 7.75/1.48  fof(f27,plain,(
% 7.75/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.48    inference(ennf_transformation,[],[f13])).
% 7.75/1.48  
% 7.75/1.48  fof(f28,plain,(
% 7.75/1.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.48    inference(flattening,[],[f27])).
% 7.75/1.48  
% 7.75/1.48  fof(f46,plain,(
% 7.75/1.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.48    inference(nnf_transformation,[],[f28])).
% 7.75/1.48  
% 7.75/1.48  fof(f75,plain,(
% 7.75/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.48    inference(cnf_transformation,[],[f46])).
% 7.75/1.48  
% 7.75/1.48  fof(f82,plain,(
% 7.75/1.48    v1_funct_2(sK8,sK5,sK6)),
% 7.75/1.48    inference(cnf_transformation,[],[f49])).
% 7.75/1.48  
% 7.75/1.48  fof(f11,axiom,(
% 7.75/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 7.75/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.48  
% 7.75/1.48  fof(f25,plain,(
% 7.75/1.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.48    inference(ennf_transformation,[],[f11])).
% 7.75/1.48  
% 7.75/1.48  fof(f73,plain,(
% 7.75/1.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.48    inference(cnf_transformation,[],[f25])).
% 7.75/1.48  
% 7.75/1.48  fof(f8,axiom,(
% 7.75/1.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 7.75/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.48  
% 7.75/1.48  fof(f21,plain,(
% 7.75/1.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 7.75/1.48    inference(ennf_transformation,[],[f8])).
% 7.75/1.48  
% 7.75/1.48  fof(f22,plain,(
% 7.75/1.48    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.75/1.48    inference(flattening,[],[f21])).
% 7.75/1.48  
% 7.75/1.48  fof(f40,plain,(
% 7.75/1.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.75/1.48    inference(nnf_transformation,[],[f22])).
% 7.75/1.48  
% 7.75/1.48  fof(f41,plain,(
% 7.75/1.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.75/1.48    inference(rectify,[],[f40])).
% 7.75/1.48  
% 7.75/1.48  fof(f44,plain,(
% 7.75/1.48    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 & r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))))),
% 7.75/1.48    introduced(choice_axiom,[])).
% 7.75/1.48  
% 7.75/1.48  fof(f43,plain,(
% 7.75/1.48    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X2)) = X3 & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))))) )),
% 7.75/1.48    introduced(choice_axiom,[])).
% 7.75/1.48  
% 7.75/1.48  fof(f42,plain,(
% 7.75/1.48    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK2(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK2(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2))))),
% 7.75/1.48    introduced(choice_axiom,[])).
% 7.75/1.48  
% 7.75/1.48  fof(f45,plain,(
% 7.75/1.48    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK2(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK2(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK3(X0,X1,X2)) = sK2(X0,X1,X2) & r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK2(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK4(X0,X1,X6)) = X6 & r2_hidden(sK4(X0,X1,X6),X1) & r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 7.75/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f41,f44,f43,f42])).
% 7.75/1.48  
% 7.75/1.48  fof(f63,plain,(
% 7.75/1.48    ( ! [X6,X2,X0,X1] : (r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f45])).
% 7.75/1.48  
% 7.75/1.48  fof(f90,plain,(
% 7.75/1.48    ( ! [X6,X0,X1] : (r2_hidden(sK4(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.75/1.48    inference(equality_resolution,[],[f63])).
% 7.75/1.48  
% 7.75/1.48  fof(f81,plain,(
% 7.75/1.48    v1_funct_1(sK8)),
% 7.75/1.48    inference(cnf_transformation,[],[f49])).
% 7.75/1.48  
% 7.75/1.48  fof(f10,axiom,(
% 7.75/1.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 7.75/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.48  
% 7.75/1.48  fof(f24,plain,(
% 7.75/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.48    inference(ennf_transformation,[],[f10])).
% 7.75/1.48  
% 7.75/1.48  fof(f72,plain,(
% 7.75/1.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.48    inference(cnf_transformation,[],[f24])).
% 7.75/1.48  
% 7.75/1.48  fof(f3,axiom,(
% 7.75/1.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 7.75/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.48  
% 7.75/1.48  fof(f35,plain,(
% 7.75/1.48    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 7.75/1.48    inference(nnf_transformation,[],[f3])).
% 7.75/1.48  
% 7.75/1.48  fof(f55,plain,(
% 7.75/1.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f35])).
% 7.75/1.48  
% 7.75/1.48  fof(f4,axiom,(
% 7.75/1.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 7.75/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.48  
% 7.75/1.48  fof(f17,plain,(
% 7.75/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 7.75/1.48    inference(ennf_transformation,[],[f4])).
% 7.75/1.48  
% 7.75/1.48  fof(f18,plain,(
% 7.75/1.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 7.75/1.48    inference(flattening,[],[f17])).
% 7.75/1.48  
% 7.75/1.48  fof(f56,plain,(
% 7.75/1.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f18])).
% 7.75/1.48  
% 7.75/1.48  fof(f12,axiom,(
% 7.75/1.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 7.75/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.48  
% 7.75/1.48  fof(f26,plain,(
% 7.75/1.48    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 7.75/1.48    inference(ennf_transformation,[],[f12])).
% 7.75/1.48  
% 7.75/1.48  fof(f74,plain,(
% 7.75/1.48    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.48    inference(cnf_transformation,[],[f26])).
% 7.75/1.48  
% 7.75/1.48  fof(f84,plain,(
% 7.75/1.48    r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7))),
% 7.75/1.48    inference(cnf_transformation,[],[f49])).
% 7.75/1.48  
% 7.75/1.48  fof(f65,plain,(
% 7.75/1.48    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f45])).
% 7.75/1.48  
% 7.75/1.48  fof(f88,plain,(
% 7.75/1.48    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK4(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.75/1.48    inference(equality_resolution,[],[f65])).
% 7.75/1.48  
% 7.75/1.48  fof(f85,plain,(
% 7.75/1.48    ( ! [X5] : (k1_funct_1(sK8,X5) != sK9 | ~r2_hidden(X5,sK7) | ~m1_subset_1(X5,sK5)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f49])).
% 7.75/1.48  
% 7.75/1.48  fof(f64,plain,(
% 7.75/1.48    ( ! [X6,X2,X0,X1] : (r2_hidden(sK4(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f45])).
% 7.75/1.48  
% 7.75/1.48  fof(f89,plain,(
% 7.75/1.48    ( ! [X6,X0,X1] : (r2_hidden(sK4(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.75/1.48    inference(equality_resolution,[],[f64])).
% 7.75/1.48  
% 7.75/1.48  fof(f1,axiom,(
% 7.75/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 7.75/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.48  
% 7.75/1.48  fof(f16,plain,(
% 7.75/1.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 7.75/1.48    inference(ennf_transformation,[],[f1])).
% 7.75/1.48  
% 7.75/1.48  fof(f31,plain,(
% 7.75/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 7.75/1.48    inference(nnf_transformation,[],[f16])).
% 7.75/1.48  
% 7.75/1.48  fof(f32,plain,(
% 7.75/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.75/1.48    inference(rectify,[],[f31])).
% 7.75/1.48  
% 7.75/1.48  fof(f33,plain,(
% 7.75/1.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 7.75/1.48    introduced(choice_axiom,[])).
% 7.75/1.48  
% 7.75/1.48  fof(f34,plain,(
% 7.75/1.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 7.75/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f32,f33])).
% 7.75/1.48  
% 7.75/1.48  fof(f51,plain,(
% 7.75/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f34])).
% 7.75/1.48  
% 7.75/1.48  fof(f52,plain,(
% 7.75/1.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f34])).
% 7.75/1.48  
% 7.75/1.48  fof(f79,plain,(
% 7.75/1.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.48    inference(cnf_transformation,[],[f46])).
% 7.75/1.48  
% 7.75/1.48  fof(f93,plain,(
% 7.75/1.48    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 7.75/1.48    inference(equality_resolution,[],[f79])).
% 7.75/1.48  
% 7.75/1.48  fof(f76,plain,(
% 7.75/1.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 7.75/1.48    inference(cnf_transformation,[],[f46])).
% 7.75/1.48  
% 7.75/1.48  fof(f95,plain,(
% 7.75/1.48    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 7.75/1.48    inference(equality_resolution,[],[f76])).
% 7.75/1.48  
% 7.75/1.48  fof(f7,axiom,(
% 7.75/1.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 7.75/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.48  
% 7.75/1.48  fof(f20,plain,(
% 7.75/1.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 7.75/1.48    inference(ennf_transformation,[],[f7])).
% 7.75/1.48  
% 7.75/1.48  fof(f36,plain,(
% 7.75/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.75/1.48    inference(nnf_transformation,[],[f20])).
% 7.75/1.48  
% 7.75/1.48  fof(f37,plain,(
% 7.75/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.75/1.48    inference(rectify,[],[f36])).
% 7.75/1.48  
% 7.75/1.48  fof(f38,plain,(
% 7.75/1.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))))),
% 7.75/1.48    introduced(choice_axiom,[])).
% 7.75/1.48  
% 7.75/1.48  fof(f39,plain,(
% 7.75/1.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 7.75/1.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f37,f38])).
% 7.75/1.48  
% 7.75/1.48  fof(f59,plain,(
% 7.75/1.48    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f39])).
% 7.75/1.48  
% 7.75/1.48  fof(f9,axiom,(
% 7.75/1.48    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 7.75/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.48  
% 7.75/1.48  fof(f23,plain,(
% 7.75/1.48    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 7.75/1.48    inference(ennf_transformation,[],[f9])).
% 7.75/1.48  
% 7.75/1.48  fof(f71,plain,(
% 7.75/1.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f23])).
% 7.75/1.48  
% 7.75/1.48  fof(f2,axiom,(
% 7.75/1.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 7.75/1.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 7.75/1.48  
% 7.75/1.48  fof(f53,plain,(
% 7.75/1.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f2])).
% 7.75/1.48  
% 7.75/1.48  fof(f61,plain,(
% 7.75/1.48    ( ! [X2,X0,X1] : (r2_hidden(sK1(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f39])).
% 7.75/1.48  
% 7.75/1.48  fof(f66,plain,(
% 7.75/1.48    ( ! [X6,X2,X0,X7,X1] : (r2_hidden(X6,X2) | k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f45])).
% 7.75/1.48  
% 7.75/1.48  fof(f86,plain,(
% 7.75/1.48    ( ! [X2,X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),X2) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.75/1.48    inference(equality_resolution,[],[f66])).
% 7.75/1.48  
% 7.75/1.48  fof(f87,plain,(
% 7.75/1.48    ( ! [X0,X7,X1] : (r2_hidden(k1_funct_1(X0,X7),k9_relat_1(X0,X1)) | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 7.75/1.48    inference(equality_resolution,[],[f86])).
% 7.75/1.48  
% 7.75/1.48  fof(f60,plain,(
% 7.75/1.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK1(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 7.75/1.48    inference(cnf_transformation,[],[f39])).
% 7.75/1.48  
% 7.75/1.48  cnf(c_33,negated_conjecture,
% 7.75/1.48      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 7.75/1.48      inference(cnf_transformation,[],[f83]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1198,plain,
% 7.75/1.48      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_30,plain,
% 7.75/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.75/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.48      | k1_relset_1(X1,X2,X0) = X1
% 7.75/1.48      | k1_xboole_0 = X2 ),
% 7.75/1.48      inference(cnf_transformation,[],[f75]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1201,plain,
% 7.75/1.48      ( k1_relset_1(X0,X1,X2) = X0
% 7.75/1.48      | k1_xboole_0 = X1
% 7.75/1.48      | v1_funct_2(X2,X0,X1) != iProver_top
% 7.75/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1716,plain,
% 7.75/1.48      ( k1_relset_1(sK5,sK6,sK8) = sK5
% 7.75/1.48      | sK6 = k1_xboole_0
% 7.75/1.48      | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1198,c_1201]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_34,negated_conjecture,
% 7.75/1.48      ( v1_funct_2(sK8,sK5,sK6) ),
% 7.75/1.48      inference(cnf_transformation,[],[f82]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1717,plain,
% 7.75/1.48      ( ~ v1_funct_2(sK8,sK5,sK6)
% 7.75/1.48      | k1_relset_1(sK5,sK6,sK8) = sK5
% 7.75/1.48      | sK6 = k1_xboole_0 ),
% 7.75/1.48      inference(predicate_to_equality_rev,[status(thm)],[c_1716]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_2280,plain,
% 7.75/1.48      ( sK6 = k1_xboole_0 | k1_relset_1(sK5,sK6,sK8) = sK5 ),
% 7.75/1.48      inference(global_propositional_subsumption,
% 7.75/1.48                [status(thm)],
% 7.75/1.48                [c_1716,c_34,c_1717]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_2281,plain,
% 7.75/1.48      ( k1_relset_1(sK5,sK6,sK8) = sK5 | sK6 = k1_xboole_0 ),
% 7.75/1.48      inference(renaming,[status(thm)],[c_2280]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_23,plain,
% 7.75/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 7.75/1.48      inference(cnf_transformation,[],[f73]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1208,plain,
% 7.75/1.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 7.75/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_2594,plain,
% 7.75/1.48      ( k1_relset_1(sK5,sK6,sK8) = k1_relat_1(sK8) ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1198,c_1208]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_2985,plain,
% 7.75/1.48      ( k1_relat_1(sK8) = sK5 | sK6 = k1_xboole_0 ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_2281,c_2594]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_20,plain,
% 7.75/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.75/1.48      | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1))
% 7.75/1.48      | ~ v1_funct_1(X1)
% 7.75/1.48      | ~ v1_relat_1(X1) ),
% 7.75/1.48      inference(cnf_transformation,[],[f90]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1211,plain,
% 7.75/1.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.75/1.48      | r2_hidden(sK4(X1,X2,X0),k1_relat_1(X1)) = iProver_top
% 7.75/1.48      | v1_funct_1(X1) != iProver_top
% 7.75/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_4902,plain,
% 7.75/1.48      ( sK6 = k1_xboole_0
% 7.75/1.48      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 7.75/1.48      | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top
% 7.75/1.48      | v1_funct_1(sK8) != iProver_top
% 7.75/1.48      | v1_relat_1(sK8) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_2985,c_1211]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_35,negated_conjecture,
% 7.75/1.48      ( v1_funct_1(sK8) ),
% 7.75/1.48      inference(cnf_transformation,[],[f81]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_36,plain,
% 7.75/1.48      ( v1_funct_1(sK8) = iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_38,plain,
% 7.75/1.48      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_33]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_22,plain,
% 7.75/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 7.75/1.48      inference(cnf_transformation,[],[f72]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1568,plain,
% 7.75/1.48      ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 7.75/1.48      | v1_relat_1(sK8) ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_22]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1569,plain,
% 7.75/1.48      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 7.75/1.48      | v1_relat_1(sK8) = iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_1568]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_5105,plain,
% 7.75/1.48      ( sK6 = k1_xboole_0
% 7.75/1.48      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 7.75/1.48      | r2_hidden(sK4(sK8,X1,X0),sK5) = iProver_top ),
% 7.75/1.48      inference(global_propositional_subsumption,
% 7.75/1.48                [status(thm)],
% 7.75/1.48                [c_4902,c_36,c_38,c_1569]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_4,plain,
% 7.75/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 7.75/1.48      inference(cnf_transformation,[],[f55]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1226,plain,
% 7.75/1.48      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 7.75/1.48      | r1_tarski(X0,X1) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_6,plain,
% 7.75/1.48      ( m1_subset_1(X0,X1)
% 7.75/1.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 7.75/1.48      | ~ r2_hidden(X0,X2) ),
% 7.75/1.48      inference(cnf_transformation,[],[f56]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1224,plain,
% 7.75/1.48      ( m1_subset_1(X0,X1) = iProver_top
% 7.75/1.48      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 7.75/1.48      | r2_hidden(X0,X2) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_3422,plain,
% 7.75/1.48      ( m1_subset_1(X0,X1) = iProver_top
% 7.75/1.48      | r2_hidden(X0,X2) != iProver_top
% 7.75/1.48      | r1_tarski(X2,X1) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1226,c_1224]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_11052,plain,
% 7.75/1.48      ( sK6 = k1_xboole_0
% 7.75/1.48      | m1_subset_1(sK4(sK8,X0,X1),X2) = iProver_top
% 7.75/1.48      | r2_hidden(X1,k9_relat_1(sK8,X0)) != iProver_top
% 7.75/1.48      | r1_tarski(sK5,X2) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_5105,c_3422]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_24,plain,
% 7.75/1.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 7.75/1.48      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 7.75/1.48      inference(cnf_transformation,[],[f74]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1207,plain,
% 7.75/1.48      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 7.75/1.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_2608,plain,
% 7.75/1.48      ( k7_relset_1(sK5,sK6,sK8,X0) = k9_relat_1(sK8,X0) ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1198,c_1207]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_32,negated_conjecture,
% 7.75/1.48      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) ),
% 7.75/1.48      inference(cnf_transformation,[],[f84]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1199,plain,
% 7.75/1.48      ( r2_hidden(sK9,k7_relset_1(sK5,sK6,sK8,sK7)) = iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_2989,plain,
% 7.75/1.48      ( r2_hidden(sK9,k9_relat_1(sK8,sK7)) = iProver_top ),
% 7.75/1.48      inference(demodulation,[status(thm)],[c_2608,c_1199]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_18,plain,
% 7.75/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.75/1.48      | ~ v1_funct_1(X1)
% 7.75/1.48      | ~ v1_relat_1(X1)
% 7.75/1.48      | k1_funct_1(X1,sK4(X1,X2,X0)) = X0 ),
% 7.75/1.48      inference(cnf_transformation,[],[f88]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1213,plain,
% 7.75/1.48      ( k1_funct_1(X0,sK4(X0,X1,X2)) = X2
% 7.75/1.48      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 7.75/1.48      | v1_funct_1(X0) != iProver_top
% 7.75/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_4653,plain,
% 7.75/1.48      ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9
% 7.75/1.48      | v1_funct_1(sK8) != iProver_top
% 7.75/1.48      | v1_relat_1(sK8) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_2989,c_1213]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_4939,plain,
% 7.75/1.48      ( k1_funct_1(sK8,sK4(sK8,sK7,sK9)) = sK9 ),
% 7.75/1.48      inference(global_propositional_subsumption,
% 7.75/1.48                [status(thm)],
% 7.75/1.48                [c_4653,c_36,c_38,c_1569]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_31,negated_conjecture,
% 7.75/1.48      ( ~ m1_subset_1(X0,sK5)
% 7.75/1.48      | ~ r2_hidden(X0,sK7)
% 7.75/1.48      | k1_funct_1(sK8,X0) != sK9 ),
% 7.75/1.48      inference(cnf_transformation,[],[f85]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1200,plain,
% 7.75/1.48      ( k1_funct_1(sK8,X0) != sK9
% 7.75/1.48      | m1_subset_1(X0,sK5) != iProver_top
% 7.75/1.48      | r2_hidden(X0,sK7) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_4942,plain,
% 7.75/1.48      ( m1_subset_1(sK4(sK8,sK7,sK9),sK5) != iProver_top
% 7.75/1.48      | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_4939,c_1200]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_12378,plain,
% 7.75/1.48      ( sK6 = k1_xboole_0
% 7.75/1.48      | r2_hidden(sK4(sK8,sK7,sK9),sK7) != iProver_top
% 7.75/1.48      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 7.75/1.48      | r1_tarski(sK5,sK5) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_11052,c_4942]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_19,plain,
% 7.75/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.75/1.48      | r2_hidden(sK4(X1,X2,X0),X2)
% 7.75/1.48      | ~ v1_funct_1(X1)
% 7.75/1.48      | ~ v1_relat_1(X1) ),
% 7.75/1.48      inference(cnf_transformation,[],[f89]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_2105,plain,
% 7.75/1.48      ( r2_hidden(sK4(X0,X1,sK9),X1)
% 7.75/1.48      | ~ r2_hidden(sK9,k9_relat_1(X0,X1))
% 7.75/1.48      | ~ v1_funct_1(X0)
% 7.75/1.48      | ~ v1_relat_1(X0) ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_19]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_3175,plain,
% 7.75/1.48      ( r2_hidden(sK4(sK8,X0,sK9),X0)
% 7.75/1.48      | ~ r2_hidden(sK9,k9_relat_1(sK8,X0))
% 7.75/1.48      | ~ v1_funct_1(sK8)
% 7.75/1.48      | ~ v1_relat_1(sK8) ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_2105]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_10590,plain,
% 7.75/1.48      ( r2_hidden(sK4(sK8,sK7,sK9),sK7)
% 7.75/1.48      | ~ r2_hidden(sK9,k9_relat_1(sK8,sK7))
% 7.75/1.48      | ~ v1_funct_1(sK8)
% 7.75/1.48      | ~ v1_relat_1(sK8) ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_3175]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_10592,plain,
% 7.75/1.48      ( r2_hidden(sK4(sK8,sK7,sK9),sK7) = iProver_top
% 7.75/1.48      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 7.75/1.48      | v1_funct_1(sK8) != iProver_top
% 7.75/1.48      | v1_relat_1(sK8) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_10590]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_12632,plain,
% 7.75/1.48      ( sK6 = k1_xboole_0 | r1_tarski(sK5,sK5) != iProver_top ),
% 7.75/1.48      inference(global_propositional_subsumption,
% 7.75/1.48                [status(thm)],
% 7.75/1.48                [c_12378,c_36,c_38,c_1569,c_2989,c_10592]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1,plain,
% 7.75/1.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 7.75/1.48      inference(cnf_transformation,[],[f51]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1229,plain,
% 7.75/1.48      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 7.75/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_0,plain,
% 7.75/1.48      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 7.75/1.48      inference(cnf_transformation,[],[f52]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1230,plain,
% 7.75/1.48      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 7.75/1.48      | r1_tarski(X0,X1) = iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_2418,plain,
% 7.75/1.48      ( r1_tarski(X0,X0) = iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1229,c_1230]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_12638,plain,
% 7.75/1.48      ( sK6 = k1_xboole_0 ),
% 7.75/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_12632,c_2418]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_12653,plain,
% 7.75/1.48      ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,k1_xboole_0))) = iProver_top ),
% 7.75/1.48      inference(demodulation,[status(thm)],[c_12638,c_1198]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_26,plain,
% 7.75/1.48      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 7.75/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 7.75/1.48      | k1_xboole_0 = X1
% 7.75/1.48      | k1_xboole_0 = X0 ),
% 7.75/1.48      inference(cnf_transformation,[],[f93]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1205,plain,
% 7.75/1.48      ( k1_xboole_0 = X0
% 7.75/1.48      | k1_xboole_0 = X1
% 7.75/1.48      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 7.75/1.48      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_12991,plain,
% 7.75/1.48      ( sK5 = k1_xboole_0
% 7.75/1.48      | sK8 = k1_xboole_0
% 7.75/1.48      | v1_funct_2(sK8,sK5,k1_xboole_0) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_12653,c_1205]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_37,plain,
% 7.75/1.48      ( v1_funct_2(sK8,sK5,sK6) = iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_408,plain,( X0 = X0 ),theory(equality) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_435,plain,
% 7.75/1.48      ( k1_xboole_0 = k1_xboole_0 ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_408]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1896,plain,
% 7.75/1.48      ( sK8 = sK8 ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_408]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_421,plain,
% 7.75/1.48      ( ~ v1_funct_2(X0,X1,X2)
% 7.75/1.48      | v1_funct_2(X3,X4,X5)
% 7.75/1.48      | X3 != X0
% 7.75/1.48      | X4 != X1
% 7.75/1.48      | X5 != X2 ),
% 7.75/1.48      theory(equality) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1686,plain,
% 7.75/1.48      ( v1_funct_2(X0,X1,X2)
% 7.75/1.48      | ~ v1_funct_2(sK8,sK5,sK6)
% 7.75/1.48      | X2 != sK6
% 7.75/1.48      | X1 != sK5
% 7.75/1.48      | X0 != sK8 ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_421]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1895,plain,
% 7.75/1.48      ( v1_funct_2(sK8,X0,X1)
% 7.75/1.48      | ~ v1_funct_2(sK8,sK5,sK6)
% 7.75/1.48      | X1 != sK6
% 7.75/1.48      | X0 != sK5
% 7.75/1.48      | sK8 != sK8 ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_1686]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_2344,plain,
% 7.75/1.48      ( v1_funct_2(sK8,sK5,X0)
% 7.75/1.48      | ~ v1_funct_2(sK8,sK5,sK6)
% 7.75/1.48      | X0 != sK6
% 7.75/1.48      | sK5 != sK5
% 7.75/1.48      | sK8 != sK8 ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_1895]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_2346,plain,
% 7.75/1.48      ( X0 != sK6
% 7.75/1.48      | sK5 != sK5
% 7.75/1.48      | sK8 != sK8
% 7.75/1.48      | v1_funct_2(sK8,sK5,X0) = iProver_top
% 7.75/1.48      | v1_funct_2(sK8,sK5,sK6) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_2344]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_2348,plain,
% 7.75/1.48      ( sK5 != sK5
% 7.75/1.48      | sK8 != sK8
% 7.75/1.48      | k1_xboole_0 != sK6
% 7.75/1.48      | v1_funct_2(sK8,sK5,sK6) != iProver_top
% 7.75/1.48      | v1_funct_2(sK8,sK5,k1_xboole_0) = iProver_top ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_2346]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_2345,plain,
% 7.75/1.48      ( sK5 = sK5 ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_408]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_409,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_3385,plain,
% 7.75/1.48      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_409]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_3386,plain,
% 7.75/1.48      ( sK6 != k1_xboole_0 | k1_xboole_0 = sK6 | k1_xboole_0 != k1_xboole_0 ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_3385]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_13146,plain,
% 7.75/1.48      ( sK8 = k1_xboole_0 | sK5 = k1_xboole_0 ),
% 7.75/1.48      inference(global_propositional_subsumption,
% 7.75/1.48                [status(thm)],
% 7.75/1.48                [c_12991,c_37,c_435,c_1896,c_2348,c_2345,c_3386,c_12638]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_13147,plain,
% 7.75/1.48      ( sK5 = k1_xboole_0 | sK8 = k1_xboole_0 ),
% 7.75/1.48      inference(renaming,[status(thm)],[c_13146]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_13150,plain,
% 7.75/1.48      ( sK8 = k1_xboole_0
% 7.75/1.48      | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_13147,c_12653]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_29,plain,
% 7.75/1.48      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 7.75/1.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 7.75/1.48      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 7.75/1.48      inference(cnf_transformation,[],[f95]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1202,plain,
% 7.75/1.48      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 7.75/1.48      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 7.75/1.48      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_14622,plain,
% 7.75/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
% 7.75/1.48      | sK8 = k1_xboole_0
% 7.75/1.48      | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_13150,c_1202]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1197,plain,
% 7.75/1.48      ( v1_funct_2(sK8,sK5,sK6) = iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_12654,plain,
% 7.75/1.48      ( v1_funct_2(sK8,sK5,k1_xboole_0) = iProver_top ),
% 7.75/1.48      inference(demodulation,[status(thm)],[c_12638,c_1197]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_13151,plain,
% 7.75/1.48      ( sK8 = k1_xboole_0
% 7.75/1.48      | v1_funct_2(sK8,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_13147,c_12654]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_15086,plain,
% 7.75/1.48      ( sK8 = k1_xboole_0
% 7.75/1.48      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0 ),
% 7.75/1.48      inference(global_propositional_subsumption,
% 7.75/1.48                [status(thm)],
% 7.75/1.48                [c_14622,c_13151]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_15087,plain,
% 7.75/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_xboole_0
% 7.75/1.48      | sK8 = k1_xboole_0 ),
% 7.75/1.48      inference(renaming,[status(thm)],[c_15086]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_12650,plain,
% 7.75/1.48      ( k1_relset_1(sK5,k1_xboole_0,sK8) = k1_relat_1(sK8) ),
% 7.75/1.48      inference(demodulation,[status(thm)],[c_12638,c_2594]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_13489,plain,
% 7.75/1.48      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK8) = k1_relat_1(sK8)
% 7.75/1.48      | sK8 = k1_xboole_0 ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_13147,c_12650]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_15093,plain,
% 7.75/1.48      ( k1_relat_1(sK8) = k1_xboole_0 | sK8 = k1_xboole_0 ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_15087,c_13489]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_12,plain,
% 7.75/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.75/1.48      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1))
% 7.75/1.48      | ~ v1_relat_1(X1) ),
% 7.75/1.48      inference(cnf_transformation,[],[f59]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1219,plain,
% 7.75/1.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.75/1.48      | r2_hidden(sK1(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 7.75/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_21,plain,
% 7.75/1.48      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 7.75/1.48      inference(cnf_transformation,[],[f71]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1210,plain,
% 7.75/1.48      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_3577,plain,
% 7.75/1.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.75/1.48      | r1_tarski(k1_relat_1(X1),sK1(X0,X2,X1)) != iProver_top
% 7.75/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1219,c_1210]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_17423,plain,
% 7.75/1.48      ( sK8 = k1_xboole_0
% 7.75/1.48      | r2_hidden(X0,k9_relat_1(sK8,X1)) != iProver_top
% 7.75/1.48      | r1_tarski(k1_xboole_0,sK1(X0,X1,sK8)) != iProver_top
% 7.75/1.48      | v1_relat_1(sK8) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_15093,c_3577]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_3,plain,
% 7.75/1.48      ( r1_tarski(k1_xboole_0,X0) ),
% 7.75/1.48      inference(cnf_transformation,[],[f53]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1227,plain,
% 7.75/1.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_10,plain,
% 7.75/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.75/1.48      | r2_hidden(sK1(X0,X2,X1),X2)
% 7.75/1.48      | ~ v1_relat_1(X1) ),
% 7.75/1.48      inference(cnf_transformation,[],[f61]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1221,plain,
% 7.75/1.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.75/1.48      | r2_hidden(sK1(X0,X2,X1),X2) = iProver_top
% 7.75/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_3441,plain,
% 7.75/1.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.75/1.48      | r1_tarski(X2,sK1(X0,X2,X1)) != iProver_top
% 7.75/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1221,c_1210]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_15272,plain,
% 7.75/1.48      ( r2_hidden(X0,k9_relat_1(X1,k1_xboole_0)) != iProver_top
% 7.75/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1227,c_3441]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_15291,plain,
% 7.75/1.48      ( r1_tarski(k9_relat_1(X0,k1_xboole_0),X1) = iProver_top
% 7.75/1.48      | v1_relat_1(X0) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1229,c_15272]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_17,plain,
% 7.75/1.48      ( ~ r2_hidden(X0,X1)
% 7.75/1.48      | ~ r2_hidden(X0,k1_relat_1(X2))
% 7.75/1.48      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1))
% 7.75/1.48      | ~ v1_funct_1(X2)
% 7.75/1.48      | ~ v1_relat_1(X2) ),
% 7.75/1.48      inference(cnf_transformation,[],[f87]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1214,plain,
% 7.75/1.48      ( r2_hidden(X0,X1) != iProver_top
% 7.75/1.48      | r2_hidden(X0,k1_relat_1(X2)) != iProver_top
% 7.75/1.48      | r2_hidden(k1_funct_1(X2,X0),k9_relat_1(X2,X1)) = iProver_top
% 7.75/1.48      | v1_funct_1(X2) != iProver_top
% 7.75/1.48      | v1_relat_1(X2) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_5669,plain,
% 7.75/1.48      ( r2_hidden(sK4(sK8,sK7,sK9),X0) != iProver_top
% 7.75/1.48      | r2_hidden(sK4(sK8,sK7,sK9),k1_relat_1(sK8)) != iProver_top
% 7.75/1.48      | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top
% 7.75/1.48      | v1_funct_1(sK8) != iProver_top
% 7.75/1.48      | v1_relat_1(sK8) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_4939,c_1214]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_6605,plain,
% 7.75/1.48      ( r2_hidden(sK4(sK8,sK7,sK9),X0) != iProver_top
% 7.75/1.48      | r2_hidden(sK4(sK8,sK7,sK9),k1_relat_1(sK8)) != iProver_top
% 7.75/1.48      | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top ),
% 7.75/1.48      inference(global_propositional_subsumption,
% 7.75/1.48                [status(thm)],
% 7.75/1.48                [c_5669,c_36,c_38,c_1569]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_6616,plain,
% 7.75/1.48      ( sK6 = k1_xboole_0
% 7.75/1.48      | r2_hidden(sK4(sK8,sK7,sK9),X0) != iProver_top
% 7.75/1.48      | r2_hidden(sK4(sK8,sK7,sK9),sK5) != iProver_top
% 7.75/1.48      | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_2985,c_6605]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_6614,plain,
% 7.75/1.48      ( r2_hidden(sK4(sK8,sK7,sK9),X0) != iProver_top
% 7.75/1.48      | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top
% 7.75/1.48      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 7.75/1.48      | v1_funct_1(sK8) != iProver_top
% 7.75/1.48      | v1_relat_1(sK8) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1211,c_6605]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_6655,plain,
% 7.75/1.48      ( r2_hidden(sK4(sK8,sK7,sK9),X0) != iProver_top
% 7.75/1.48      | r2_hidden(sK9,k9_relat_1(sK8,X0)) = iProver_top ),
% 7.75/1.48      inference(global_propositional_subsumption,
% 7.75/1.48                [status(thm)],
% 7.75/1.48                [c_6616,c_36,c_38,c_1569,c_2989,c_6614]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_6664,plain,
% 7.75/1.48      ( r2_hidden(sK9,k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top
% 7.75/1.48      | r2_hidden(sK9,k9_relat_1(sK8,sK7)) != iProver_top
% 7.75/1.48      | v1_funct_1(sK8) != iProver_top
% 7.75/1.48      | v1_relat_1(sK8) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1211,c_6655]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_7010,plain,
% 7.75/1.48      ( r2_hidden(sK9,k9_relat_1(sK8,k1_relat_1(sK8))) = iProver_top ),
% 7.75/1.48      inference(global_propositional_subsumption,
% 7.75/1.48                [status(thm)],
% 7.75/1.48                [c_6664,c_36,c_38,c_1569,c_2989]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_7017,plain,
% 7.75/1.48      ( r1_tarski(k9_relat_1(sK8,k1_relat_1(sK8)),sK9) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_7010,c_1210]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_16063,plain,
% 7.75/1.48      ( sK8 = k1_xboole_0
% 7.75/1.48      | r1_tarski(k9_relat_1(sK8,k1_xboole_0),sK9) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_15093,c_7017]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_18063,plain,
% 7.75/1.48      ( sK8 = k1_xboole_0 | v1_relat_1(sK8) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_15291,c_16063]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_18684,plain,
% 7.75/1.48      ( sK8 = k1_xboole_0 ),
% 7.75/1.48      inference(global_propositional_subsumption,
% 7.75/1.48                [status(thm)],
% 7.75/1.48                [c_17423,c_38,c_1569,c_18063]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_18714,plain,
% 7.75/1.48      ( r2_hidden(sK9,k9_relat_1(k1_xboole_0,sK7)) = iProver_top ),
% 7.75/1.48      inference(demodulation,[status(thm)],[c_18684,c_2989]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_11,plain,
% 7.75/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.75/1.48      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1)
% 7.75/1.48      | ~ v1_relat_1(X1) ),
% 7.75/1.48      inference(cnf_transformation,[],[f60]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1220,plain,
% 7.75/1.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.75/1.48      | r2_hidden(k4_tarski(sK1(X0,X2,X1),X0),X1) = iProver_top
% 7.75/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_4444,plain,
% 7.75/1.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 7.75/1.48      | r1_tarski(X1,k4_tarski(sK1(X0,X2,X1),X0)) != iProver_top
% 7.75/1.48      | v1_relat_1(X1) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1220,c_1210]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_17443,plain,
% 7.75/1.48      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
% 7.75/1.48      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.75/1.48      inference(superposition,[status(thm)],[c_1227,c_4444]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1733,plain,
% 7.75/1.48      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) | v1_relat_1(X0) ),
% 7.75/1.48      inference(resolution,[status(thm)],[c_22,c_4]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1734,plain,
% 7.75/1.48      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 7.75/1.48      | v1_relat_1(X0) = iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_1733]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1736,plain,
% 7.75/1.48      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 7.75/1.48      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_1734]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1789,plain,
% 7.75/1.48      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_3]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1790,plain,
% 7.75/1.48      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_1789]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_1792,plain,
% 7.75/1.48      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 7.75/1.48      inference(instantiation,[status(thm)],[c_1790]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_3625,plain,
% 7.75/1.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 7.75/1.48      | ~ r1_tarski(X1,k4_tarski(sK1(X0,X2,X1),X0))
% 7.75/1.48      | ~ v1_relat_1(X1) ),
% 7.75/1.48      inference(resolution,[status(thm)],[c_11,c_21]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_15106,plain,
% 7.75/1.48      ( ~ r2_hidden(X0,k9_relat_1(k1_xboole_0,X1))
% 7.75/1.48      | ~ v1_relat_1(k1_xboole_0) ),
% 7.75/1.48      inference(resolution,[status(thm)],[c_3625,c_3]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_15107,plain,
% 7.75/1.48      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
% 7.75/1.48      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 7.75/1.48      inference(predicate_to_equality,[status(thm)],[c_15106]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_17951,plain,
% 7.75/1.48      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top ),
% 7.75/1.48      inference(global_propositional_subsumption,
% 7.75/1.48                [status(thm)],
% 7.75/1.48                [c_17443,c_1736,c_1792,c_15107]) ).
% 7.75/1.48  
% 7.75/1.48  cnf(c_20186,plain,
% 7.75/1.48      ( $false ),
% 7.75/1.48      inference(forward_subsumption_resolution,[status(thm)],[c_18714,c_17951]) ).
% 7.75/1.48  
% 7.75/1.48  
% 7.75/1.48  % SZS output end CNFRefutation for theBenchmark.p
% 7.75/1.48  
% 7.75/1.48  ------                               Statistics
% 7.75/1.48  
% 7.75/1.48  ------ Selected
% 7.75/1.48  
% 7.75/1.48  total_time:                             0.568
% 7.75/1.48  
%------------------------------------------------------------------------------
