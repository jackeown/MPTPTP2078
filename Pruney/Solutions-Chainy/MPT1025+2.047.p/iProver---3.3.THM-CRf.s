%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:09 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :  187 (3307 expanded)
%              Number of clauses        :  120 (1181 expanded)
%              Number of leaves         :   22 ( 788 expanded)
%              Depth                    :   32
%              Number of atoms          :  635 (16403 expanded)
%              Number of equality atoms :  294 (4231 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f12,conjecture,(
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

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f39,plain,(
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

fof(f38,plain,
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
              ( k1_funct_1(sK7,X5) != X4
              | ~ r2_hidden(X5,sK6)
              | ~ m1_subset_1(X5,sK4) )
          & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK7,sK4,sK5)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ m1_subset_1(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f25,f39,f38])).

fof(f70,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f40])).

fof(f10,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f71,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f40])).

fof(f11,axiom,(
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

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(nnf_transformation,[],[f23])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f69,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f40])).

fof(f7,axiom,(
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

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f7])).

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
    inference(flattening,[],[f17])).

fof(f31,plain,(
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
    inference(nnf_transformation,[],[f18])).

fof(f32,plain,(
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
    inference(rectify,[],[f31])).

fof(f35,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f34,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
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

fof(f36,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).

fof(f51,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f77,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f51])).

fof(f68,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f40])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(X1))
        | ~ r1_tarski(X0,X1) )
      & ( r1_tarski(X0,X1)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f43,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f52,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f76,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f53,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f75,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f72,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f66,plain,(
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
    inference(equality_resolution,[],[f66])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f63,plain,(
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
    inference(equality_resolution,[],[f63])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f16])).

fof(f28,plain,(
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
    inference(rectify,[],[f27])).

fof(f29,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f8,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_29,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1092,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_29])).

cnf(c_20,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1101,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_2274,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1092,c_1101])).

cnf(c_28,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1093,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2599,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2274,c_1093])).

cnf(c_26,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_1095,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_3264,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_1095])).

cnf(c_19,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_1102,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_1815,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1092,c_1102])).

cnf(c_3268,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_3264,c_1815])).

cnf(c_30,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_33,plain,
    ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_3486,plain,
    ( sK5 = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3268,c_33])).

cnf(c_3487,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_3486])).

cnf(c_17,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1104,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_4189,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3487,c_1104])).

cnf(c_31,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_32,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1117,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1675,plain,
    ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1092,c_1117])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_222,plain,
    ( ~ r1_tarski(X0,X1)
    | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
    inference(prop_impl,[status(thm)],[c_2])).

cnf(c_223,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(renaming,[status(thm)],[c_222])).

cnf(c_289,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(bin_hyper_res,[status(thm)],[c_4,c_223])).

cnf(c_1089,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_289])).

cnf(c_2079,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_1675,c_1089])).

cnf(c_5,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1116,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2170,plain,
    ( v1_relat_1(sK7) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2079,c_1116])).

cnf(c_5309,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4189,c_32,c_2170])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1119,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_5319,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | m1_subset_1(sK3(sK7,X1,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_5309,c_1119])).

cnf(c_16,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_1105,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_1106,plain,
    ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4403,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_2599,c_1106])).

cnf(c_5039,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4403,c_32,c_2170])).

cnf(c_27,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | ~ m1_subset_1(X0,sK4)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1094,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | r2_hidden(X0,sK6) != iProver_top
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_5043,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
    | m1_subset_1(sK3(sK7,sK6,sK8),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_5039,c_1094])).

cnf(c_5065,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | m1_subset_1(sK3(sK7,sK6,sK8),sK4) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1105,c_5043])).

cnf(c_5170,plain,
    ( m1_subset_1(sK3(sK7,sK6,sK8),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5065,c_32,c_2170,c_2599])).

cnf(c_6204,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_5319,c_5170])).

cnf(c_6207,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6204,c_2599])).

cnf(c_6214,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6207,c_1092])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1099,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6346,plain,
    ( sK4 = k1_xboole_0
    | sK7 = k1_xboole_0
    | v1_funct_2(sK7,sK4,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_6214,c_1099])).

cnf(c_370,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_397,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_1666,plain,
    ( sK7 = sK7 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_383,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1508,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK7,sK4,sK5)
    | X2 != sK5
    | X1 != sK4
    | X0 != sK7 ),
    inference(instantiation,[status(thm)],[c_383])).

cnf(c_1665,plain,
    ( v1_funct_2(sK7,X0,X1)
    | ~ v1_funct_2(sK7,sK4,sK5)
    | X1 != sK5
    | X0 != sK4
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1508])).

cnf(c_1891,plain,
    ( v1_funct_2(sK7,sK4,X0)
    | ~ v1_funct_2(sK7,sK4,sK5)
    | X0 != sK5
    | sK4 != sK4
    | sK7 != sK7 ),
    inference(instantiation,[status(thm)],[c_1665])).

cnf(c_1893,plain,
    ( X0 != sK5
    | sK4 != sK4
    | sK7 != sK7
    | v1_funct_2(sK7,sK4,X0) = iProver_top
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1891])).

cnf(c_1895,plain,
    ( sK4 != sK4
    | sK7 != sK7
    | k1_xboole_0 != sK5
    | v1_funct_2(sK7,sK4,sK5) != iProver_top
    | v1_funct_2(sK7,sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1893])).

cnf(c_1892,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_370])).

cnf(c_371,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2368,plain,
    ( X0 != X1
    | X0 = sK5
    | sK5 != X1 ),
    inference(instantiation,[status(thm)],[c_371])).

cnf(c_2369,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2368])).

cnf(c_6702,plain,
    ( sK7 = k1_xboole_0
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6346,c_33,c_397,c_1666,c_1895,c_1892,c_2369,c_2599,c_6204])).

cnf(c_6703,plain,
    ( sK4 = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_6702])).

cnf(c_1091,plain,
    ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_30])).

cnf(c_6215,plain,
    ( v1_funct_2(sK7,sK4,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_6207,c_1091])).

cnf(c_6710,plain,
    ( sK7 = k1_xboole_0
    | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_6703,c_6215])).

cnf(c_6709,plain,
    ( sK7 = k1_xboole_0
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_6703,c_6214])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1614,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1615,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1614])).

cnf(c_1617,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1615])).

cnf(c_372,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_1632,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(X3,k2_zfmisc_1(X1,X2))
    | X3 != X0 ),
    inference(instantiation,[status(thm)],[c_372])).

cnf(c_2159,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | r1_tarski(sK7,k2_zfmisc_1(X1,X2))
    | sK7 != X0 ),
    inference(instantiation,[status(thm)],[c_1632])).

cnf(c_2160,plain,
    ( sK7 != X0
    | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r1_tarski(sK7,k2_zfmisc_1(X1,X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2159])).

cnf(c_2162,plain,
    ( sK7 != k1_xboole_0
    | r1_tarski(sK7,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2160])).

cnf(c_1461,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_2680,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ r1_tarski(sK7,k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_1461])).

cnf(c_2681,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | r1_tarski(sK7,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2680])).

cnf(c_2683,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(sK7,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2681])).

cnf(c_7616,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6709,c_1617,c_2162,c_2683])).

cnf(c_7624,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_7616,c_1102])).

cnf(c_25,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1096,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_7626,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
    | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7616,c_1096])).

cnf(c_7632,plain,
    ( k1_relat_1(sK7) = k1_xboole_0
    | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_7624,c_7626])).

cnf(c_8740,plain,
    ( k1_relat_1(sK7) = k1_xboole_0
    | sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_6710,c_7632])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1112,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_18,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_1103,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_2444,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(k1_relat_1(X1),sK0(X0,X2,X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1112,c_1103])).

cnf(c_9066,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r1_tarski(k1_xboole_0,sK0(X0,X1,sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8740,c_2444])).

cnf(c_9137,plain,
    ( r1_tarski(k1_xboole_0,sK0(X0,X1,sK7)) != iProver_top
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | sK7 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9066,c_2170])).

cnf(c_9138,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r1_tarski(k1_xboole_0,sK0(X0,X1,sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_9137])).

cnf(c_1120,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_9146,plain,
    ( sK7 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9138,c_1120])).

cnf(c_9158,plain,
    ( sK7 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2599,c_9146])).

cnf(c_9303,plain,
    ( r2_hidden(sK8,k9_relat_1(k1_xboole_0,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_9158,c_2599])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1113,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_3035,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r1_tarski(X1,k4_tarski(sK0(X0,X2,X1),X0)) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1113,c_1103])).

cnf(c_7994,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1120,c_3035])).

cnf(c_102,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_104,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_102])).

cnf(c_1553,plain,
    ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_289])).

cnf(c_1554,plain,
    ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1553])).

cnf(c_1556,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1554])).

cnf(c_7997,plain,
    ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7994,c_104,c_1556,c_1617])).

cnf(c_10152,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_9303,c_7997])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 09:45:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  % Running in FOF mode
% 3.98/0.99  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/0.99  
% 3.98/0.99  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.98/0.99  
% 3.98/0.99  ------  iProver source info
% 3.98/0.99  
% 3.98/0.99  git: date: 2020-06-30 10:37:57 +0100
% 3.98/0.99  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.98/0.99  git: non_committed_changes: false
% 3.98/0.99  git: last_make_outside_of_git: false
% 3.98/0.99  
% 3.98/0.99  ------ 
% 3.98/0.99  ------ Parsing...
% 3.98/0.99  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.98/0.99  
% 3.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.98/0.99  
% 3.98/0.99  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.98/0.99  
% 3.98/0.99  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.98/0.99  ------ Proving...
% 3.98/0.99  ------ Problem Properties 
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  clauses                                 32
% 3.98/0.99  conjectures                             5
% 3.98/0.99  EPR                                     6
% 3.98/0.99  Horn                                    25
% 3.98/0.99  unary                                   6
% 3.98/0.99  binary                                  6
% 3.98/0.99  lits                                    98
% 3.98/0.99  lits eq                                 19
% 3.98/0.99  fd_pure                                 0
% 3.98/0.99  fd_pseudo                               0
% 3.98/0.99  fd_cond                                 3
% 3.98/0.99  fd_pseudo_cond                          4
% 3.98/0.99  AC symbols                              0
% 3.98/0.99  
% 3.98/0.99  ------ Input Options Time Limit: Unbounded
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  ------ 
% 3.98/0.99  Current options:
% 3.98/0.99  ------ 
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  ------ Proving...
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  % SZS status Theorem for theBenchmark.p
% 3.98/0.99  
% 3.98/0.99   Resolution empty clause
% 3.98/0.99  
% 3.98/0.99  % SZS output start CNFRefutation for theBenchmark.p
% 3.98/0.99  
% 3.98/0.99  fof(f12,conjecture,(
% 3.98/0.99    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f13,negated_conjecture,(
% 3.98/0.99    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.98/0.99    inference(negated_conjecture,[],[f12])).
% 3.98/0.99  
% 3.98/0.99  fof(f24,plain,(
% 3.98/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.98/0.99    inference(ennf_transformation,[],[f13])).
% 3.98/0.99  
% 3.98/0.99  fof(f25,plain,(
% 3.98/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.98/0.99    inference(flattening,[],[f24])).
% 3.98/0.99  
% 3.98/0.99  fof(f39,plain,(
% 3.98/0.99    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.98/0.99    introduced(choice_axiom,[])).
% 3.98/0.99  
% 3.98/0.99  fof(f38,plain,(
% 3.98/0.99    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 3.98/0.99    introduced(choice_axiom,[])).
% 3.98/0.99  
% 3.98/0.99  fof(f40,plain,(
% 3.98/0.99    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 3.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f25,f39,f38])).
% 3.98/0.99  
% 3.98/0.99  fof(f70,plain,(
% 3.98/0.99    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.98/0.99    inference(cnf_transformation,[],[f40])).
% 3.98/0.99  
% 3.98/0.99  fof(f10,axiom,(
% 3.98/0.99    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f21,plain,(
% 3.98/0.99    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/0.99    inference(ennf_transformation,[],[f10])).
% 3.98/0.99  
% 3.98/0.99  fof(f61,plain,(
% 3.98/0.99    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f21])).
% 3.98/0.99  
% 3.98/0.99  fof(f71,plain,(
% 3.98/0.99    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 3.98/0.99    inference(cnf_transformation,[],[f40])).
% 3.98/0.99  
% 3.98/0.99  fof(f11,axiom,(
% 3.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f22,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/0.99    inference(ennf_transformation,[],[f11])).
% 3.98/0.99  
% 3.98/0.99  fof(f23,plain,(
% 3.98/0.99    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/0.99    inference(flattening,[],[f22])).
% 3.98/0.99  
% 3.98/0.99  fof(f37,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/0.99    inference(nnf_transformation,[],[f23])).
% 3.98/0.99  
% 3.98/0.99  fof(f62,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f37])).
% 3.98/0.99  
% 3.98/0.99  fof(f9,axiom,(
% 3.98/0.99    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f20,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.98/0.99    inference(ennf_transformation,[],[f9])).
% 3.98/0.99  
% 3.98/0.99  fof(f60,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f20])).
% 3.98/0.99  
% 3.98/0.99  fof(f69,plain,(
% 3.98/0.99    v1_funct_2(sK7,sK4,sK5)),
% 3.98/0.99    inference(cnf_transformation,[],[f40])).
% 3.98/0.99  
% 3.98/0.99  fof(f7,axiom,(
% 3.98/0.99    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f17,plain,(
% 3.98/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.98/0.99    inference(ennf_transformation,[],[f7])).
% 3.98/0.99  
% 3.98/0.99  fof(f18,plain,(
% 3.98/0.99    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.98/0.99    inference(flattening,[],[f17])).
% 3.98/0.99  
% 3.98/0.99  fof(f31,plain,(
% 3.98/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.98/0.99    inference(nnf_transformation,[],[f18])).
% 3.98/0.99  
% 3.98/0.99  fof(f32,plain,(
% 3.98/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.98/0.99    inference(rectify,[],[f31])).
% 3.98/0.99  
% 3.98/0.99  fof(f35,plain,(
% 3.98/0.99    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 3.98/0.99    introduced(choice_axiom,[])).
% 3.98/0.99  
% 3.98/0.99  fof(f34,plain,(
% 3.98/0.99    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 3.98/0.99    introduced(choice_axiom,[])).
% 3.98/0.99  
% 3.98/0.99  fof(f33,plain,(
% 3.98/0.99    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.98/0.99    introduced(choice_axiom,[])).
% 3.98/0.99  
% 3.98/0.99  fof(f36,plain,(
% 3.98/0.99    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f32,f35,f34,f33])).
% 3.98/0.99  
% 3.98/0.99  fof(f51,plain,(
% 3.98/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f36])).
% 3.98/0.99  
% 3.98/0.99  fof(f77,plain,(
% 3.98/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/0.99    inference(equality_resolution,[],[f51])).
% 3.98/0.99  
% 3.98/0.99  fof(f68,plain,(
% 3.98/0.99    v1_funct_1(sK7)),
% 3.98/0.99    inference(cnf_transformation,[],[f40])).
% 3.98/0.99  
% 3.98/0.99  fof(f3,axiom,(
% 3.98/0.99    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f26,plain,(
% 3.98/0.99    ! [X0,X1] : ((m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))))),
% 3.98/0.99    inference(nnf_transformation,[],[f3])).
% 3.98/0.99  
% 3.98/0.99  fof(f43,plain,(
% 3.98/0.99    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f26])).
% 3.98/0.99  
% 3.98/0.99  fof(f4,axiom,(
% 3.98/0.99    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f15,plain,(
% 3.98/0.99    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.98/0.99    inference(ennf_transformation,[],[f4])).
% 3.98/0.99  
% 3.98/0.99  fof(f45,plain,(
% 3.98/0.99    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f15])).
% 3.98/0.99  
% 3.98/0.99  fof(f44,plain,(
% 3.98/0.99    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f26])).
% 3.98/0.99  
% 3.98/0.99  fof(f5,axiom,(
% 3.98/0.99    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f46,plain,(
% 3.98/0.99    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f5])).
% 3.98/0.99  
% 3.98/0.99  fof(f2,axiom,(
% 3.98/0.99    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f14,plain,(
% 3.98/0.99    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.98/0.99    inference(ennf_transformation,[],[f2])).
% 3.98/0.99  
% 3.98/0.99  fof(f42,plain,(
% 3.98/0.99    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f14])).
% 3.98/0.99  
% 3.98/0.99  fof(f52,plain,(
% 3.98/0.99    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f36])).
% 3.98/0.99  
% 3.98/0.99  fof(f76,plain,(
% 3.98/0.99    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/0.99    inference(equality_resolution,[],[f52])).
% 3.98/0.99  
% 3.98/0.99  fof(f53,plain,(
% 3.98/0.99    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f36])).
% 3.98/0.99  
% 3.98/0.99  fof(f75,plain,(
% 3.98/0.99    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.98/0.99    inference(equality_resolution,[],[f53])).
% 3.98/0.99  
% 3.98/0.99  fof(f72,plain,(
% 3.98/0.99    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f40])).
% 3.98/0.99  
% 3.98/0.99  fof(f66,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f37])).
% 3.98/0.99  
% 3.98/0.99  fof(f80,plain,(
% 3.98/0.99    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.98/0.99    inference(equality_resolution,[],[f66])).
% 3.98/0.99  
% 3.98/0.99  fof(f1,axiom,(
% 3.98/0.99    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f41,plain,(
% 3.98/0.99    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f1])).
% 3.98/0.99  
% 3.98/0.99  fof(f63,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.98/0.99    inference(cnf_transformation,[],[f37])).
% 3.98/0.99  
% 3.98/0.99  fof(f82,plain,(
% 3.98/0.99    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.98/0.99    inference(equality_resolution,[],[f63])).
% 3.98/0.99  
% 3.98/0.99  fof(f6,axiom,(
% 3.98/0.99    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f16,plain,(
% 3.98/0.99    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.98/0.99    inference(ennf_transformation,[],[f6])).
% 3.98/0.99  
% 3.98/0.99  fof(f27,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.98/0.99    inference(nnf_transformation,[],[f16])).
% 3.98/0.99  
% 3.98/0.99  fof(f28,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.98/0.99    inference(rectify,[],[f27])).
% 3.98/0.99  
% 3.98/0.99  fof(f29,plain,(
% 3.98/0.99    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.98/0.99    introduced(choice_axiom,[])).
% 3.98/0.99  
% 3.98/0.99  fof(f30,plain,(
% 3.98/0.99    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.98/0.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f28,f29])).
% 3.98/0.99  
% 3.98/0.99  fof(f47,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f30])).
% 3.98/0.99  
% 3.98/0.99  fof(f8,axiom,(
% 3.98/0.99    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.98/0.99    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 3.98/0.99  
% 3.98/0.99  fof(f19,plain,(
% 3.98/0.99    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.98/0.99    inference(ennf_transformation,[],[f8])).
% 3.98/0.99  
% 3.98/0.99  fof(f59,plain,(
% 3.98/0.99    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f19])).
% 3.98/0.99  
% 3.98/0.99  fof(f48,plain,(
% 3.98/0.99    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.98/0.99    inference(cnf_transformation,[],[f30])).
% 3.98/0.99  
% 3.98/0.99  cnf(c_29,negated_conjecture,
% 3.98/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.98/0.99      inference(cnf_transformation,[],[f70]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1092,plain,
% 3.98/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_29]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_20,plain,
% 3.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.98/0.99      inference(cnf_transformation,[],[f61]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1101,plain,
% 3.98/0.99      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.98/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2274,plain,
% 3.98/0.99      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_1092,c_1101]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_28,negated_conjecture,
% 3.98/0.99      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.98/0.99      inference(cnf_transformation,[],[f71]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1093,plain,
% 3.98/0.99      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2599,plain,
% 3.98/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 3.98/0.99      inference(demodulation,[status(thm)],[c_2274,c_1093]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_26,plain,
% 3.98/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | k1_relset_1(X1,X2,X0) = X1
% 3.98/0.99      | k1_xboole_0 = X2 ),
% 3.98/0.99      inference(cnf_transformation,[],[f62]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1095,plain,
% 3.98/0.99      ( k1_relset_1(X0,X1,X2) = X0
% 3.98/0.99      | k1_xboole_0 = X1
% 3.98/0.99      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.98/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_3264,plain,
% 3.98/0.99      ( k1_relset_1(sK4,sK5,sK7) = sK4
% 3.98/0.99      | sK5 = k1_xboole_0
% 3.98/0.99      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_1092,c_1095]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_19,plain,
% 3.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f60]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1102,plain,
% 3.98/0.99      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.98/0.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1815,plain,
% 3.98/0.99      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_1092,c_1102]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_3268,plain,
% 3.98/0.99      ( k1_relat_1(sK7) = sK4
% 3.98/0.99      | sK5 = k1_xboole_0
% 3.98/0.99      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 3.98/0.99      inference(demodulation,[status(thm)],[c_3264,c_1815]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_30,negated_conjecture,
% 3.98/0.99      ( v1_funct_2(sK7,sK4,sK5) ),
% 3.98/0.99      inference(cnf_transformation,[],[f69]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_33,plain,
% 3.98/0.99      ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_3486,plain,
% 3.98/0.99      ( sK5 = k1_xboole_0 | k1_relat_1(sK7) = sK4 ),
% 3.98/0.99      inference(global_propositional_subsumption,[status(thm)],[c_3268,c_33]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_3487,plain,
% 3.98/0.99      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 3.98/0.99      inference(renaming,[status(thm)],[c_3486]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_17,plain,
% 3.98/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.98/0.99      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 3.98/0.99      | ~ v1_funct_1(X1)
% 3.98/0.99      | ~ v1_relat_1(X1) ),
% 3.98/0.99      inference(cnf_transformation,[],[f77]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1104,plain,
% 3.98/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.98/0.99      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
% 3.98/0.99      | v1_funct_1(X1) != iProver_top
% 3.98/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4189,plain,
% 3.98/0.99      ( sK5 = k1_xboole_0
% 3.98/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.98/0.99      | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top
% 3.98/0.99      | v1_funct_1(sK7) != iProver_top
% 3.98/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_3487,c_1104]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_31,negated_conjecture,
% 3.98/0.99      ( v1_funct_1(sK7) ),
% 3.98/0.99      inference(cnf_transformation,[],[f68]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_32,plain,
% 3.98/0.99      ( v1_funct_1(sK7) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_3,plain,
% 3.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1) ),
% 3.98/0.99      inference(cnf_transformation,[],[f43]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1117,plain,
% 3.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.98/0.99      | r1_tarski(X0,X1) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1675,plain,
% 3.98/0.99      ( r1_tarski(sK7,k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_1092,c_1117]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4,plain,
% 3.98/0.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f45]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2,plain,
% 3.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.98/0.99      inference(cnf_transformation,[],[f44]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_222,plain,
% 3.98/0.99      ( ~ r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1)) ),
% 3.98/0.99      inference(prop_impl,[status(thm)],[c_2]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_223,plain,
% 3.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.98/0.99      inference(renaming,[status(thm)],[c_222]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_289,plain,
% 3.98/0.99      ( ~ r1_tarski(X0,X1) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.98/0.99      inference(bin_hyper_res,[status(thm)],[c_4,c_223]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1089,plain,
% 3.98/0.99      ( r1_tarski(X0,X1) != iProver_top
% 3.98/0.99      | v1_relat_1(X1) != iProver_top
% 3.98/0.99      | v1_relat_1(X0) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_289]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2079,plain,
% 3.98/0.99      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 3.98/0.99      | v1_relat_1(sK7) = iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_1675,c_1089]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_5,plain,
% 3.98/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.98/0.99      inference(cnf_transformation,[],[f46]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1116,plain,
% 3.98/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2170,plain,
% 3.98/0.99      ( v1_relat_1(sK7) = iProver_top ),
% 3.98/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_2079,c_1116]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_5309,plain,
% 3.98/0.99      ( sK5 = k1_xboole_0
% 3.98/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.98/0.99      | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_4189,c_32,c_2170]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1,plain,
% 3.98/0.99      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.98/0.99      inference(cnf_transformation,[],[f42]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1119,plain,
% 3.98/0.99      ( r2_hidden(X0,X1) != iProver_top | m1_subset_1(X0,X1) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_5319,plain,
% 3.98/0.99      ( sK5 = k1_xboole_0
% 3.98/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.98/0.99      | m1_subset_1(sK3(sK7,X1,X0),sK4) = iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_5309,c_1119]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_16,plain,
% 3.98/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.98/0.99      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.98/0.99      | ~ v1_funct_1(X1)
% 3.98/0.99      | ~ v1_relat_1(X1) ),
% 3.98/0.99      inference(cnf_transformation,[],[f76]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1105,plain,
% 3.98/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.98/0.99      | r2_hidden(sK3(X1,X2,X0),X2) = iProver_top
% 3.98/0.99      | v1_funct_1(X1) != iProver_top
% 3.98/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_15,plain,
% 3.98/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.98/0.99      | ~ v1_funct_1(X1)
% 3.98/0.99      | ~ v1_relat_1(X1)
% 3.98/0.99      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
% 3.98/0.99      inference(cnf_transformation,[],[f75]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1106,plain,
% 3.98/0.99      ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
% 3.98/0.99      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 3.98/0.99      | v1_funct_1(X0) != iProver_top
% 3.98/0.99      | v1_relat_1(X0) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_4403,plain,
% 3.98/0.99      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8
% 3.98/0.99      | v1_funct_1(sK7) != iProver_top
% 3.98/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_2599,c_1106]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_5039,plain,
% 3.98/0.99      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_4403,c_32,c_2170]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_27,negated_conjecture,
% 3.98/0.99      ( ~ r2_hidden(X0,sK6)
% 3.98/0.99      | ~ m1_subset_1(X0,sK4)
% 3.98/0.99      | k1_funct_1(sK7,X0) != sK8 ),
% 3.98/0.99      inference(cnf_transformation,[],[f72]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1094,plain,
% 3.98/0.99      ( k1_funct_1(sK7,X0) != sK8
% 3.98/0.99      | r2_hidden(X0,sK6) != iProver_top
% 3.98/0.99      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_5043,plain,
% 3.98/0.99      ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
% 3.98/0.99      | m1_subset_1(sK3(sK7,sK6,sK8),sK4) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_5039,c_1094]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_5065,plain,
% 3.98/0.99      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 3.98/0.99      | m1_subset_1(sK3(sK7,sK6,sK8),sK4) != iProver_top
% 3.98/0.99      | v1_funct_1(sK7) != iProver_top
% 3.98/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_1105,c_5043]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_5170,plain,
% 3.98/0.99      ( m1_subset_1(sK3(sK7,sK6,sK8),sK4) != iProver_top ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_5065,c_32,c_2170,c_2599]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6204,plain,
% 3.98/0.99      ( sK5 = k1_xboole_0 | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_5319,c_5170]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6207,plain,
% 3.98/0.99      ( sK5 = k1_xboole_0 ),
% 3.98/0.99      inference(global_propositional_subsumption,[status(thm)],[c_6204,c_2599]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6214,plain,
% 3.98/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0))) = iProver_top ),
% 3.98/0.99      inference(demodulation,[status(thm)],[c_6207,c_1092]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_22,plain,
% 3.98/0.99      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.98/0.99      | k1_xboole_0 = X1
% 3.98/0.99      | k1_xboole_0 = X0 ),
% 3.98/0.99      inference(cnf_transformation,[],[f80]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1099,plain,
% 3.98/0.99      ( k1_xboole_0 = X0
% 3.98/0.99      | k1_xboole_0 = X1
% 3.98/0.99      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 3.98/0.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6346,plain,
% 3.98/0.99      ( sK4 = k1_xboole_0
% 3.98/0.99      | sK7 = k1_xboole_0
% 3.98/0.99      | v1_funct_2(sK7,sK4,k1_xboole_0) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_6214,c_1099]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_370,plain,( X0 = X0 ),theory(equality) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_397,plain,
% 3.98/0.99      ( k1_xboole_0 = k1_xboole_0 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_370]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1666,plain,
% 3.98/0.99      ( sK7 = sK7 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_370]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_383,plain,
% 3.98/0.99      ( ~ v1_funct_2(X0,X1,X2)
% 3.98/0.99      | v1_funct_2(X3,X4,X5)
% 3.98/0.99      | X3 != X0
% 3.98/0.99      | X4 != X1
% 3.98/0.99      | X5 != X2 ),
% 3.98/0.99      theory(equality) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1508,plain,
% 3.98/0.99      ( v1_funct_2(X0,X1,X2)
% 3.98/0.99      | ~ v1_funct_2(sK7,sK4,sK5)
% 3.98/0.99      | X2 != sK5
% 3.98/0.99      | X1 != sK4
% 3.98/0.99      | X0 != sK7 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_383]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1665,plain,
% 3.98/0.99      ( v1_funct_2(sK7,X0,X1)
% 3.98/0.99      | ~ v1_funct_2(sK7,sK4,sK5)
% 3.98/0.99      | X1 != sK5
% 3.98/0.99      | X0 != sK4
% 3.98/0.99      | sK7 != sK7 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1508]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1891,plain,
% 3.98/0.99      ( v1_funct_2(sK7,sK4,X0)
% 3.98/0.99      | ~ v1_funct_2(sK7,sK4,sK5)
% 3.98/0.99      | X0 != sK5
% 3.98/0.99      | sK4 != sK4
% 3.98/0.99      | sK7 != sK7 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1665]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1893,plain,
% 3.98/0.99      ( X0 != sK5
% 3.98/0.99      | sK4 != sK4
% 3.98/0.99      | sK7 != sK7
% 3.98/0.99      | v1_funct_2(sK7,sK4,X0) = iProver_top
% 3.98/0.99      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_1891]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1895,plain,
% 3.98/0.99      ( sK4 != sK4
% 3.98/0.99      | sK7 != sK7
% 3.98/0.99      | k1_xboole_0 != sK5
% 3.98/0.99      | v1_funct_2(sK7,sK4,sK5) != iProver_top
% 3.98/0.99      | v1_funct_2(sK7,sK4,k1_xboole_0) = iProver_top ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1893]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1892,plain,
% 3.98/0.99      ( sK4 = sK4 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_370]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_371,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2368,plain,
% 3.98/0.99      ( X0 != X1 | X0 = sK5 | sK5 != X1 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_371]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2369,plain,
% 3.98/0.99      ( sK5 != k1_xboole_0 | k1_xboole_0 = sK5 | k1_xboole_0 != k1_xboole_0 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_2368]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6702,plain,
% 3.98/0.99      ( sK7 = k1_xboole_0 | sK4 = k1_xboole_0 ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_6346,c_33,c_397,c_1666,c_1895,c_1892,c_2369,c_2599,c_6204]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6703,plain,
% 3.98/0.99      ( sK4 = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 3.98/0.99      inference(renaming,[status(thm)],[c_6702]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1091,plain,
% 3.98/0.99      ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_30]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6215,plain,
% 3.98/0.99      ( v1_funct_2(sK7,sK4,k1_xboole_0) = iProver_top ),
% 3.98/0.99      inference(demodulation,[status(thm)],[c_6207,c_1091]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6710,plain,
% 3.98/0.99      ( sK7 = k1_xboole_0
% 3.98/0.99      | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_6703,c_6215]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_6709,plain,
% 3.98/0.99      ( sK7 = k1_xboole_0
% 3.98/0.99      | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_6703,c_6214]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_0,plain,
% 3.98/0.99      ( r1_tarski(k1_xboole_0,X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f41]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1614,plain,
% 3.98/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_0]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1615,plain,
% 3.98/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_1614]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1617,plain,
% 3.98/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1615]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_372,plain,
% 3.98/0.99      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 3.98/0.99      theory(equality) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1632,plain,
% 3.98/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.98/0.99      | r1_tarski(X3,k2_zfmisc_1(X1,X2))
% 3.98/0.99      | X3 != X0 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_372]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2159,plain,
% 3.98/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.98/0.99      | r1_tarski(sK7,k2_zfmisc_1(X1,X2))
% 3.98/0.99      | sK7 != X0 ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1632]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2160,plain,
% 3.98/0.99      ( sK7 != X0
% 3.98/0.99      | r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.98/0.99      | r1_tarski(sK7,k2_zfmisc_1(X1,X2)) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_2159]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2162,plain,
% 3.98/0.99      ( sK7 != k1_xboole_0
% 3.98/0.99      | r1_tarski(sK7,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top
% 3.98/0.99      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_2160]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1461,plain,
% 3.98/0.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.98/0.99      | ~ r1_tarski(X0,k2_zfmisc_1(X1,X2)) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_2]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2680,plain,
% 3.98/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.98/0.99      | ~ r1_tarski(sK7,k2_zfmisc_1(X0,X1)) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1461]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2681,plain,
% 3.98/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 3.98/0.99      | r1_tarski(sK7,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_2680]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2683,plain,
% 3.98/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.98/0.99      | r1_tarski(sK7,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_2681]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7616,plain,
% 3.98/0.99      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_6709,c_1617,c_2162,c_2683]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7624,plain,
% 3.98/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_relat_1(sK7) ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_7616,c_1102]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_25,plain,
% 3.98/0.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.98/0.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.98/0.99      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.98/0.99      inference(cnf_transformation,[],[f82]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1096,plain,
% 3.98/0.99      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 3.98/0.99      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 3.98/0.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7626,plain,
% 3.98/0.99      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK7) = k1_xboole_0
% 3.98/0.99      | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_7616,c_1096]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7632,plain,
% 3.98/0.99      ( k1_relat_1(sK7) = k1_xboole_0
% 3.98/0.99      | v1_funct_2(sK7,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.98/0.99      inference(demodulation,[status(thm)],[c_7624,c_7626]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_8740,plain,
% 3.98/0.99      ( k1_relat_1(sK7) = k1_xboole_0 | sK7 = k1_xboole_0 ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_6710,c_7632]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_9,plain,
% 3.98/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.98/0.99      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1))
% 3.98/0.99      | ~ v1_relat_1(X1) ),
% 3.98/0.99      inference(cnf_transformation,[],[f47]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1112,plain,
% 3.98/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.98/0.99      | r2_hidden(sK0(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 3.98/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_18,plain,
% 3.98/0.99      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.98/0.99      inference(cnf_transformation,[],[f59]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1103,plain,
% 3.98/0.99      ( r2_hidden(X0,X1) != iProver_top | r1_tarski(X1,X0) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_2444,plain,
% 3.98/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.98/0.99      | r1_tarski(k1_relat_1(X1),sK0(X0,X2,X1)) != iProver_top
% 3.98/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_1112,c_1103]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_9066,plain,
% 3.98/0.99      ( sK7 = k1_xboole_0
% 3.98/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.98/0.99      | r1_tarski(k1_xboole_0,sK0(X0,X1,sK7)) != iProver_top
% 3.98/0.99      | v1_relat_1(sK7) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_8740,c_2444]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_9137,plain,
% 3.98/0.99      ( r1_tarski(k1_xboole_0,sK0(X0,X1,sK7)) != iProver_top
% 3.98/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.98/0.99      | sK7 = k1_xboole_0 ),
% 3.98/0.99      inference(global_propositional_subsumption,[status(thm)],[c_9066,c_2170]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_9138,plain,
% 3.98/0.99      ( sK7 = k1_xboole_0
% 3.98/0.99      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.98/0.99      | r1_tarski(k1_xboole_0,sK0(X0,X1,sK7)) != iProver_top ),
% 3.98/0.99      inference(renaming,[status(thm)],[c_9137]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1120,plain,
% 3.98/0.99      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_9146,plain,
% 3.98/0.99      ( sK7 = k1_xboole_0 | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top ),
% 3.98/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_9138,c_1120]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_9158,plain,
% 3.98/0.99      ( sK7 = k1_xboole_0 ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_2599,c_9146]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_9303,plain,
% 3.98/0.99      ( r2_hidden(sK8,k9_relat_1(k1_xboole_0,sK6)) = iProver_top ),
% 3.98/0.99      inference(demodulation,[status(thm)],[c_9158,c_2599]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_8,plain,
% 3.98/0.99      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.98/0.99      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.98/0.99      | ~ v1_relat_1(X1) ),
% 3.98/0.99      inference(cnf_transformation,[],[f48]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1113,plain,
% 3.98/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.98/0.99      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.98/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_3035,plain,
% 3.98/0.99      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.98/0.99      | r1_tarski(X1,k4_tarski(sK0(X0,X2,X1),X0)) != iProver_top
% 3.98/0.99      | v1_relat_1(X1) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_1113,c_1103]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7994,plain,
% 3.98/0.99      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top
% 3.98/0.99      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.98/0.99      inference(superposition,[status(thm)],[c_1120,c_3035]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_102,plain,
% 3.98/0.99      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_104,plain,
% 3.98/0.99      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_102]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1553,plain,
% 3.98/0.99      ( ~ r1_tarski(X0,k2_zfmisc_1(X1,X2))
% 3.98/0.99      | v1_relat_1(X0)
% 3.98/0.99      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_289]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1554,plain,
% 3.98/0.99      ( r1_tarski(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 3.98/0.99      | v1_relat_1(X0) = iProver_top
% 3.98/0.99      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.98/0.99      inference(predicate_to_equality,[status(thm)],[c_1553]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_1556,plain,
% 3.98/0.99      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.98/0.99      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.98/0.99      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.98/0.99      inference(instantiation,[status(thm)],[c_1554]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_7997,plain,
% 3.98/0.99      ( r2_hidden(X0,k9_relat_1(k1_xboole_0,X1)) != iProver_top ),
% 3.98/0.99      inference(global_propositional_subsumption,
% 3.98/0.99                [status(thm)],
% 3.98/0.99                [c_7994,c_104,c_1556,c_1617]) ).
% 3.98/0.99  
% 3.98/0.99  cnf(c_10152,plain,
% 3.98/0.99      ( $false ),
% 3.98/0.99      inference(forward_subsumption_resolution,[status(thm)],[c_9303,c_7997]) ).
% 3.98/0.99  
% 3.98/0.99  
% 3.98/0.99  % SZS output end CNFRefutation for theBenchmark.p
% 3.98/0.99  
% 3.98/0.99  ------                               Statistics
% 3.98/0.99  
% 3.98/0.99  ------ Selected
% 3.98/0.99  
% 3.98/0.99  total_time:                             0.287
% 3.98/0.99  
%------------------------------------------------------------------------------
