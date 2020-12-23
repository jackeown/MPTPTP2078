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
% DateTime   : Thu Dec  3 12:08:02 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 468 expanded)
%              Number of clauses        :  101 ( 162 expanded)
%              Number of leaves         :   24 ( 107 expanded)
%              Depth                    :   19
%              Number of atoms          :  651 (2245 expanded)
%              Number of equality atoms :  252 ( 552 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
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

fof(f20,negated_conjecture,(
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
    inference(negated_conjecture,[],[f19])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f61,plain,(
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

fof(f60,plain,
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

fof(f62,plain,
    ( ! [X5] :
        ( k1_funct_1(sK7,X5) != sK8
        | ~ r2_hidden(X5,sK6)
        | ~ m1_subset_1(X5,sK4) )
    & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK7,sK4,sK5)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f43,f61,f60])).

fof(f104,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f62])).

fof(f18,axiom,(
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

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f59,plain,(
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
    inference(nnf_transformation,[],[f41])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f103,plain,(
    v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f62])).

fof(f12,axiom,(
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

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f53,plain,(
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
    inference(nnf_transformation,[],[f34])).

fof(f54,plain,(
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
    inference(rectify,[],[f53])).

fof(f57,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f55,plain,(
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

fof(f58,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f54,f57,f56,f55])).

fof(f83,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f115,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f83])).

fof(f102,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f62])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f84,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f114,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f95,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f105,plain,(
    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f62])).

fof(f85,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f113,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f85])).

fof(f106,plain,(
    ! [X5] :
      ( k1_funct_1(sK7,X5) != sK8
      | ~ r2_hidden(X5,sK6)
      | ~ m1_subset_1(X5,sK4) ) ),
    inference(cnf_transformation,[],[f62])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f44])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f45])).

fof(f107,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f64])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v5_relat_1(X1,X0)
      | ~ r1_tarski(k2_relat_1(X1),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X1))
         => v5_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v5_relat_1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f8,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f75,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f8])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f49,plain,(
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
    inference(nnf_transformation,[],[f28])).

fof(f50,plain,(
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
    inference(rectify,[],[f49])).

fof(f51,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK0(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
        & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(k4_tarski(X0,X1),X2)
       => ( r2_hidden(X1,k2_relat_1(X2))
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X1,k2_relat_1(X2))
        & r2_hidden(X0,k1_relat_1(X2)) )
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f31])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X1,k2_relat_1(X2))
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k2_relat_1(X1))
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,k2_relat_1(X1)) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,k2_relat_1(X1))
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f13,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f91,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
    <=> ( k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(nnf_transformation,[],[f2])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( k2_zfmisc_1(X0,X1) = k1_xboole_0
        | ( k1_xboole_0 != X1
          & k1_xboole_0 != X0 ) )
      & ( k1_xboole_0 = X1
        | k1_xboole_0 = X0
        | k2_zfmisc_1(X0,X1) != k1_xboole_0 ) ) ),
    inference(flattening,[],[f46])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k2_zfmisc_1(X0,X1) = k1_xboole_0
      | k1_xboole_0 != X1 ) ),
    inference(cnf_transformation,[],[f47])).

fof(f109,plain,(
    ! [X0] : k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(equality_resolution,[],[f68])).

fof(f3,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f69,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f15])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f73,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_41,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1196,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_38,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f96])).

cnf(c_1199,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38])).

cnf(c_6566,plain,
    ( k1_relset_1(sK4,sK5,sK7) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1199])).

cnf(c_31,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f94])).

cnf(c_1206,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_31])).

cnf(c_2655,plain,
    ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_1196,c_1206])).

cnf(c_6576,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0
    | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
    inference(demodulation,[status(thm)],[c_6566,c_2655])).

cnf(c_42,negated_conjecture,
    ( v1_funct_2(sK7,sK4,sK5) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_45,plain,
    ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_42])).

cnf(c_7109,plain,
    ( sK5 = k1_xboole_0
    | k1_relat_1(sK7) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_6576,c_45])).

cnf(c_7110,plain,
    ( k1_relat_1(sK7) = sK4
    | sK5 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7109])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f115])).

cnf(c_1210,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_7114,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7110,c_1210])).

cnf(c_43,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f102])).

cnf(c_44,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_43])).

cnf(c_46,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_41])).

cnf(c_29,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f92])).

cnf(c_1632,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1633,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1632])).

cnf(c_9805,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7114,c_44,c_46,c_1633])).

cnf(c_7,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1230,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | m1_subset_1(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_7])).

cnf(c_9815,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | m1_subset_1(sK3(sK7,X1,X0),sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_9805,c_1230])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f114])).

cnf(c_1211,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_32,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f95])).

cnf(c_1205,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_3322,plain,
    ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1196,c_1205])).

cnf(c_40,negated_conjecture,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1197,plain,
    ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_40])).

cnf(c_3743,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3322,c_1197])).

cnf(c_25,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f113])).

cnf(c_1212,plain,
    ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_4182,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3743,c_1212])).

cnf(c_4454,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4182,c_44,c_46,c_1633])).

cnf(c_39,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | ~ m1_subset_1(X0,sK4)
    | k1_funct_1(sK7,X0) != sK8 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1198,plain,
    ( k1_funct_1(sK7,X0) != sK8
    | r2_hidden(X0,sK6) != iProver_top
    | m1_subset_1(X0,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_4457,plain,
    ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
    | m1_subset_1(sK3(sK7,sK6,sK8),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_4454,c_1198])).

cnf(c_4462,plain,
    ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
    | m1_subset_1(sK3(sK7,sK6,sK8),sK4) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1211,c_4457])).

cnf(c_4561,plain,
    ( m1_subset_1(sK3(sK7,sK6,sK8),sK4) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4462,c_44,c_46,c_1633,c_3743])).

cnf(c_10888,plain,
    ( sK5 = k1_xboole_0
    | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9815,c_4561])).

cnf(c_11020,plain,
    ( sK5 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10888,c_3743])).

cnf(c_1,plain,
    ( r1_tarski(X0,X0) ),
    inference(cnf_transformation,[],[f107])).

cnf(c_1232,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_10,plain,
    ( v5_relat_1(X0,X1)
    | ~ r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f74])).

cnf(c_1227,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | r1_tarski(k2_relat_1(X0),X1) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3537,plain,
    ( v5_relat_1(X0,k2_relat_1(X0)) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1232,c_1227])).

cnf(c_9,plain,
    ( ~ v5_relat_1(X0,X1)
    | v5_relat_1(X2,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1228,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | v5_relat_1(X2,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_6452,plain,
    ( v5_relat_1(k2_zfmisc_1(sK4,sK5),X0) != iProver_top
    | v5_relat_1(sK7,X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1196,c_1228])).

cnf(c_3580,plain,
    ( ~ v5_relat_1(k2_zfmisc_1(sK4,sK5),X0)
    | v5_relat_1(sK7,X0)
    | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(resolution,[status(thm)],[c_9,c_41])).

cnf(c_12,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_3966,plain,
    ( ~ v5_relat_1(k2_zfmisc_1(sK4,sK5),X0)
    | v5_relat_1(sK7,X0) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3580,c_12])).

cnf(c_3967,plain,
    ( v5_relat_1(k2_zfmisc_1(sK4,sK5),X0) != iProver_top
    | v5_relat_1(sK7,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3966])).

cnf(c_6944,plain,
    ( v5_relat_1(sK7,X0) = iProver_top
    | v5_relat_1(k2_zfmisc_1(sK4,sK5),X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6452,c_3967])).

cnf(c_6945,plain,
    ( v5_relat_1(k2_zfmisc_1(sK4,sK5),X0) != iProver_top
    | v5_relat_1(sK7,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_6944])).

cnf(c_6950,plain,
    ( v5_relat_1(sK7,k2_relat_1(k2_zfmisc_1(sK4,sK5))) = iProver_top
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3537,c_6945])).

cnf(c_1225,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7106,plain,
    ( v5_relat_1(sK7,k2_relat_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6950,c_1225])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1222,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_18,plain,
    ( r2_hidden(X0,k2_relat_1(X1))
    | ~ r2_hidden(k4_tarski(X2,X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f82])).

cnf(c_1219,plain,
    ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_5371,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(X0,k2_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1222,c_1219])).

cnf(c_8087,plain,
    ( r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3743,c_5371])).

cnf(c_8457,plain,
    ( r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8087,c_46,c_1633])).

cnf(c_17,plain,
    ( ~ v5_relat_1(X0,X1)
    | r2_hidden(X2,X1)
    | ~ r2_hidden(X2,k2_relat_1(X0))
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f80])).

cnf(c_1220,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,X1) = iProver_top
    | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_8464,plain,
    ( v5_relat_1(sK7,X0) != iProver_top
    | r2_hidden(sK8,X0) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8457,c_1220])).

cnf(c_8615,plain,
    ( r2_hidden(sK8,X0) = iProver_top
    | v5_relat_1(sK7,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_8464,c_46,c_1633])).

cnf(c_8616,plain,
    ( v5_relat_1(sK7,X0) != iProver_top
    | r2_hidden(sK8,X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_8615])).

cnf(c_8625,plain,
    ( r2_hidden(sK8,k2_relat_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
    inference(superposition,[status(thm)],[c_7106,c_8616])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ r1_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f91])).

cnf(c_1209,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r1_tarski(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_10138,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(sK4,sK5)),sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_8625,c_1209])).

cnf(c_11024,plain,
    ( r1_tarski(k2_relat_1(k2_zfmisc_1(sK4,k1_xboole_0)),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11020,c_10138])).

cnf(c_3,plain,
    ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f109])).

cnf(c_11076,plain,
    ( r1_tarski(k2_relat_1(k1_xboole_0),sK8) != iProver_top ),
    inference(demodulation,[status(thm)],[c_11024,c_3])).

cnf(c_6,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1625,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_9763,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) ),
    inference(instantiation,[status(thm)],[c_1625])).

cnf(c_9766,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9763])).

cnf(c_30,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f93])).

cnf(c_4255,plain,
    ( v5_relat_1(X0,sK8)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK8))) ),
    inference(instantiation,[status(thm)],[c_30])).

cnf(c_9762,plain,
    ( v5_relat_1(k1_xboole_0,sK8)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) ),
    inference(instantiation,[status(thm)],[c_4255])).

cnf(c_9764,plain,
    ( v5_relat_1(k1_xboole_0,sK8) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9762])).

cnf(c_11,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f73])).

cnf(c_2479,plain,
    ( ~ v5_relat_1(X0,sK8)
    | r1_tarski(k2_relat_1(X0),sK8)
    | ~ v1_relat_1(X0) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_2481,plain,
    ( v5_relat_1(X0,sK8) != iProver_top
    | r1_tarski(k2_relat_1(X0),sK8) = iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2479])).

cnf(c_2483,plain,
    ( v5_relat_1(k1_xboole_0,sK8) != iProver_top
    | r1_tarski(k2_relat_1(k1_xboole_0),sK8) = iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2481])).

cnf(c_1628,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1625])).

cnf(c_1624,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_29])).

cnf(c_1626,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1624])).

cnf(c_11096,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK8))) = iProver_top ),
    inference(grounding,[status(thm)],[c_9766:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_11097,plain,
    ( v5_relat_1(k1_xboole_0,sK8) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK8))) != iProver_top ),
    inference(grounding,[status(thm)],[c_9764:[bind(X0,$fot(k1_xboole_0))]])).

cnf(c_11098,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(grounding,[status(thm)],[c_1628:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(c_11099,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(grounding,[status(thm)],[c_1626:[bind(X1,$fot(k1_xboole_0)),bind(X0,$fot(k1_xboole_0))]])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_11076,c_11096,c_11097,c_2483,c_11098,c_11099])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 11:32:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  % Running in FOF mode
% 3.89/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.03  
% 3.89/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.89/1.03  
% 3.89/1.03  ------  iProver source info
% 3.89/1.03  
% 3.89/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.89/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.89/1.03  git: non_committed_changes: false
% 3.89/1.03  git: last_make_outside_of_git: false
% 3.89/1.03  
% 3.89/1.03  ------ 
% 3.89/1.03  ------ Parsing...
% 3.89/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.89/1.03  
% 3.89/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.89/1.03  ------ Proving...
% 3.89/1.03  ------ Problem Properties 
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  clauses                                 43
% 3.89/1.03  conjectures                             5
% 3.89/1.03  EPR                                     6
% 3.89/1.03  Horn                                    35
% 3.89/1.03  unary                                   9
% 3.89/1.03  binary                                  6
% 3.89/1.03  lits                                    127
% 3.89/1.03  lits eq                                 25
% 3.89/1.03  fd_pure                                 0
% 3.89/1.03  fd_pseudo                               0
% 3.89/1.03  fd_cond                                 4
% 3.89/1.03  fd_pseudo_cond                          5
% 3.89/1.03  AC symbols                              0
% 3.89/1.03  
% 3.89/1.03  ------ Input Options Time Limit: Unbounded
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ 
% 3.89/1.03  Current options:
% 3.89/1.03  ------ 
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  ------ Proving...
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  % SZS status Theorem for theBenchmark.p
% 3.89/1.03  
% 3.89/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.89/1.03  
% 3.89/1.03  fof(f19,conjecture,(
% 3.89/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f20,negated_conjecture,(
% 3.89/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.89/1.03    inference(negated_conjecture,[],[f19])).
% 3.89/1.03  
% 3.89/1.03  fof(f42,plain,(
% 3.89/1.03    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.89/1.03    inference(ennf_transformation,[],[f20])).
% 3.89/1.03  
% 3.89/1.03  fof(f43,plain,(
% 3.89/1.03    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.89/1.03    inference(flattening,[],[f42])).
% 3.89/1.03  
% 3.89/1.03  fof(f61,plain,(
% 3.89/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK8 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK8,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.89/1.03    introduced(choice_axiom,[])).
% 3.89/1.03  
% 3.89/1.03  fof(f60,plain,(
% 3.89/1.03    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK7,X5) != X4 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(X4,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7))),
% 3.89/1.03    introduced(choice_axiom,[])).
% 3.89/1.03  
% 3.89/1.03  fof(f62,plain,(
% 3.89/1.03    (! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) & r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK7,sK4,sK5) & v1_funct_1(sK7)),
% 3.89/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7,sK8])],[f43,f61,f60])).
% 3.89/1.03  
% 3.89/1.03  fof(f104,plain,(
% 3.89/1.03    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 3.89/1.03    inference(cnf_transformation,[],[f62])).
% 3.89/1.03  
% 3.89/1.03  fof(f18,axiom,(
% 3.89/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f40,plain,(
% 3.89/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.89/1.03    inference(ennf_transformation,[],[f18])).
% 3.89/1.03  
% 3.89/1.03  fof(f41,plain,(
% 3.89/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.89/1.03    inference(flattening,[],[f40])).
% 3.89/1.03  
% 3.89/1.03  fof(f59,plain,(
% 3.89/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.89/1.03    inference(nnf_transformation,[],[f41])).
% 3.89/1.03  
% 3.89/1.03  fof(f96,plain,(
% 3.89/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.89/1.03    inference(cnf_transformation,[],[f59])).
% 3.89/1.03  
% 3.89/1.03  fof(f16,axiom,(
% 3.89/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f38,plain,(
% 3.89/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.89/1.03    inference(ennf_transformation,[],[f16])).
% 3.89/1.03  
% 3.89/1.03  fof(f94,plain,(
% 3.89/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.89/1.03    inference(cnf_transformation,[],[f38])).
% 3.89/1.03  
% 3.89/1.03  fof(f103,plain,(
% 3.89/1.03    v1_funct_2(sK7,sK4,sK5)),
% 3.89/1.03    inference(cnf_transformation,[],[f62])).
% 3.89/1.03  
% 3.89/1.03  fof(f12,axiom,(
% 3.89/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f33,plain,(
% 3.89/1.03    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.89/1.03    inference(ennf_transformation,[],[f12])).
% 3.89/1.03  
% 3.89/1.03  fof(f34,plain,(
% 3.89/1.03    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.89/1.03    inference(flattening,[],[f33])).
% 3.89/1.03  
% 3.89/1.03  fof(f53,plain,(
% 3.89/1.03    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.89/1.03    inference(nnf_transformation,[],[f34])).
% 3.89/1.03  
% 3.89/1.03  fof(f54,plain,(
% 3.89/1.03    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.89/1.03    inference(rectify,[],[f53])).
% 3.89/1.03  
% 3.89/1.03  fof(f57,plain,(
% 3.89/1.03    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 3.89/1.03    introduced(choice_axiom,[])).
% 3.89/1.03  
% 3.89/1.03  fof(f56,plain,(
% 3.89/1.03    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 3.89/1.03    introduced(choice_axiom,[])).
% 3.89/1.03  
% 3.89/1.03  fof(f55,plain,(
% 3.89/1.03    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 3.89/1.03    introduced(choice_axiom,[])).
% 3.89/1.03  
% 3.89/1.03  fof(f58,plain,(
% 3.89/1.03    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.89/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f54,f57,f56,f55])).
% 3.89/1.03  
% 3.89/1.03  fof(f83,plain,(
% 3.89/1.03    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f58])).
% 3.89/1.03  
% 3.89/1.03  fof(f115,plain,(
% 3.89/1.03    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.89/1.03    inference(equality_resolution,[],[f83])).
% 3.89/1.03  
% 3.89/1.03  fof(f102,plain,(
% 3.89/1.03    v1_funct_1(sK7)),
% 3.89/1.03    inference(cnf_transformation,[],[f62])).
% 3.89/1.03  
% 3.89/1.03  fof(f14,axiom,(
% 3.89/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f36,plain,(
% 3.89/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.89/1.03    inference(ennf_transformation,[],[f14])).
% 3.89/1.03  
% 3.89/1.03  fof(f92,plain,(
% 3.89/1.03    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.89/1.03    inference(cnf_transformation,[],[f36])).
% 3.89/1.03  
% 3.89/1.03  fof(f4,axiom,(
% 3.89/1.03    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f22,plain,(
% 3.89/1.03    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 3.89/1.03    inference(ennf_transformation,[],[f4])).
% 3.89/1.03  
% 3.89/1.03  fof(f70,plain,(
% 3.89/1.03    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f22])).
% 3.89/1.03  
% 3.89/1.03  fof(f84,plain,(
% 3.89/1.03    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f58])).
% 3.89/1.03  
% 3.89/1.03  fof(f114,plain,(
% 3.89/1.03    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.89/1.03    inference(equality_resolution,[],[f84])).
% 3.89/1.03  
% 3.89/1.03  fof(f17,axiom,(
% 3.89/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f39,plain,(
% 3.89/1.03    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.89/1.03    inference(ennf_transformation,[],[f17])).
% 3.89/1.03  
% 3.89/1.03  fof(f95,plain,(
% 3.89/1.03    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.89/1.03    inference(cnf_transformation,[],[f39])).
% 3.89/1.03  
% 3.89/1.03  fof(f105,plain,(
% 3.89/1.03    r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6))),
% 3.89/1.03    inference(cnf_transformation,[],[f62])).
% 3.89/1.03  
% 3.89/1.03  fof(f85,plain,(
% 3.89/1.03    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f58])).
% 3.89/1.03  
% 3.89/1.03  fof(f113,plain,(
% 3.89/1.03    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.89/1.03    inference(equality_resolution,[],[f85])).
% 3.89/1.03  
% 3.89/1.03  fof(f106,plain,(
% 3.89/1.03    ( ! [X5] : (k1_funct_1(sK7,X5) != sK8 | ~r2_hidden(X5,sK6) | ~m1_subset_1(X5,sK4)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f62])).
% 3.89/1.03  
% 3.89/1.03  fof(f1,axiom,(
% 3.89/1.03    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f44,plain,(
% 3.89/1.03    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.89/1.03    inference(nnf_transformation,[],[f1])).
% 3.89/1.03  
% 3.89/1.03  fof(f45,plain,(
% 3.89/1.03    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 3.89/1.03    inference(flattening,[],[f44])).
% 3.89/1.03  
% 3.89/1.03  fof(f64,plain,(
% 3.89/1.03    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 3.89/1.03    inference(cnf_transformation,[],[f45])).
% 3.89/1.03  
% 3.89/1.03  fof(f107,plain,(
% 3.89/1.03    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 3.89/1.03    inference(equality_resolution,[],[f64])).
% 3.89/1.03  
% 3.89/1.03  fof(f7,axiom,(
% 3.89/1.03    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f27,plain,(
% 3.89/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 3.89/1.03    inference(ennf_transformation,[],[f7])).
% 3.89/1.03  
% 3.89/1.03  fof(f48,plain,(
% 3.89/1.03    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 3.89/1.03    inference(nnf_transformation,[],[f27])).
% 3.89/1.03  
% 3.89/1.03  fof(f74,plain,(
% 3.89/1.03    ( ! [X0,X1] : (v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f48])).
% 3.89/1.03  
% 3.89/1.03  fof(f6,axiom,(
% 3.89/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X1)) => v5_relat_1(X2,X0)))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f25,plain,(
% 3.89/1.03    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.89/1.03    inference(ennf_transformation,[],[f6])).
% 3.89/1.03  
% 3.89/1.03  fof(f26,plain,(
% 3.89/1.03    ! [X0,X1] : (! [X2] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.89/1.03    inference(flattening,[],[f25])).
% 3.89/1.03  
% 3.89/1.03  fof(f72,plain,(
% 3.89/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f26])).
% 3.89/1.03  
% 3.89/1.03  fof(f8,axiom,(
% 3.89/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f75,plain,(
% 3.89/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.89/1.03    inference(cnf_transformation,[],[f8])).
% 3.89/1.03  
% 3.89/1.03  fof(f9,axiom,(
% 3.89/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f28,plain,(
% 3.89/1.03    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 3.89/1.03    inference(ennf_transformation,[],[f9])).
% 3.89/1.03  
% 3.89/1.03  fof(f49,plain,(
% 3.89/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.89/1.03    inference(nnf_transformation,[],[f28])).
% 3.89/1.03  
% 3.89/1.03  fof(f50,plain,(
% 3.89/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.89/1.03    inference(rectify,[],[f49])).
% 3.89/1.03  
% 3.89/1.03  fof(f51,plain,(
% 3.89/1.03    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))))),
% 3.89/1.03    introduced(choice_axiom,[])).
% 3.89/1.03  
% 3.89/1.03  fof(f52,plain,(
% 3.89/1.03    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK0(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) & r2_hidden(sK0(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 3.89/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f50,f51])).
% 3.89/1.03  
% 3.89/1.03  fof(f77,plain,(
% 3.89/1.03    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK0(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f52])).
% 3.89/1.03  
% 3.89/1.03  fof(f11,axiom,(
% 3.89/1.03    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(k4_tarski(X0,X1),X2) => (r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2)))))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f31,plain,(
% 3.89/1.03    ! [X0,X1,X2] : (((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2)) | ~v1_relat_1(X2))),
% 3.89/1.03    inference(ennf_transformation,[],[f11])).
% 3.89/1.03  
% 3.89/1.03  fof(f32,plain,(
% 3.89/1.03    ! [X0,X1,X2] : ((r2_hidden(X1,k2_relat_1(X2)) & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2))),
% 3.89/1.03    inference(flattening,[],[f31])).
% 3.89/1.03  
% 3.89/1.03  fof(f82,plain,(
% 3.89/1.03    ( ! [X2,X0,X1] : (r2_hidden(X1,k2_relat_1(X2)) | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_relat_1(X2)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f32])).
% 3.89/1.03  
% 3.89/1.03  fof(f10,axiom,(
% 3.89/1.03    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k2_relat_1(X1)) => r2_hidden(X2,X0)))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f29,plain,(
% 3.89/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 3.89/1.03    inference(ennf_transformation,[],[f10])).
% 3.89/1.03  
% 3.89/1.03  fof(f30,plain,(
% 3.89/1.03    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 3.89/1.03    inference(flattening,[],[f29])).
% 3.89/1.03  
% 3.89/1.03  fof(f80,plain,(
% 3.89/1.03    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,k2_relat_1(X1)) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f30])).
% 3.89/1.03  
% 3.89/1.03  fof(f13,axiom,(
% 3.89/1.03    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f35,plain,(
% 3.89/1.03    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 3.89/1.03    inference(ennf_transformation,[],[f13])).
% 3.89/1.03  
% 3.89/1.03  fof(f91,plain,(
% 3.89/1.03    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f35])).
% 3.89/1.03  
% 3.89/1.03  fof(f2,axiom,(
% 3.89/1.03    ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 <=> (k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f46,plain,(
% 3.89/1.03    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & ((k1_xboole_0 = X1 | k1_xboole_0 = X0) | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.89/1.03    inference(nnf_transformation,[],[f2])).
% 3.89/1.03  
% 3.89/1.03  fof(f47,plain,(
% 3.89/1.03    ! [X0,X1] : ((k2_zfmisc_1(X0,X1) = k1_xboole_0 | (k1_xboole_0 != X1 & k1_xboole_0 != X0)) & (k1_xboole_0 = X1 | k1_xboole_0 = X0 | k2_zfmisc_1(X0,X1) != k1_xboole_0))),
% 3.89/1.03    inference(flattening,[],[f46])).
% 3.89/1.03  
% 3.89/1.03  fof(f68,plain,(
% 3.89/1.03    ( ! [X0,X1] : (k2_zfmisc_1(X0,X1) = k1_xboole_0 | k1_xboole_0 != X1) )),
% 3.89/1.03    inference(cnf_transformation,[],[f47])).
% 3.89/1.03  
% 3.89/1.03  fof(f109,plain,(
% 3.89/1.03    ( ! [X0] : (k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0) )),
% 3.89/1.03    inference(equality_resolution,[],[f68])).
% 3.89/1.03  
% 3.89/1.03  fof(f3,axiom,(
% 3.89/1.03    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f69,plain,(
% 3.89/1.03    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 3.89/1.03    inference(cnf_transformation,[],[f3])).
% 3.89/1.03  
% 3.89/1.03  fof(f15,axiom,(
% 3.89/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 3.89/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.89/1.03  
% 3.89/1.03  fof(f21,plain,(
% 3.89/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 3.89/1.03    inference(pure_predicate_removal,[],[f15])).
% 3.89/1.03  
% 3.89/1.03  fof(f37,plain,(
% 3.89/1.03    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.89/1.03    inference(ennf_transformation,[],[f21])).
% 3.89/1.03  
% 3.89/1.03  fof(f93,plain,(
% 3.89/1.03    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.89/1.03    inference(cnf_transformation,[],[f37])).
% 3.89/1.03  
% 3.89/1.03  fof(f73,plain,(
% 3.89/1.03    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 3.89/1.03    inference(cnf_transformation,[],[f48])).
% 3.89/1.03  
% 3.89/1.03  cnf(c_41,negated_conjecture,
% 3.89/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 3.89/1.03      inference(cnf_transformation,[],[f104]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1196,plain,
% 3.89/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_38,plain,
% 3.89/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.89/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.89/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.89/1.03      | k1_xboole_0 = X2 ),
% 3.89/1.03      inference(cnf_transformation,[],[f96]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1199,plain,
% 3.89/1.03      ( k1_relset_1(X0,X1,X2) = X0
% 3.89/1.03      | k1_xboole_0 = X1
% 3.89/1.03      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.89/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_38]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_6566,plain,
% 3.89/1.03      ( k1_relset_1(sK4,sK5,sK7) = sK4
% 3.89/1.03      | sK5 = k1_xboole_0
% 3.89/1.03      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_1196,c_1199]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_31,plain,
% 3.89/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.89/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.89/1.03      inference(cnf_transformation,[],[f94]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1206,plain,
% 3.89/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.89/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_31]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2655,plain,
% 3.89/1.03      ( k1_relset_1(sK4,sK5,sK7) = k1_relat_1(sK7) ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_1196,c_1206]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_6576,plain,
% 3.89/1.03      ( k1_relat_1(sK7) = sK4
% 3.89/1.03      | sK5 = k1_xboole_0
% 3.89/1.03      | v1_funct_2(sK7,sK4,sK5) != iProver_top ),
% 3.89/1.03      inference(demodulation,[status(thm)],[c_6566,c_2655]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_42,negated_conjecture,
% 3.89/1.03      ( v1_funct_2(sK7,sK4,sK5) ),
% 3.89/1.03      inference(cnf_transformation,[],[f103]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_45,plain,
% 3.89/1.03      ( v1_funct_2(sK7,sK4,sK5) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_42]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_7109,plain,
% 3.89/1.03      ( sK5 = k1_xboole_0 | k1_relat_1(sK7) = sK4 ),
% 3.89/1.03      inference(global_propositional_subsumption,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_6576,c_45]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_7110,plain,
% 3.89/1.03      ( k1_relat_1(sK7) = sK4 | sK5 = k1_xboole_0 ),
% 3.89/1.03      inference(renaming,[status(thm)],[c_7109]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_27,plain,
% 3.89/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.89/1.03      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 3.89/1.03      | ~ v1_funct_1(X1)
% 3.89/1.03      | ~ v1_relat_1(X1) ),
% 3.89/1.03      inference(cnf_transformation,[],[f115]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1210,plain,
% 3.89/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.89/1.03      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
% 3.89/1.03      | v1_funct_1(X1) != iProver_top
% 3.89/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_7114,plain,
% 3.89/1.03      ( sK5 = k1_xboole_0
% 3.89/1.03      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.89/1.03      | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top
% 3.89/1.03      | v1_funct_1(sK7) != iProver_top
% 3.89/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_7110,c_1210]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_43,negated_conjecture,
% 3.89/1.03      ( v1_funct_1(sK7) ),
% 3.89/1.03      inference(cnf_transformation,[],[f102]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_44,plain,
% 3.89/1.03      ( v1_funct_1(sK7) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_43]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_46,plain,
% 3.89/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_41]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_29,plain,
% 3.89/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.89/1.03      | v1_relat_1(X0) ),
% 3.89/1.03      inference(cnf_transformation,[],[f92]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1632,plain,
% 3.89/1.03      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
% 3.89/1.03      | v1_relat_1(sK7) ),
% 3.89/1.03      inference(instantiation,[status(thm)],[c_29]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1633,plain,
% 3.89/1.03      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) != iProver_top
% 3.89/1.03      | v1_relat_1(sK7) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_1632]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_9805,plain,
% 3.89/1.03      ( sK5 = k1_xboole_0
% 3.89/1.03      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.89/1.03      | r2_hidden(sK3(sK7,X1,X0),sK4) = iProver_top ),
% 3.89/1.03      inference(global_propositional_subsumption,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_7114,c_44,c_46,c_1633]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_7,plain,
% 3.89/1.03      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 3.89/1.03      inference(cnf_transformation,[],[f70]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1230,plain,
% 3.89/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.89/1.03      | m1_subset_1(X0,X1) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_7]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_9815,plain,
% 3.89/1.03      ( sK5 = k1_xboole_0
% 3.89/1.03      | r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 3.89/1.03      | m1_subset_1(sK3(sK7,X1,X0),sK4) = iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_9805,c_1230]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_26,plain,
% 3.89/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.89/1.03      | r2_hidden(sK3(X1,X2,X0),X2)
% 3.89/1.03      | ~ v1_funct_1(X1)
% 3.89/1.03      | ~ v1_relat_1(X1) ),
% 3.89/1.03      inference(cnf_transformation,[],[f114]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1211,plain,
% 3.89/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.89/1.03      | r2_hidden(sK3(X1,X2,X0),X2) = iProver_top
% 3.89/1.03      | v1_funct_1(X1) != iProver_top
% 3.89/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_32,plain,
% 3.89/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.89/1.03      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.89/1.03      inference(cnf_transformation,[],[f95]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1205,plain,
% 3.89/1.03      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.89/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_3322,plain,
% 3.89/1.03      ( k7_relset_1(sK4,sK5,sK7,X0) = k9_relat_1(sK7,X0) ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_1196,c_1205]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_40,negated_conjecture,
% 3.89/1.03      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) ),
% 3.89/1.03      inference(cnf_transformation,[],[f105]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1197,plain,
% 3.89/1.03      ( r2_hidden(sK8,k7_relset_1(sK4,sK5,sK7,sK6)) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_40]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_3743,plain,
% 3.89/1.03      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) = iProver_top ),
% 3.89/1.03      inference(demodulation,[status(thm)],[c_3322,c_1197]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_25,plain,
% 3.89/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.89/1.03      | ~ v1_funct_1(X1)
% 3.89/1.03      | ~ v1_relat_1(X1)
% 3.89/1.03      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
% 3.89/1.03      inference(cnf_transformation,[],[f113]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1212,plain,
% 3.89/1.03      ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
% 3.89/1.03      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 3.89/1.03      | v1_funct_1(X0) != iProver_top
% 3.89/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_4182,plain,
% 3.89/1.03      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8
% 3.89/1.03      | v1_funct_1(sK7) != iProver_top
% 3.89/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_3743,c_1212]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_4454,plain,
% 3.89/1.03      ( k1_funct_1(sK7,sK3(sK7,sK6,sK8)) = sK8 ),
% 3.89/1.03      inference(global_propositional_subsumption,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_4182,c_44,c_46,c_1633]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_39,negated_conjecture,
% 3.89/1.03      ( ~ r2_hidden(X0,sK6)
% 3.89/1.03      | ~ m1_subset_1(X0,sK4)
% 3.89/1.03      | k1_funct_1(sK7,X0) != sK8 ),
% 3.89/1.03      inference(cnf_transformation,[],[f106]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1198,plain,
% 3.89/1.03      ( k1_funct_1(sK7,X0) != sK8
% 3.89/1.03      | r2_hidden(X0,sK6) != iProver_top
% 3.89/1.03      | m1_subset_1(X0,sK4) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_4457,plain,
% 3.89/1.03      ( r2_hidden(sK3(sK7,sK6,sK8),sK6) != iProver_top
% 3.89/1.03      | m1_subset_1(sK3(sK7,sK6,sK8),sK4) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_4454,c_1198]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_4462,plain,
% 3.89/1.03      ( r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top
% 3.89/1.03      | m1_subset_1(sK3(sK7,sK6,sK8),sK4) != iProver_top
% 3.89/1.03      | v1_funct_1(sK7) != iProver_top
% 3.89/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_1211,c_4457]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_4561,plain,
% 3.89/1.03      ( m1_subset_1(sK3(sK7,sK6,sK8),sK4) != iProver_top ),
% 3.89/1.03      inference(global_propositional_subsumption,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_4462,c_44,c_46,c_1633,c_3743]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_10888,plain,
% 3.89/1.03      ( sK5 = k1_xboole_0
% 3.89/1.03      | r2_hidden(sK8,k9_relat_1(sK7,sK6)) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_9815,c_4561]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_11020,plain,
% 3.89/1.03      ( sK5 = k1_xboole_0 ),
% 3.89/1.03      inference(global_propositional_subsumption,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_10888,c_3743]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1,plain,
% 3.89/1.03      ( r1_tarski(X0,X0) ),
% 3.89/1.03      inference(cnf_transformation,[],[f107]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1232,plain,
% 3.89/1.03      ( r1_tarski(X0,X0) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_10,plain,
% 3.89/1.03      ( v5_relat_1(X0,X1)
% 3.89/1.03      | ~ r1_tarski(k2_relat_1(X0),X1)
% 3.89/1.03      | ~ v1_relat_1(X0) ),
% 3.89/1.03      inference(cnf_transformation,[],[f74]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1227,plain,
% 3.89/1.03      ( v5_relat_1(X0,X1) = iProver_top
% 3.89/1.03      | r1_tarski(k2_relat_1(X0),X1) != iProver_top
% 3.89/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_3537,plain,
% 3.89/1.03      ( v5_relat_1(X0,k2_relat_1(X0)) = iProver_top
% 3.89/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_1232,c_1227]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_9,plain,
% 3.89/1.03      ( ~ v5_relat_1(X0,X1)
% 3.89/1.03      | v5_relat_1(X2,X1)
% 3.89/1.03      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
% 3.89/1.03      | ~ v1_relat_1(X0) ),
% 3.89/1.03      inference(cnf_transformation,[],[f72]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1228,plain,
% 3.89/1.03      ( v5_relat_1(X0,X1) != iProver_top
% 3.89/1.03      | v5_relat_1(X2,X1) = iProver_top
% 3.89/1.03      | m1_subset_1(X2,k1_zfmisc_1(X0)) != iProver_top
% 3.89/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_6452,plain,
% 3.89/1.03      ( v5_relat_1(k2_zfmisc_1(sK4,sK5),X0) != iProver_top
% 3.89/1.03      | v5_relat_1(sK7,X0) = iProver_top
% 3.89/1.03      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_1196,c_1228]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_3580,plain,
% 3.89/1.03      ( ~ v5_relat_1(k2_zfmisc_1(sK4,sK5),X0)
% 3.89/1.03      | v5_relat_1(sK7,X0)
% 3.89/1.03      | ~ v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 3.89/1.03      inference(resolution,[status(thm)],[c_9,c_41]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_12,plain,
% 3.89/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.89/1.03      inference(cnf_transformation,[],[f75]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_3966,plain,
% 3.89/1.03      ( ~ v5_relat_1(k2_zfmisc_1(sK4,sK5),X0) | v5_relat_1(sK7,X0) ),
% 3.89/1.03      inference(forward_subsumption_resolution,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_3580,c_12]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_3967,plain,
% 3.89/1.03      ( v5_relat_1(k2_zfmisc_1(sK4,sK5),X0) != iProver_top
% 3.89/1.03      | v5_relat_1(sK7,X0) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_3966]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_6944,plain,
% 3.89/1.03      ( v5_relat_1(sK7,X0) = iProver_top
% 3.89/1.03      | v5_relat_1(k2_zfmisc_1(sK4,sK5),X0) != iProver_top ),
% 3.89/1.03      inference(global_propositional_subsumption,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_6452,c_3967]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_6945,plain,
% 3.89/1.03      ( v5_relat_1(k2_zfmisc_1(sK4,sK5),X0) != iProver_top
% 3.89/1.03      | v5_relat_1(sK7,X0) = iProver_top ),
% 3.89/1.03      inference(renaming,[status(thm)],[c_6944]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_6950,plain,
% 3.89/1.03      ( v5_relat_1(sK7,k2_relat_1(k2_zfmisc_1(sK4,sK5))) = iProver_top
% 3.89/1.03      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_3537,c_6945]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1225,plain,
% 3.89/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_7106,plain,
% 3.89/1.03      ( v5_relat_1(sK7,k2_relat_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.89/1.03      inference(forward_subsumption_resolution,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_6950,c_1225]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_15,plain,
% 3.89/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.89/1.03      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1)
% 3.89/1.03      | ~ v1_relat_1(X1) ),
% 3.89/1.03      inference(cnf_transformation,[],[f77]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1222,plain,
% 3.89/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.89/1.03      | r2_hidden(k4_tarski(sK0(X0,X2,X1),X0),X1) = iProver_top
% 3.89/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_18,plain,
% 3.89/1.03      ( r2_hidden(X0,k2_relat_1(X1))
% 3.89/1.03      | ~ r2_hidden(k4_tarski(X2,X0),X1)
% 3.89/1.03      | ~ v1_relat_1(X1) ),
% 3.89/1.03      inference(cnf_transformation,[],[f82]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1219,plain,
% 3.89/1.03      ( r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 3.89/1.03      | r2_hidden(k4_tarski(X2,X0),X1) != iProver_top
% 3.89/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_5371,plain,
% 3.89/1.03      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.89/1.03      | r2_hidden(X0,k2_relat_1(X1)) = iProver_top
% 3.89/1.03      | v1_relat_1(X1) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_1222,c_1219]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_8087,plain,
% 3.89/1.03      ( r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top
% 3.89/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_3743,c_5371]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_8457,plain,
% 3.89/1.03      ( r2_hidden(sK8,k2_relat_1(sK7)) = iProver_top ),
% 3.89/1.03      inference(global_propositional_subsumption,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_8087,c_46,c_1633]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_17,plain,
% 3.89/1.03      ( ~ v5_relat_1(X0,X1)
% 3.89/1.03      | r2_hidden(X2,X1)
% 3.89/1.03      | ~ r2_hidden(X2,k2_relat_1(X0))
% 3.89/1.03      | ~ v1_relat_1(X0) ),
% 3.89/1.03      inference(cnf_transformation,[],[f80]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1220,plain,
% 3.89/1.03      ( v5_relat_1(X0,X1) != iProver_top
% 3.89/1.03      | r2_hidden(X2,X1) = iProver_top
% 3.89/1.03      | r2_hidden(X2,k2_relat_1(X0)) != iProver_top
% 3.89/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_8464,plain,
% 3.89/1.03      ( v5_relat_1(sK7,X0) != iProver_top
% 3.89/1.03      | r2_hidden(sK8,X0) = iProver_top
% 3.89/1.03      | v1_relat_1(sK7) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_8457,c_1220]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_8615,plain,
% 3.89/1.03      ( r2_hidden(sK8,X0) = iProver_top
% 3.89/1.03      | v5_relat_1(sK7,X0) != iProver_top ),
% 3.89/1.03      inference(global_propositional_subsumption,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_8464,c_46,c_1633]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_8616,plain,
% 3.89/1.03      ( v5_relat_1(sK7,X0) != iProver_top
% 3.89/1.03      | r2_hidden(sK8,X0) = iProver_top ),
% 3.89/1.03      inference(renaming,[status(thm)],[c_8615]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_8625,plain,
% 3.89/1.03      ( r2_hidden(sK8,k2_relat_1(k2_zfmisc_1(sK4,sK5))) = iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_7106,c_8616]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_28,plain,
% 3.89/1.03      ( ~ r2_hidden(X0,X1) | ~ r1_tarski(X1,X0) ),
% 3.89/1.03      inference(cnf_transformation,[],[f91]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1209,plain,
% 3.89/1.03      ( r2_hidden(X0,X1) != iProver_top
% 3.89/1.03      | r1_tarski(X1,X0) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_10138,plain,
% 3.89/1.03      ( r1_tarski(k2_relat_1(k2_zfmisc_1(sK4,sK5)),sK8) != iProver_top ),
% 3.89/1.03      inference(superposition,[status(thm)],[c_8625,c_1209]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_11024,plain,
% 3.89/1.03      ( r1_tarski(k2_relat_1(k2_zfmisc_1(sK4,k1_xboole_0)),sK8) != iProver_top ),
% 3.89/1.03      inference(demodulation,[status(thm)],[c_11020,c_10138]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_3,plain,
% 3.89/1.03      ( k2_zfmisc_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 3.89/1.03      inference(cnf_transformation,[],[f109]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_11076,plain,
% 3.89/1.03      ( r1_tarski(k2_relat_1(k1_xboole_0),sK8) != iProver_top ),
% 3.89/1.03      inference(demodulation,[status(thm)],[c_11024,c_3]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_6,plain,
% 3.89/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
% 3.89/1.03      inference(cnf_transformation,[],[f69]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1625,plain,
% 3.89/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ),
% 3.89/1.03      inference(instantiation,[status(thm)],[c_6]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_9763,plain,
% 3.89/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) ),
% 3.89/1.03      inference(instantiation,[status(thm)],[c_1625]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_9766,plain,
% 3.89/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_9763]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_30,plain,
% 3.89/1.03      ( v5_relat_1(X0,X1)
% 3.89/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 3.89/1.03      inference(cnf_transformation,[],[f93]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_4255,plain,
% 3.89/1.03      ( v5_relat_1(X0,sK8)
% 3.89/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK8))) ),
% 3.89/1.03      inference(instantiation,[status(thm)],[c_30]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_9762,plain,
% 3.89/1.03      ( v5_relat_1(k1_xboole_0,sK8)
% 3.89/1.03      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) ),
% 3.89/1.03      inference(instantiation,[status(thm)],[c_4255]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_9764,plain,
% 3.89/1.03      ( v5_relat_1(k1_xboole_0,sK8) = iProver_top
% 3.89/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,sK8))) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_9762]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_11,plain,
% 3.89/1.03      ( ~ v5_relat_1(X0,X1)
% 3.89/1.03      | r1_tarski(k2_relat_1(X0),X1)
% 3.89/1.03      | ~ v1_relat_1(X0) ),
% 3.89/1.03      inference(cnf_transformation,[],[f73]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2479,plain,
% 3.89/1.03      ( ~ v5_relat_1(X0,sK8)
% 3.89/1.03      | r1_tarski(k2_relat_1(X0),sK8)
% 3.89/1.03      | ~ v1_relat_1(X0) ),
% 3.89/1.03      inference(instantiation,[status(thm)],[c_11]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2481,plain,
% 3.89/1.03      ( v5_relat_1(X0,sK8) != iProver_top
% 3.89/1.03      | r1_tarski(k2_relat_1(X0),sK8) = iProver_top
% 3.89/1.03      | v1_relat_1(X0) != iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_2479]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_2483,plain,
% 3.89/1.03      ( v5_relat_1(k1_xboole_0,sK8) != iProver_top
% 3.89/1.03      | r1_tarski(k2_relat_1(k1_xboole_0),sK8) = iProver_top
% 3.89/1.03      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.89/1.03      inference(instantiation,[status(thm)],[c_2481]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1628,plain,
% 3.89/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_1625]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1624,plain,
% 3.89/1.03      ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.89/1.03      | v1_relat_1(k1_xboole_0) ),
% 3.89/1.03      inference(instantiation,[status(thm)],[c_29]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_1626,plain,
% 3.89/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 3.89/1.03      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.89/1.03      inference(predicate_to_equality,[status(thm)],[c_1624]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_11096,plain,
% 3.89/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK8))) = iProver_top ),
% 3.89/1.03      inference(grounding,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_9766:[bind(X0,$fot(k1_xboole_0))]]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_11097,plain,
% 3.89/1.03      ( v5_relat_1(k1_xboole_0,sK8) = iProver_top
% 3.89/1.03      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK8))) != iProver_top ),
% 3.89/1.03      inference(grounding,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_9764:[bind(X0,$fot(k1_xboole_0))]]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_11098,plain,
% 3.89/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.89/1.03      inference(grounding,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_1628:[bind(X1,$fot(k1_xboole_0)),
% 3.89/1.03                 bind(X0,$fot(k1_xboole_0))]]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(c_11099,plain,
% 3.89/1.03      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.89/1.03      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.89/1.03      inference(grounding,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_1626:[bind(X1,$fot(k1_xboole_0)),
% 3.89/1.03                 bind(X0,$fot(k1_xboole_0))]]) ).
% 3.89/1.03  
% 3.89/1.03  cnf(contradiction,plain,
% 3.89/1.03      ( $false ),
% 3.89/1.03      inference(minisat,
% 3.89/1.03                [status(thm)],
% 3.89/1.03                [c_11076,c_11096,c_11097,c_2483,c_11098,c_11099]) ).
% 3.89/1.03  
% 3.89/1.03  
% 3.89/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.89/1.03  
% 3.89/1.03  ------                               Statistics
% 3.89/1.03  
% 3.89/1.03  ------ Selected
% 3.89/1.03  
% 3.89/1.03  total_time:                             0.288
% 3.89/1.03  
%------------------------------------------------------------------------------
