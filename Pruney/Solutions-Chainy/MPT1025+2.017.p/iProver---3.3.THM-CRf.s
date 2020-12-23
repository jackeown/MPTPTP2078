%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:03 EST 2020

% Result     : Theorem 4.08s
% Output     : CNFRefutation 4.08s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 657 expanded)
%              Number of clauses        :   64 ( 199 expanded)
%              Number of leaves         :   16 ( 164 expanded)
%              Depth                    :   22
%              Number of atoms          :  457 (3634 expanded)
%              Number of equality atoms :  194 ( 940 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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

fof(f25,plain,(
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

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f26])).

fof(f47,plain,(
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
    inference(rectify,[],[f46])).

fof(f50,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f49,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
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

fof(f51,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f47,f50,f49,f48])).

fof(f71,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f105,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f71])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

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

fof(f40,plain,(
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

fof(f41,plain,(
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
    inference(flattening,[],[f40])).

fof(f60,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ m1_subset_1(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK11
            | ~ r2_hidden(X5,X2)
            | ~ m1_subset_1(X5,X0) )
        & r2_hidden(sK11,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f59,plain,
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
              ( k1_funct_1(sK10,X5) != X4
              | ~ r2_hidden(X5,sK9)
              | ~ m1_subset_1(X5,sK7) )
          & r2_hidden(X4,k7_relset_1(sK7,sK8,sK10,sK9)) )
      & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
      & v1_funct_2(sK10,sK7,sK8)
      & v1_funct_1(sK10) ) ),
    introduced(choice_axiom,[])).

fof(f61,plain,
    ( ! [X5] :
        ( k1_funct_1(sK10,X5) != sK11
        | ~ r2_hidden(X5,sK9)
        | ~ m1_subset_1(X5,sK7) )
    & r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9))
    & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    & v1_funct_2(sK10,sK7,sK8)
    & v1_funct_1(sK10) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f41,f60,f59])).

fof(f99,plain,(
    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f61])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f38,plain,(
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

fof(f39,plain,(
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
    inference(flattening,[],[f38])).

fof(f58,plain,(
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
    inference(nnf_transformation,[],[f39])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f98,plain,(
    v1_funct_2(sK10,sK7,sK8) ),
    inference(cnf_transformation,[],[f61])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f70,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f106,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f70])).

fof(f97,plain,(
    v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f61])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f64,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f90,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f100,plain,(
    r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9)) ),
    inference(cnf_transformation,[],[f61])).

fof(f72,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f104,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f72])).

fof(f101,plain,(
    ! [X5] :
      ( k1_funct_1(sK10,X5) != sK11
      | ~ r2_hidden(X5,sK9)
      | ~ m1_subset_1(X5,sK7) ) ),
    inference(cnf_transformation,[],[f61])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f12])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ! [X2] :
          ( r2_hidden(X2,k1_relat_1(X1))
         => r2_hidden(k1_funct_1(X1,X2),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(k1_funct_1(X1,X2),X0)
          | ~ r2_hidden(X2,k1_relat_1(X1)) )
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f29])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_funct_1(X1,X2),X0)
      | ~ r2_hidden(X2,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f63,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f105])).

cnf(c_1019,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_37,negated_conjecture,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
    inference(cnf_transformation,[],[f99])).

cnf(c_996,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f91])).

cnf(c_999,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_34])).

cnf(c_1555,plain,
    ( k1_relset_1(sK7,sK8,sK10) = sK7
    | sK8 = k1_xboole_0
    | v1_funct_2(sK10,sK7,sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_996,c_999])).

cnf(c_38,negated_conjecture,
    ( v1_funct_2(sK10,sK7,sK8) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_1556,plain,
    ( ~ v1_funct_2(sK10,sK7,sK8)
    | k1_relset_1(sK7,sK8,sK10) = sK7
    | sK8 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1555])).

cnf(c_2146,plain,
    ( sK8 = k1_xboole_0
    | k1_relset_1(sK7,sK8,sK10) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1555,c_38,c_1556])).

cnf(c_2147,plain,
    ( k1_relset_1(sK7,sK8,sK10) = sK7
    | sK8 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_2146])).

cnf(c_27,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f89])).

cnf(c_1006,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_2229,plain,
    ( k1_relset_1(sK7,sK8,sK10) = k1_relat_1(sK10) ),
    inference(superposition,[status(thm)],[c_996,c_1006])).

cnf(c_2231,plain,
    ( k1_relat_1(sK10) = sK7
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_2147,c_2229])).

cnf(c_15,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f106])).

cnf(c_1018,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_6048,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
    | r2_hidden(sK3(sK10,X1,X0),sK7) = iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_2231,c_1018])).

cnf(c_39,negated_conjecture,
    ( v1_funct_1(sK10) ),
    inference(cnf_transformation,[],[f97])).

cnf(c_40,plain,
    ( v1_funct_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_39])).

cnf(c_42,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1429,plain,
    ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
    | v1_relat_1(sK10) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_1430,plain,
    ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
    | v1_relat_1(sK10) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1429])).

cnf(c_9283,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
    | r2_hidden(sK3(sK10,X1,X0),sK7) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6048,c_40,c_42,c_1430])).

cnf(c_2,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f64])).

cnf(c_1031,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_9293,plain,
    ( sK8 = k1_xboole_0
    | m1_subset_1(sK3(sK10,X0,X1),sK7) = iProver_top
    | r2_hidden(X1,k9_relat_1(sK10,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9283,c_1031])).

cnf(c_28,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f90])).

cnf(c_1005,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_2520,plain,
    ( k7_relset_1(sK7,sK8,sK10,X0) = k9_relat_1(sK10,X0) ),
    inference(superposition,[status(thm)],[c_996,c_1005])).

cnf(c_36,negated_conjecture,
    ( r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9)) ),
    inference(cnf_transformation,[],[f100])).

cnf(c_997,plain,
    ( r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_36])).

cnf(c_2868,plain,
    ( r2_hidden(sK11,k9_relat_1(sK10,sK9)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2520,c_997])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_1020,plain,
    ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_5805,plain,
    ( k1_funct_1(sK10,sK3(sK10,sK9,sK11)) = sK11
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_2868,c_1020])).

cnf(c_6643,plain,
    ( k1_funct_1(sK10,sK3(sK10,sK9,sK11)) = sK11 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5805,c_40,c_42,c_1430])).

cnf(c_35,negated_conjecture,
    ( ~ m1_subset_1(X0,sK7)
    | ~ r2_hidden(X0,sK9)
    | k1_funct_1(sK10,X0) != sK11 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_998,plain,
    ( k1_funct_1(sK10,X0) != sK11
    | m1_subset_1(X0,sK7) != iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_35])).

cnf(c_6649,plain,
    ( m1_subset_1(sK3(sK10,sK9,sK11),sK7) != iProver_top
    | r2_hidden(sK3(sK10,sK9,sK11),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_6643,c_998])).

cnf(c_11517,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(sK3(sK10,sK9,sK11),sK9) != iProver_top
    | r2_hidden(sK11,k9_relat_1(sK10,sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_9293,c_6649])).

cnf(c_11526,plain,
    ( r2_hidden(sK3(sK10,sK9,sK11),sK9) != iProver_top
    | sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11517,c_2868])).

cnf(c_11527,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(sK3(sK10,sK9,sK11),sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_11526])).

cnf(c_11532,plain,
    ( sK8 = k1_xboole_0
    | r2_hidden(sK11,k9_relat_1(sK10,sK9)) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_1019,c_11527])).

cnf(c_11647,plain,
    ( sK8 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_11532,c_40,c_42,c_1430,c_2868])).

cnf(c_26,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f88])).

cnf(c_1007,plain,
    ( v5_relat_1(X0,X1) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1729,plain,
    ( v5_relat_1(sK10,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_996,c_1007])).

cnf(c_22,plain,
    ( ~ v5_relat_1(X0,X1)
    | ~ r2_hidden(X2,k1_relat_1(X0))
    | r2_hidden(k1_funct_1(X0,X2),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1011,plain,
    ( v5_relat_1(X0,X1) != iProver_top
    | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
    | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6647,plain,
    ( v5_relat_1(sK10,X0) != iProver_top
    | r2_hidden(sK3(sK10,sK9,sK11),k1_relat_1(sK10)) != iProver_top
    | r2_hidden(sK11,X0) = iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_6643,c_1011])).

cnf(c_7009,plain,
    ( v5_relat_1(sK10,X0) != iProver_top
    | r2_hidden(sK3(sK10,sK9,sK11),k1_relat_1(sK10)) != iProver_top
    | r2_hidden(sK11,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_6647,c_40,c_42,c_1430])).

cnf(c_7019,plain,
    ( sK8 = k1_xboole_0
    | v5_relat_1(sK10,X0) != iProver_top
    | r2_hidden(sK3(sK10,sK9,sK11),sK7) != iProver_top
    | r2_hidden(sK11,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_2231,c_7009])).

cnf(c_7018,plain,
    ( v5_relat_1(sK10,X0) != iProver_top
    | r2_hidden(sK11,X0) = iProver_top
    | r2_hidden(sK11,k9_relat_1(sK10,sK9)) != iProver_top
    | v1_funct_1(sK10) != iProver_top
    | v1_relat_1(sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_1018,c_7009])).

cnf(c_7199,plain,
    ( v5_relat_1(sK10,X0) != iProver_top
    | r2_hidden(sK11,X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_7019,c_40,c_42,c_1430,c_2868,c_7018])).

cnf(c_7207,plain,
    ( r2_hidden(sK11,sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1729,c_7199])).

cnf(c_11654,plain,
    ( r2_hidden(sK11,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_11647,c_7207])).

cnf(c_1,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_1032,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_24,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X1,X0) ),
    inference(cnf_transformation,[],[f86])).

cnf(c_1009,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X1,X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1635,plain,
    ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1032,c_1009])).

cnf(c_13407,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_11654,c_1635])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:50:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  % Running in FOF mode
% 4.08/1.00  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.08/1.00  
% 4.08/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 4.08/1.00  
% 4.08/1.00  ------  iProver source info
% 4.08/1.00  
% 4.08/1.00  git: date: 2020-06-30 10:37:57 +0100
% 4.08/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 4.08/1.00  git: non_committed_changes: false
% 4.08/1.00  git: last_make_outside_of_git: false
% 4.08/1.00  
% 4.08/1.00  ------ 
% 4.08/1.00  ------ Parsing...
% 4.08/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 4.08/1.00  
% 4.08/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 4.08/1.00  
% 4.08/1.00  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 4.08/1.00  
% 4.08/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 4.08/1.00  ------ Proving...
% 4.08/1.00  ------ Problem Properties 
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  clauses                                 40
% 4.08/1.00  conjectures                             5
% 4.08/1.00  EPR                                     7
% 4.08/1.00  Horn                                    30
% 4.08/1.00  unary                                   5
% 4.08/1.00  binary                                  7
% 4.08/1.00  lits                                    137
% 4.08/1.00  lits eq                                 25
% 4.08/1.00  fd_pure                                 0
% 4.08/1.00  fd_pseudo                               0
% 4.08/1.00  fd_cond                                 3
% 4.08/1.00  fd_pseudo_cond                          7
% 4.08/1.00  AC symbols                              0
% 4.08/1.00  
% 4.08/1.00  ------ Input Options Time Limit: Unbounded
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  ------ 
% 4.08/1.00  Current options:
% 4.08/1.00  ------ 
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  ------ Proving...
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  % SZS status Theorem for theBenchmark.p
% 4.08/1.00  
% 4.08/1.00   Resolution empty clause
% 4.08/1.00  
% 4.08/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 4.08/1.00  
% 4.08/1.00  fof(f6,axiom,(
% 4.08/1.00    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 4.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f25,plain,(
% 4.08/1.00    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 4.08/1.00    inference(ennf_transformation,[],[f6])).
% 4.08/1.00  
% 4.08/1.00  fof(f26,plain,(
% 4.08/1.00    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.08/1.00    inference(flattening,[],[f25])).
% 4.08/1.00  
% 4.08/1.00  fof(f46,plain,(
% 4.08/1.00    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.08/1.00    inference(nnf_transformation,[],[f26])).
% 4.08/1.00  
% 4.08/1.00  fof(f47,plain,(
% 4.08/1.00    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.08/1.00    inference(rectify,[],[f46])).
% 4.08/1.00  
% 4.08/1.00  fof(f50,plain,(
% 4.08/1.00    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 4.08/1.00    introduced(choice_axiom,[])).
% 4.08/1.00  
% 4.08/1.00  fof(f49,plain,(
% 4.08/1.00    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 4.08/1.00    introduced(choice_axiom,[])).
% 4.08/1.00  
% 4.08/1.00  fof(f48,plain,(
% 4.08/1.00    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 4.08/1.00    introduced(choice_axiom,[])).
% 4.08/1.00  
% 4.08/1.00  fof(f51,plain,(
% 4.08/1.00    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 4.08/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f47,f50,f49,f48])).
% 4.08/1.00  
% 4.08/1.00  fof(f71,plain,(
% 4.08/1.00    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f51])).
% 4.08/1.00  
% 4.08/1.00  fof(f105,plain,(
% 4.08/1.00    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.08/1.00    inference(equality_resolution,[],[f71])).
% 4.08/1.00  
% 4.08/1.00  fof(f16,conjecture,(
% 4.08/1.00    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 4.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f17,negated_conjecture,(
% 4.08/1.00    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : (m1_subset_1(X5,X0) => ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2))) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 4.08/1.00    inference(negated_conjecture,[],[f16])).
% 4.08/1.00  
% 4.08/1.00  fof(f40,plain,(
% 4.08/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : ((k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2)) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 4.08/1.00    inference(ennf_transformation,[],[f17])).
% 4.08/1.00  
% 4.08/1.00  fof(f41,plain,(
% 4.08/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 4.08/1.00    inference(flattening,[],[f40])).
% 4.08/1.00  
% 4.08/1.00  fof(f60,plain,(
% 4.08/1.00    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK11 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(sK11,k7_relset_1(X0,X1,X3,X2)))) )),
% 4.08/1.00    introduced(choice_axiom,[])).
% 4.08/1.00  
% 4.08/1.00  fof(f59,plain,(
% 4.08/1.00    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~m1_subset_1(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK10,X5) != X4 | ~r2_hidden(X5,sK9) | ~m1_subset_1(X5,sK7)) & r2_hidden(X4,k7_relset_1(sK7,sK8,sK10,sK9))) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK10,sK7,sK8) & v1_funct_1(sK10))),
% 4.08/1.00    introduced(choice_axiom,[])).
% 4.08/1.00  
% 4.08/1.00  fof(f61,plain,(
% 4.08/1.00    (! [X5] : (k1_funct_1(sK10,X5) != sK11 | ~r2_hidden(X5,sK9) | ~m1_subset_1(X5,sK7)) & r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9))) & m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) & v1_funct_2(sK10,sK7,sK8) & v1_funct_1(sK10)),
% 4.08/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7,sK8,sK9,sK10,sK11])],[f41,f60,f59])).
% 4.08/1.00  
% 4.08/1.00  fof(f99,plain,(
% 4.08/1.00    m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))),
% 4.08/1.00    inference(cnf_transformation,[],[f61])).
% 4.08/1.00  
% 4.08/1.00  fof(f15,axiom,(
% 4.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 4.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f38,plain,(
% 4.08/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(ennf_transformation,[],[f15])).
% 4.08/1.00  
% 4.08/1.00  fof(f39,plain,(
% 4.08/1.00    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(flattening,[],[f38])).
% 4.08/1.00  
% 4.08/1.00  fof(f58,plain,(
% 4.08/1.00    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(nnf_transformation,[],[f39])).
% 4.08/1.00  
% 4.08/1.00  fof(f91,plain,(
% 4.08/1.00    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f58])).
% 4.08/1.00  
% 4.08/1.00  fof(f98,plain,(
% 4.08/1.00    v1_funct_2(sK10,sK7,sK8)),
% 4.08/1.00    inference(cnf_transformation,[],[f61])).
% 4.08/1.00  
% 4.08/1.00  fof(f13,axiom,(
% 4.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 4.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f36,plain,(
% 4.08/1.00    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(ennf_transformation,[],[f13])).
% 4.08/1.00  
% 4.08/1.00  fof(f89,plain,(
% 4.08/1.00    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f36])).
% 4.08/1.00  
% 4.08/1.00  fof(f70,plain,(
% 4.08/1.00    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f51])).
% 4.08/1.00  
% 4.08/1.00  fof(f106,plain,(
% 4.08/1.00    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.08/1.00    inference(equality_resolution,[],[f70])).
% 4.08/1.00  
% 4.08/1.00  fof(f97,plain,(
% 4.08/1.00    v1_funct_1(sK10)),
% 4.08/1.00    inference(cnf_transformation,[],[f61])).
% 4.08/1.00  
% 4.08/1.00  fof(f11,axiom,(
% 4.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 4.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f34,plain,(
% 4.08/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(ennf_transformation,[],[f11])).
% 4.08/1.00  
% 4.08/1.00  fof(f87,plain,(
% 4.08/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f34])).
% 4.08/1.00  
% 4.08/1.00  fof(f3,axiom,(
% 4.08/1.00    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 4.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f21,plain,(
% 4.08/1.00    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 4.08/1.00    inference(ennf_transformation,[],[f3])).
% 4.08/1.00  
% 4.08/1.00  fof(f64,plain,(
% 4.08/1.00    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f21])).
% 4.08/1.00  
% 4.08/1.00  fof(f14,axiom,(
% 4.08/1.00    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 4.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f37,plain,(
% 4.08/1.00    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(ennf_transformation,[],[f14])).
% 4.08/1.00  
% 4.08/1.00  fof(f90,plain,(
% 4.08/1.00    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f37])).
% 4.08/1.00  
% 4.08/1.00  fof(f100,plain,(
% 4.08/1.00    r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9))),
% 4.08/1.00    inference(cnf_transformation,[],[f61])).
% 4.08/1.00  
% 4.08/1.00  fof(f72,plain,(
% 4.08/1.00    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f51])).
% 4.08/1.00  
% 4.08/1.00  fof(f104,plain,(
% 4.08/1.00    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 4.08/1.00    inference(equality_resolution,[],[f72])).
% 4.08/1.00  
% 4.08/1.00  fof(f101,plain,(
% 4.08/1.00    ( ! [X5] : (k1_funct_1(sK10,X5) != sK11 | ~r2_hidden(X5,sK9) | ~m1_subset_1(X5,sK7)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f61])).
% 4.08/1.00  
% 4.08/1.00  fof(f12,axiom,(
% 4.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 4.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f19,plain,(
% 4.08/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 4.08/1.00    inference(pure_predicate_removal,[],[f12])).
% 4.08/1.00  
% 4.08/1.00  fof(f35,plain,(
% 4.08/1.00    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 4.08/1.00    inference(ennf_transformation,[],[f19])).
% 4.08/1.00  
% 4.08/1.00  fof(f88,plain,(
% 4.08/1.00    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 4.08/1.00    inference(cnf_transformation,[],[f35])).
% 4.08/1.00  
% 4.08/1.00  fof(f8,axiom,(
% 4.08/1.00    ! [X0,X1] : ((v1_funct_1(X1) & v5_relat_1(X1,X0) & v1_relat_1(X1)) => ! [X2] : (r2_hidden(X2,k1_relat_1(X1)) => r2_hidden(k1_funct_1(X1,X2),X0)))),
% 4.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f29,plain,(
% 4.08/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | (~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 4.08/1.00    inference(ennf_transformation,[],[f8])).
% 4.08/1.00  
% 4.08/1.00  fof(f30,plain,(
% 4.08/1.00    ! [X0,X1] : (! [X2] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1))) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 4.08/1.00    inference(flattening,[],[f29])).
% 4.08/1.00  
% 4.08/1.00  fof(f84,plain,(
% 4.08/1.00    ( ! [X2,X0,X1] : (r2_hidden(k1_funct_1(X1,X2),X0) | ~r2_hidden(X2,k1_relat_1(X1)) | ~v1_funct_1(X1) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f30])).
% 4.08/1.00  
% 4.08/1.00  fof(f2,axiom,(
% 4.08/1.00    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 4.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f63,plain,(
% 4.08/1.00    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f2])).
% 4.08/1.00  
% 4.08/1.00  fof(f10,axiom,(
% 4.08/1.00    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 4.08/1.00    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 4.08/1.00  
% 4.08/1.00  fof(f33,plain,(
% 4.08/1.00    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 4.08/1.00    inference(ennf_transformation,[],[f10])).
% 4.08/1.00  
% 4.08/1.00  fof(f86,plain,(
% 4.08/1.00    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 4.08/1.00    inference(cnf_transformation,[],[f33])).
% 4.08/1.00  
% 4.08/1.00  cnf(c_14,plain,
% 4.08/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 4.08/1.00      | r2_hidden(sK3(X1,X2,X0),X2)
% 4.08/1.00      | ~ v1_funct_1(X1)
% 4.08/1.00      | ~ v1_relat_1(X1) ),
% 4.08/1.00      inference(cnf_transformation,[],[f105]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1019,plain,
% 4.08/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 4.08/1.00      | r2_hidden(sK3(X1,X2,X0),X2) = iProver_top
% 4.08/1.00      | v1_funct_1(X1) != iProver_top
% 4.08/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_37,negated_conjecture,
% 4.08/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) ),
% 4.08/1.00      inference(cnf_transformation,[],[f99]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_996,plain,
% 4.08/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_34,plain,
% 4.08/1.00      ( ~ v1_funct_2(X0,X1,X2)
% 4.08/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.00      | k1_relset_1(X1,X2,X0) = X1
% 4.08/1.00      | k1_xboole_0 = X2 ),
% 4.08/1.00      inference(cnf_transformation,[],[f91]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_999,plain,
% 4.08/1.00      ( k1_relset_1(X0,X1,X2) = X0
% 4.08/1.00      | k1_xboole_0 = X1
% 4.08/1.00      | v1_funct_2(X2,X0,X1) != iProver_top
% 4.08/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_34]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1555,plain,
% 4.08/1.00      ( k1_relset_1(sK7,sK8,sK10) = sK7
% 4.08/1.00      | sK8 = k1_xboole_0
% 4.08/1.00      | v1_funct_2(sK10,sK7,sK8) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_996,c_999]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_38,negated_conjecture,
% 4.08/1.00      ( v1_funct_2(sK10,sK7,sK8) ),
% 4.08/1.00      inference(cnf_transformation,[],[f98]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1556,plain,
% 4.08/1.00      ( ~ v1_funct_2(sK10,sK7,sK8)
% 4.08/1.00      | k1_relset_1(sK7,sK8,sK10) = sK7
% 4.08/1.00      | sK8 = k1_xboole_0 ),
% 4.08/1.00      inference(predicate_to_equality_rev,[status(thm)],[c_1555]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2146,plain,
% 4.08/1.00      ( sK8 = k1_xboole_0 | k1_relset_1(sK7,sK8,sK10) = sK7 ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_1555,c_38,c_1556]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2147,plain,
% 4.08/1.00      ( k1_relset_1(sK7,sK8,sK10) = sK7 | sK8 = k1_xboole_0 ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_2146]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_27,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.00      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f89]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1006,plain,
% 4.08/1.00      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 4.08/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2229,plain,
% 4.08/1.00      ( k1_relset_1(sK7,sK8,sK10) = k1_relat_1(sK10) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_996,c_1006]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2231,plain,
% 4.08/1.00      ( k1_relat_1(sK10) = sK7 | sK8 = k1_xboole_0 ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_2147,c_2229]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_15,plain,
% 4.08/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 4.08/1.00      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1))
% 4.08/1.00      | ~ v1_funct_1(X1)
% 4.08/1.00      | ~ v1_relat_1(X1) ),
% 4.08/1.00      inference(cnf_transformation,[],[f106]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1018,plain,
% 4.08/1.00      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 4.08/1.00      | r2_hidden(sK3(X1,X2,X0),k1_relat_1(X1)) = iProver_top
% 4.08/1.00      | v1_funct_1(X1) != iProver_top
% 4.08/1.00      | v1_relat_1(X1) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6048,plain,
% 4.08/1.00      ( sK8 = k1_xboole_0
% 4.08/1.00      | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
% 4.08/1.00      | r2_hidden(sK3(sK10,X1,X0),sK7) = iProver_top
% 4.08/1.00      | v1_funct_1(sK10) != iProver_top
% 4.08/1.00      | v1_relat_1(sK10) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_2231,c_1018]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_39,negated_conjecture,
% 4.08/1.00      ( v1_funct_1(sK10) ),
% 4.08/1.00      inference(cnf_transformation,[],[f97]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_40,plain,
% 4.08/1.00      ( v1_funct_1(sK10) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_39]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_42,plain,
% 4.08/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_25,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f87]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1429,plain,
% 4.08/1.00      ( ~ m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8)))
% 4.08/1.00      | v1_relat_1(sK10) ),
% 4.08/1.00      inference(instantiation,[status(thm)],[c_25]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1430,plain,
% 4.08/1.00      ( m1_subset_1(sK10,k1_zfmisc_1(k2_zfmisc_1(sK7,sK8))) != iProver_top
% 4.08/1.00      | v1_relat_1(sK10) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1429]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9283,plain,
% 4.08/1.00      ( sK8 = k1_xboole_0
% 4.08/1.00      | r2_hidden(X0,k9_relat_1(sK10,X1)) != iProver_top
% 4.08/1.00      | r2_hidden(sK3(sK10,X1,X0),sK7) = iProver_top ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_6048,c_40,c_42,c_1430]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2,plain,
% 4.08/1.00      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 4.08/1.00      inference(cnf_transformation,[],[f64]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1031,plain,
% 4.08/1.00      ( m1_subset_1(X0,X1) = iProver_top | r2_hidden(X0,X1) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_9293,plain,
% 4.08/1.00      ( sK8 = k1_xboole_0
% 4.08/1.00      | m1_subset_1(sK3(sK10,X0,X1),sK7) = iProver_top
% 4.08/1.00      | r2_hidden(X1,k9_relat_1(sK10,X0)) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_9283,c_1031]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_28,plain,
% 4.08/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 4.08/1.00      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 4.08/1.00      inference(cnf_transformation,[],[f90]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1005,plain,
% 4.08/1.00      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 4.08/1.00      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2520,plain,
% 4.08/1.00      ( k7_relset_1(sK7,sK8,sK10,X0) = k9_relat_1(sK10,X0) ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_996,c_1005]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_36,negated_conjecture,
% 4.08/1.00      ( r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9)) ),
% 4.08/1.00      inference(cnf_transformation,[],[f100]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_997,plain,
% 4.08/1.00      ( r2_hidden(sK11,k7_relset_1(sK7,sK8,sK10,sK9)) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_36]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_2868,plain,
% 4.08/1.00      ( r2_hidden(sK11,k9_relat_1(sK10,sK9)) = iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_2520,c_997]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13,plain,
% 4.08/1.00      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 4.08/1.00      | ~ v1_funct_1(X1)
% 4.08/1.00      | ~ v1_relat_1(X1)
% 4.08/1.00      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
% 4.08/1.00      inference(cnf_transformation,[],[f104]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1020,plain,
% 4.08/1.00      ( k1_funct_1(X0,sK3(X0,X1,X2)) = X2
% 4.08/1.00      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 4.08/1.00      | v1_funct_1(X0) != iProver_top
% 4.08/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_5805,plain,
% 4.08/1.00      ( k1_funct_1(sK10,sK3(sK10,sK9,sK11)) = sK11
% 4.08/1.00      | v1_funct_1(sK10) != iProver_top
% 4.08/1.00      | v1_relat_1(sK10) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_2868,c_1020]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6643,plain,
% 4.08/1.00      ( k1_funct_1(sK10,sK3(sK10,sK9,sK11)) = sK11 ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_5805,c_40,c_42,c_1430]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_35,negated_conjecture,
% 4.08/1.00      ( ~ m1_subset_1(X0,sK7)
% 4.08/1.00      | ~ r2_hidden(X0,sK9)
% 4.08/1.00      | k1_funct_1(sK10,X0) != sK11 ),
% 4.08/1.00      inference(cnf_transformation,[],[f101]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_998,plain,
% 4.08/1.00      ( k1_funct_1(sK10,X0) != sK11
% 4.08/1.00      | m1_subset_1(X0,sK7) != iProver_top
% 4.08/1.00      | r2_hidden(X0,sK9) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_35]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6649,plain,
% 4.08/1.00      ( m1_subset_1(sK3(sK10,sK9,sK11),sK7) != iProver_top
% 4.08/1.00      | r2_hidden(sK3(sK10,sK9,sK11),sK9) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_6643,c_998]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11517,plain,
% 4.08/1.00      ( sK8 = k1_xboole_0
% 4.08/1.00      | r2_hidden(sK3(sK10,sK9,sK11),sK9) != iProver_top
% 4.08/1.00      | r2_hidden(sK11,k9_relat_1(sK10,sK9)) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_9293,c_6649]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11526,plain,
% 4.08/1.00      ( r2_hidden(sK3(sK10,sK9,sK11),sK9) != iProver_top | sK8 = k1_xboole_0 ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_11517,c_2868]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11527,plain,
% 4.08/1.00      ( sK8 = k1_xboole_0 | r2_hidden(sK3(sK10,sK9,sK11),sK9) != iProver_top ),
% 4.08/1.00      inference(renaming,[status(thm)],[c_11526]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11532,plain,
% 4.08/1.00      ( sK8 = k1_xboole_0
% 4.08/1.00      | r2_hidden(sK11,k9_relat_1(sK10,sK9)) != iProver_top
% 4.08/1.00      | v1_funct_1(sK10) != iProver_top
% 4.08/1.00      | v1_relat_1(sK10) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_1019,c_11527]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11647,plain,
% 4.08/1.00      ( sK8 = k1_xboole_0 ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_11532,c_40,c_42,c_1430,c_2868]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_26,plain,
% 4.08/1.00      ( v5_relat_1(X0,X1) | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 4.08/1.00      inference(cnf_transformation,[],[f88]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1007,plain,
% 4.08/1.00      ( v5_relat_1(X0,X1) = iProver_top
% 4.08/1.00      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1729,plain,
% 4.08/1.00      ( v5_relat_1(sK10,sK8) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_996,c_1007]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_22,plain,
% 4.08/1.00      ( ~ v5_relat_1(X0,X1)
% 4.08/1.00      | ~ r2_hidden(X2,k1_relat_1(X0))
% 4.08/1.00      | r2_hidden(k1_funct_1(X0,X2),X1)
% 4.08/1.00      | ~ v1_funct_1(X0)
% 4.08/1.00      | ~ v1_relat_1(X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f84]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1011,plain,
% 4.08/1.00      ( v5_relat_1(X0,X1) != iProver_top
% 4.08/1.00      | r2_hidden(X2,k1_relat_1(X0)) != iProver_top
% 4.08/1.00      | r2_hidden(k1_funct_1(X0,X2),X1) = iProver_top
% 4.08/1.00      | v1_funct_1(X0) != iProver_top
% 4.08/1.00      | v1_relat_1(X0) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_6647,plain,
% 4.08/1.00      ( v5_relat_1(sK10,X0) != iProver_top
% 4.08/1.00      | r2_hidden(sK3(sK10,sK9,sK11),k1_relat_1(sK10)) != iProver_top
% 4.08/1.00      | r2_hidden(sK11,X0) = iProver_top
% 4.08/1.00      | v1_funct_1(sK10) != iProver_top
% 4.08/1.00      | v1_relat_1(sK10) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_6643,c_1011]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_7009,plain,
% 4.08/1.00      ( v5_relat_1(sK10,X0) != iProver_top
% 4.08/1.00      | r2_hidden(sK3(sK10,sK9,sK11),k1_relat_1(sK10)) != iProver_top
% 4.08/1.00      | r2_hidden(sK11,X0) = iProver_top ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_6647,c_40,c_42,c_1430]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_7019,plain,
% 4.08/1.00      ( sK8 = k1_xboole_0
% 4.08/1.00      | v5_relat_1(sK10,X0) != iProver_top
% 4.08/1.00      | r2_hidden(sK3(sK10,sK9,sK11),sK7) != iProver_top
% 4.08/1.00      | r2_hidden(sK11,X0) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_2231,c_7009]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_7018,plain,
% 4.08/1.00      ( v5_relat_1(sK10,X0) != iProver_top
% 4.08/1.00      | r2_hidden(sK11,X0) = iProver_top
% 4.08/1.00      | r2_hidden(sK11,k9_relat_1(sK10,sK9)) != iProver_top
% 4.08/1.00      | v1_funct_1(sK10) != iProver_top
% 4.08/1.00      | v1_relat_1(sK10) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_1018,c_7009]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_7199,plain,
% 4.08/1.00      ( v5_relat_1(sK10,X0) != iProver_top | r2_hidden(sK11,X0) = iProver_top ),
% 4.08/1.00      inference(global_propositional_subsumption,
% 4.08/1.00                [status(thm)],
% 4.08/1.00                [c_7019,c_40,c_42,c_1430,c_2868,c_7018]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_7207,plain,
% 4.08/1.00      ( r2_hidden(sK11,sK8) = iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_1729,c_7199]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_11654,plain,
% 4.08/1.00      ( r2_hidden(sK11,k1_xboole_0) = iProver_top ),
% 4.08/1.00      inference(demodulation,[status(thm)],[c_11647,c_7207]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1,plain,
% 4.08/1.00      ( r1_tarski(k1_xboole_0,X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f63]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1032,plain,
% 4.08/1.00      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_24,plain,
% 4.08/1.00      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X1,X0) ),
% 4.08/1.00      inference(cnf_transformation,[],[f86]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1009,plain,
% 4.08/1.00      ( r1_tarski(X0,X1) != iProver_top | r2_hidden(X1,X0) != iProver_top ),
% 4.08/1.00      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_1635,plain,
% 4.08/1.00      ( r2_hidden(X0,k1_xboole_0) != iProver_top ),
% 4.08/1.00      inference(superposition,[status(thm)],[c_1032,c_1009]) ).
% 4.08/1.00  
% 4.08/1.00  cnf(c_13407,plain,
% 4.08/1.00      ( $false ),
% 4.08/1.00      inference(forward_subsumption_resolution,[status(thm)],[c_11654,c_1635]) ).
% 4.08/1.00  
% 4.08/1.00  
% 4.08/1.00  % SZS output end CNFRefutation for theBenchmark.p
% 4.08/1.00  
% 4.08/1.00  ------                               Statistics
% 4.08/1.00  
% 4.08/1.00  ------ Selected
% 4.08/1.00  
% 4.08/1.00  total_time:                             0.375
% 4.08/1.00  
%------------------------------------------------------------------------------
