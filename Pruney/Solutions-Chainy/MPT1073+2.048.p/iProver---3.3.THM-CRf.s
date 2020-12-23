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
% DateTime   : Thu Dec  3 12:10:09 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 213 expanded)
%              Number of clauses        :   44 (  71 expanded)
%              Number of leaves         :   13 (  41 expanded)
%              Depth                    :   16
%              Number of atoms          :  331 ( 931 expanded)
%              Number of equality atoms :   98 ( 237 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,axiom,(
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
    inference(ennf_transformation,[],[f5])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f24,plain,(
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
    inference(nnf_transformation,[],[f14])).

fof(f25,plain,(
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
    inference(rectify,[],[f24])).

fof(f28,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
        & r2_hidden(sK3(X0,X1,X6),X1)
        & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X2)) = X3
        & r2_hidden(sK2(X0,X1,X2),X1)
        & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
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

fof(f29,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f28,f27,f26])).

fof(f41,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f58,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f8,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f9,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f10,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(pure_predicate_removal,[],[f9])).

fof(f17,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f18,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f17])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK7,X4) != sK4
          | ~ m1_subset_1(X4,sK5) )
      & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ! [X4] :
        ( k1_funct_1(sK7,X4) != sK4
        | ~ m1_subset_1(X4,sK5) )
    & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f18,f30])).

fof(f51,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f31])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ( ( m1_subset_1(X1,X0)
            | ~ v1_xboole_0(X1) )
          & ( v1_xboole_0(X1)
            | ~ m1_subset_1(X1,X0) ) )
        | ~ v1_xboole_0(X0) )
      & ( ( ( m1_subset_1(X1,X0)
            | ~ r2_hidden(X1,X0) )
          & ( r2_hidden(X1,X0)
            | ~ m1_subset_1(X1,X0) ) )
        | v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f35,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f20,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f19])).

fof(f21,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).

fof(f32,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f52,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f31])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f57,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK3(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f42])).

fof(f54,plain,(
    ! [X4] :
      ( k1_funct_1(sK7,X4) != sK4
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f31])).

cnf(c_14,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_378,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_14,c_22])).

cnf(c_379,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | r2_hidden(sK3(sK7,X1,X0),X1)
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_378])).

cnf(c_1475,plain,
    ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
    | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_379])).

cnf(c_4,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_147,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4,c_1])).

cnf(c_148,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_147])).

cnf(c_1482,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_148])).

cnf(c_2713,plain,
    ( m1_subset_1(sK3(sK7,X0,X1),X0) = iProver_top
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_1475,c_1482])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_24,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_6,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1675,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_6])).

cnf(c_1808,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_1675])).

cnf(c_1809,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1808])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1857,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1858,plain,
    ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1857])).

cnf(c_3088,plain,
    ( r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | m1_subset_1(sK3(sK7,X0,X1),X0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2713,c_24,c_1809,c_1858])).

cnf(c_3089,plain,
    ( m1_subset_1(sK3(sK7,X0,X1),X0) = iProver_top
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top ),
    inference(renaming,[status(thm)],[c_3088])).

cnf(c_1483,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_18,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1486,plain,
    ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3471,plain,
    ( k7_relset_1(sK5,sK6,sK7,sK5) = k2_relset_1(sK5,sK6,sK7) ),
    inference(superposition,[status(thm)],[c_1483,c_1486])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_1488,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2991,plain,
    ( k7_relset_1(sK5,sK6,sK7,X0) = k9_relat_1(sK7,X0) ),
    inference(superposition,[status(thm)],[c_1483,c_1488])).

cnf(c_3478,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k9_relat_1(sK7,sK5) ),
    inference(demodulation,[status(thm)],[c_3471,c_2991])).

cnf(c_20,negated_conjecture,
    ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1484,plain,
    ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(c_3697,plain,
    ( r2_hidden(sK4,k9_relat_1(sK7,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_3478,c_1484])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_393,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X2,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_22])).

cnf(c_394,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK3(sK7,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_393])).

cnf(c_1474,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_394])).

cnf(c_3713,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK5,sK4)) = sK4
    | v1_relat_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_3697,c_1474])).

cnf(c_3998,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK5,sK4)) = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3713,c_24,c_1809,c_1858])).

cnf(c_19,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | k1_funct_1(sK7,X0) != sK4 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1485,plain,
    ( k1_funct_1(sK7,X0) != sK4
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4002,plain,
    ( m1_subset_1(sK3(sK7,sK5,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3998,c_1485])).

cnf(c_4036,plain,
    ( r2_hidden(sK4,k9_relat_1(sK7,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3089,c_4002])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_4036,c_3697])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % WCLimit    : 600
% 0.12/0.32  % DateTime   : Tue Dec  1 15:34:40 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.32  % Running in FOF mode
% 1.98/0.96  % SZS status Started for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/0.96  
% 1.98/0.96  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 1.98/0.96  
% 1.98/0.96  ------  iProver source info
% 1.98/0.96  
% 1.98/0.96  git: date: 2020-06-30 10:37:57 +0100
% 1.98/0.96  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 1.98/0.96  git: non_committed_changes: false
% 1.98/0.96  git: last_make_outside_of_git: false
% 1.98/0.96  
% 1.98/0.96  ------ 
% 1.98/0.96  
% 1.98/0.96  ------ Input Options
% 1.98/0.96  
% 1.98/0.96  --out_options                           all
% 1.98/0.96  --tptp_safe_out                         true
% 1.98/0.96  --problem_path                          ""
% 1.98/0.96  --include_path                          ""
% 1.98/0.96  --clausifier                            res/vclausify_rel
% 1.98/0.96  --clausifier_options                    --mode clausify
% 1.98/0.96  --stdin                                 false
% 1.98/0.96  --stats_out                             all
% 1.98/0.96  
% 1.98/0.96  ------ General Options
% 1.98/0.96  
% 1.98/0.96  --fof                                   false
% 1.98/0.96  --time_out_real                         305.
% 1.98/0.96  --time_out_virtual                      -1.
% 1.98/0.96  --symbol_type_check                     false
% 1.98/0.96  --clausify_out                          false
% 1.98/0.96  --sig_cnt_out                           false
% 1.98/0.96  --trig_cnt_out                          false
% 1.98/0.96  --trig_cnt_out_tolerance                1.
% 1.98/0.96  --trig_cnt_out_sk_spl                   false
% 1.98/0.96  --abstr_cl_out                          false
% 1.98/0.96  
% 1.98/0.96  ------ Global Options
% 1.98/0.96  
% 1.98/0.96  --schedule                              default
% 1.98/0.96  --add_important_lit                     false
% 1.98/0.96  --prop_solver_per_cl                    1000
% 1.98/0.96  --min_unsat_core                        false
% 1.98/0.96  --soft_assumptions                      false
% 1.98/0.96  --soft_lemma_size                       3
% 1.98/0.96  --prop_impl_unit_size                   0
% 1.98/0.96  --prop_impl_unit                        []
% 1.98/0.96  --share_sel_clauses                     true
% 1.98/0.96  --reset_solvers                         false
% 1.98/0.96  --bc_imp_inh                            [conj_cone]
% 1.98/0.96  --conj_cone_tolerance                   3.
% 1.98/0.96  --extra_neg_conj                        none
% 1.98/0.96  --large_theory_mode                     true
% 1.98/0.96  --prolific_symb_bound                   200
% 1.98/0.96  --lt_threshold                          2000
% 1.98/0.96  --clause_weak_htbl                      true
% 1.98/0.96  --gc_record_bc_elim                     false
% 1.98/0.96  
% 1.98/0.96  ------ Preprocessing Options
% 1.98/0.96  
% 1.98/0.96  --preprocessing_flag                    true
% 1.98/0.96  --time_out_prep_mult                    0.1
% 1.98/0.96  --splitting_mode                        input
% 1.98/0.96  --splitting_grd                         true
% 1.98/0.96  --splitting_cvd                         false
% 1.98/0.96  --splitting_cvd_svl                     false
% 1.98/0.96  --splitting_nvd                         32
% 1.98/0.96  --sub_typing                            true
% 1.98/0.96  --prep_gs_sim                           true
% 1.98/0.96  --prep_unflatten                        true
% 1.98/0.96  --prep_res_sim                          true
% 1.98/0.96  --prep_upred                            true
% 1.98/0.96  --prep_sem_filter                       exhaustive
% 1.98/0.96  --prep_sem_filter_out                   false
% 1.98/0.96  --pred_elim                             true
% 1.98/0.96  --res_sim_input                         true
% 1.98/0.96  --eq_ax_congr_red                       true
% 1.98/0.96  --pure_diseq_elim                       true
% 1.98/0.96  --brand_transform                       false
% 1.98/0.96  --non_eq_to_eq                          false
% 1.98/0.96  --prep_def_merge                        true
% 1.98/0.96  --prep_def_merge_prop_impl              false
% 1.98/0.96  --prep_def_merge_mbd                    true
% 1.98/0.96  --prep_def_merge_tr_red                 false
% 1.98/0.96  --prep_def_merge_tr_cl                  false
% 1.98/0.96  --smt_preprocessing                     true
% 1.98/0.96  --smt_ac_axioms                         fast
% 1.98/0.96  --preprocessed_out                      false
% 1.98/0.96  --preprocessed_stats                    false
% 1.98/0.96  
% 1.98/0.96  ------ Abstraction refinement Options
% 1.98/0.96  
% 1.98/0.96  --abstr_ref                             []
% 1.98/0.96  --abstr_ref_prep                        false
% 1.98/0.96  --abstr_ref_until_sat                   false
% 1.98/0.96  --abstr_ref_sig_restrict                funpre
% 1.98/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.98/0.96  --abstr_ref_under                       []
% 1.98/0.96  
% 1.98/0.96  ------ SAT Options
% 1.98/0.96  
% 1.98/0.96  --sat_mode                              false
% 1.98/0.96  --sat_fm_restart_options                ""
% 1.98/0.96  --sat_gr_def                            false
% 1.98/0.96  --sat_epr_types                         true
% 1.98/0.96  --sat_non_cyclic_types                  false
% 1.98/0.96  --sat_finite_models                     false
% 1.98/0.96  --sat_fm_lemmas                         false
% 1.98/0.96  --sat_fm_prep                           false
% 1.98/0.96  --sat_fm_uc_incr                        true
% 1.98/0.96  --sat_out_model                         small
% 1.98/0.96  --sat_out_clauses                       false
% 1.98/0.96  
% 1.98/0.96  ------ QBF Options
% 1.98/0.96  
% 1.98/0.96  --qbf_mode                              false
% 1.98/0.96  --qbf_elim_univ                         false
% 1.98/0.96  --qbf_dom_inst                          none
% 1.98/0.96  --qbf_dom_pre_inst                      false
% 1.98/0.96  --qbf_sk_in                             false
% 1.98/0.96  --qbf_pred_elim                         true
% 1.98/0.96  --qbf_split                             512
% 1.98/0.96  
% 1.98/0.96  ------ BMC1 Options
% 1.98/0.96  
% 1.98/0.96  --bmc1_incremental                      false
% 1.98/0.96  --bmc1_axioms                           reachable_all
% 1.98/0.96  --bmc1_min_bound                        0
% 1.98/0.96  --bmc1_max_bound                        -1
% 1.98/0.96  --bmc1_max_bound_default                -1
% 1.98/0.96  --bmc1_symbol_reachability              true
% 1.98/0.96  --bmc1_property_lemmas                  false
% 1.98/0.96  --bmc1_k_induction                      false
% 1.98/0.96  --bmc1_non_equiv_states                 false
% 1.98/0.96  --bmc1_deadlock                         false
% 1.98/0.96  --bmc1_ucm                              false
% 1.98/0.96  --bmc1_add_unsat_core                   none
% 1.98/0.96  --bmc1_unsat_core_children              false
% 1.98/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.98/0.96  --bmc1_out_stat                         full
% 1.98/0.96  --bmc1_ground_init                      false
% 1.98/0.96  --bmc1_pre_inst_next_state              false
% 1.98/0.96  --bmc1_pre_inst_state                   false
% 1.98/0.96  --bmc1_pre_inst_reach_state             false
% 1.98/0.96  --bmc1_out_unsat_core                   false
% 1.98/0.96  --bmc1_aig_witness_out                  false
% 1.98/0.96  --bmc1_verbose                          false
% 1.98/0.96  --bmc1_dump_clauses_tptp                false
% 1.98/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.98/0.96  --bmc1_dump_file                        -
% 1.98/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.98/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.98/0.96  --bmc1_ucm_extend_mode                  1
% 1.98/0.96  --bmc1_ucm_init_mode                    2
% 1.98/0.96  --bmc1_ucm_cone_mode                    none
% 1.98/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.98/0.96  --bmc1_ucm_relax_model                  4
% 1.98/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.98/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.98/0.96  --bmc1_ucm_layered_model                none
% 1.98/0.96  --bmc1_ucm_max_lemma_size               10
% 1.98/0.96  
% 1.98/0.96  ------ AIG Options
% 1.98/0.96  
% 1.98/0.96  --aig_mode                              false
% 1.98/0.96  
% 1.98/0.96  ------ Instantiation Options
% 1.98/0.96  
% 1.98/0.96  --instantiation_flag                    true
% 1.98/0.96  --inst_sos_flag                         false
% 1.98/0.96  --inst_sos_phase                        true
% 1.98/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.98/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.98/0.96  --inst_lit_sel_side                     num_symb
% 1.98/0.96  --inst_solver_per_active                1400
% 1.98/0.96  --inst_solver_calls_frac                1.
% 1.98/0.96  --inst_passive_queue_type               priority_queues
% 1.98/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.98/0.96  --inst_passive_queues_freq              [25;2]
% 1.98/0.96  --inst_dismatching                      true
% 1.98/0.96  --inst_eager_unprocessed_to_passive     true
% 1.98/0.96  --inst_prop_sim_given                   true
% 1.98/0.96  --inst_prop_sim_new                     false
% 1.98/0.96  --inst_subs_new                         false
% 1.98/0.96  --inst_eq_res_simp                      false
% 1.98/0.96  --inst_subs_given                       false
% 1.98/0.96  --inst_orphan_elimination               true
% 1.98/0.96  --inst_learning_loop_flag               true
% 1.98/0.96  --inst_learning_start                   3000
% 1.98/0.96  --inst_learning_factor                  2
% 1.98/0.96  --inst_start_prop_sim_after_learn       3
% 1.98/0.96  --inst_sel_renew                        solver
% 1.98/0.96  --inst_lit_activity_flag                true
% 1.98/0.96  --inst_restr_to_given                   false
% 1.98/0.96  --inst_activity_threshold               500
% 1.98/0.96  --inst_out_proof                        true
% 1.98/0.96  
% 1.98/0.96  ------ Resolution Options
% 1.98/0.96  
% 1.98/0.96  --resolution_flag                       true
% 1.98/0.96  --res_lit_sel                           adaptive
% 1.98/0.96  --res_lit_sel_side                      none
% 1.98/0.96  --res_ordering                          kbo
% 1.98/0.96  --res_to_prop_solver                    active
% 1.98/0.96  --res_prop_simpl_new                    false
% 1.98/0.96  --res_prop_simpl_given                  true
% 1.98/0.96  --res_passive_queue_type                priority_queues
% 1.98/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.98/0.96  --res_passive_queues_freq               [15;5]
% 1.98/0.96  --res_forward_subs                      full
% 1.98/0.96  --res_backward_subs                     full
% 1.98/0.96  --res_forward_subs_resolution           true
% 1.98/0.96  --res_backward_subs_resolution          true
% 1.98/0.96  --res_orphan_elimination                true
% 1.98/0.96  --res_time_limit                        2.
% 1.98/0.96  --res_out_proof                         true
% 1.98/0.96  
% 1.98/0.96  ------ Superposition Options
% 1.98/0.96  
% 1.98/0.96  --superposition_flag                    true
% 1.98/0.96  --sup_passive_queue_type                priority_queues
% 1.98/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.98/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.98/0.96  --demod_completeness_check              fast
% 1.98/0.96  --demod_use_ground                      true
% 1.98/0.96  --sup_to_prop_solver                    passive
% 1.98/0.96  --sup_prop_simpl_new                    true
% 1.98/0.96  --sup_prop_simpl_given                  true
% 1.98/0.96  --sup_fun_splitting                     false
% 1.98/0.96  --sup_smt_interval                      50000
% 1.98/0.96  
% 1.98/0.96  ------ Superposition Simplification Setup
% 1.98/0.96  
% 1.98/0.96  --sup_indices_passive                   []
% 1.98/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.98/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.96  --sup_full_bw                           [BwDemod]
% 1.98/0.96  --sup_immed_triv                        [TrivRules]
% 1.98/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.98/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.96  --sup_immed_bw_main                     []
% 1.98/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.98/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.96  
% 1.98/0.96  ------ Combination Options
% 1.98/0.96  
% 1.98/0.96  --comb_res_mult                         3
% 1.98/0.96  --comb_sup_mult                         2
% 1.98/0.96  --comb_inst_mult                        10
% 1.98/0.96  
% 1.98/0.96  ------ Debug Options
% 1.98/0.96  
% 1.98/0.96  --dbg_backtrace                         false
% 1.98/0.96  --dbg_dump_prop_clauses                 false
% 1.98/0.96  --dbg_dump_prop_clauses_file            -
% 1.98/0.96  --dbg_out_stat                          false
% 1.98/0.96  ------ Parsing...
% 1.98/0.96  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 1.98/0.96  
% 1.98/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 1.98/0.96  
% 1.98/0.96  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 1.98/0.96  
% 1.98/0.96  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 1.98/0.96  ------ Proving...
% 1.98/0.96  ------ Problem Properties 
% 1.98/0.96  
% 1.98/0.96  
% 1.98/0.96  clauses                                 22
% 1.98/0.96  conjectures                             3
% 1.98/0.96  EPR                                     5
% 1.98/0.96  Horn                                    17
% 1.98/0.96  unary                                   3
% 1.98/0.96  binary                                  7
% 1.98/0.96  lits                                    60
% 1.98/0.96  lits eq                                 11
% 1.98/0.96  fd_pure                                 0
% 1.98/0.96  fd_pseudo                               0
% 1.98/0.96  fd_cond                                 0
% 1.98/0.96  fd_pseudo_cond                          4
% 1.98/0.96  AC symbols                              0
% 1.98/0.96  
% 1.98/0.96  ------ Schedule dynamic 5 is on 
% 1.98/0.96  
% 1.98/0.96  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 1.98/0.96  
% 1.98/0.96  
% 1.98/0.96  ------ 
% 1.98/0.96  Current options:
% 1.98/0.96  ------ 
% 1.98/0.96  
% 1.98/0.96  ------ Input Options
% 1.98/0.96  
% 1.98/0.96  --out_options                           all
% 1.98/0.96  --tptp_safe_out                         true
% 1.98/0.96  --problem_path                          ""
% 1.98/0.96  --include_path                          ""
% 1.98/0.96  --clausifier                            res/vclausify_rel
% 1.98/0.96  --clausifier_options                    --mode clausify
% 1.98/0.96  --stdin                                 false
% 1.98/0.96  --stats_out                             all
% 1.98/0.96  
% 1.98/0.96  ------ General Options
% 1.98/0.96  
% 1.98/0.96  --fof                                   false
% 1.98/0.96  --time_out_real                         305.
% 1.98/0.96  --time_out_virtual                      -1.
% 1.98/0.96  --symbol_type_check                     false
% 1.98/0.96  --clausify_out                          false
% 1.98/0.96  --sig_cnt_out                           false
% 1.98/0.96  --trig_cnt_out                          false
% 1.98/0.96  --trig_cnt_out_tolerance                1.
% 1.98/0.96  --trig_cnt_out_sk_spl                   false
% 1.98/0.96  --abstr_cl_out                          false
% 1.98/0.96  
% 1.98/0.96  ------ Global Options
% 1.98/0.96  
% 1.98/0.96  --schedule                              default
% 1.98/0.96  --add_important_lit                     false
% 1.98/0.96  --prop_solver_per_cl                    1000
% 1.98/0.96  --min_unsat_core                        false
% 1.98/0.96  --soft_assumptions                      false
% 1.98/0.96  --soft_lemma_size                       3
% 1.98/0.96  --prop_impl_unit_size                   0
% 1.98/0.96  --prop_impl_unit                        []
% 1.98/0.96  --share_sel_clauses                     true
% 1.98/0.96  --reset_solvers                         false
% 1.98/0.96  --bc_imp_inh                            [conj_cone]
% 1.98/0.96  --conj_cone_tolerance                   3.
% 1.98/0.96  --extra_neg_conj                        none
% 1.98/0.96  --large_theory_mode                     true
% 1.98/0.96  --prolific_symb_bound                   200
% 1.98/0.96  --lt_threshold                          2000
% 1.98/0.96  --clause_weak_htbl                      true
% 1.98/0.96  --gc_record_bc_elim                     false
% 1.98/0.96  
% 1.98/0.96  ------ Preprocessing Options
% 1.98/0.96  
% 1.98/0.96  --preprocessing_flag                    true
% 1.98/0.96  --time_out_prep_mult                    0.1
% 1.98/0.96  --splitting_mode                        input
% 1.98/0.96  --splitting_grd                         true
% 1.98/0.96  --splitting_cvd                         false
% 1.98/0.96  --splitting_cvd_svl                     false
% 1.98/0.96  --splitting_nvd                         32
% 1.98/0.96  --sub_typing                            true
% 1.98/0.96  --prep_gs_sim                           true
% 1.98/0.96  --prep_unflatten                        true
% 1.98/0.96  --prep_res_sim                          true
% 1.98/0.96  --prep_upred                            true
% 1.98/0.96  --prep_sem_filter                       exhaustive
% 1.98/0.96  --prep_sem_filter_out                   false
% 1.98/0.96  --pred_elim                             true
% 1.98/0.96  --res_sim_input                         true
% 1.98/0.96  --eq_ax_congr_red                       true
% 1.98/0.96  --pure_diseq_elim                       true
% 1.98/0.96  --brand_transform                       false
% 1.98/0.96  --non_eq_to_eq                          false
% 1.98/0.96  --prep_def_merge                        true
% 1.98/0.96  --prep_def_merge_prop_impl              false
% 1.98/0.96  --prep_def_merge_mbd                    true
% 1.98/0.96  --prep_def_merge_tr_red                 false
% 1.98/0.96  --prep_def_merge_tr_cl                  false
% 1.98/0.96  --smt_preprocessing                     true
% 1.98/0.96  --smt_ac_axioms                         fast
% 1.98/0.96  --preprocessed_out                      false
% 1.98/0.96  --preprocessed_stats                    false
% 1.98/0.96  
% 1.98/0.96  ------ Abstraction refinement Options
% 1.98/0.96  
% 1.98/0.96  --abstr_ref                             []
% 1.98/0.96  --abstr_ref_prep                        false
% 1.98/0.96  --abstr_ref_until_sat                   false
% 1.98/0.96  --abstr_ref_sig_restrict                funpre
% 1.98/0.96  --abstr_ref_af_restrict_to_split_sk     false
% 1.98/0.96  --abstr_ref_under                       []
% 1.98/0.96  
% 1.98/0.96  ------ SAT Options
% 1.98/0.96  
% 1.98/0.96  --sat_mode                              false
% 1.98/0.96  --sat_fm_restart_options                ""
% 1.98/0.96  --sat_gr_def                            false
% 1.98/0.96  --sat_epr_types                         true
% 1.98/0.96  --sat_non_cyclic_types                  false
% 1.98/0.96  --sat_finite_models                     false
% 1.98/0.96  --sat_fm_lemmas                         false
% 1.98/0.96  --sat_fm_prep                           false
% 1.98/0.96  --sat_fm_uc_incr                        true
% 1.98/0.96  --sat_out_model                         small
% 1.98/0.96  --sat_out_clauses                       false
% 1.98/0.96  
% 1.98/0.96  ------ QBF Options
% 1.98/0.96  
% 1.98/0.96  --qbf_mode                              false
% 1.98/0.96  --qbf_elim_univ                         false
% 1.98/0.96  --qbf_dom_inst                          none
% 1.98/0.96  --qbf_dom_pre_inst                      false
% 1.98/0.96  --qbf_sk_in                             false
% 1.98/0.96  --qbf_pred_elim                         true
% 1.98/0.96  --qbf_split                             512
% 1.98/0.96  
% 1.98/0.96  ------ BMC1 Options
% 1.98/0.96  
% 1.98/0.96  --bmc1_incremental                      false
% 1.98/0.96  --bmc1_axioms                           reachable_all
% 1.98/0.96  --bmc1_min_bound                        0
% 1.98/0.96  --bmc1_max_bound                        -1
% 1.98/0.96  --bmc1_max_bound_default                -1
% 1.98/0.96  --bmc1_symbol_reachability              true
% 1.98/0.96  --bmc1_property_lemmas                  false
% 1.98/0.96  --bmc1_k_induction                      false
% 1.98/0.96  --bmc1_non_equiv_states                 false
% 1.98/0.96  --bmc1_deadlock                         false
% 1.98/0.96  --bmc1_ucm                              false
% 1.98/0.96  --bmc1_add_unsat_core                   none
% 1.98/0.96  --bmc1_unsat_core_children              false
% 1.98/0.96  --bmc1_unsat_core_extrapolate_axioms    false
% 1.98/0.96  --bmc1_out_stat                         full
% 1.98/0.96  --bmc1_ground_init                      false
% 1.98/0.96  --bmc1_pre_inst_next_state              false
% 1.98/0.96  --bmc1_pre_inst_state                   false
% 1.98/0.96  --bmc1_pre_inst_reach_state             false
% 1.98/0.96  --bmc1_out_unsat_core                   false
% 1.98/0.96  --bmc1_aig_witness_out                  false
% 1.98/0.96  --bmc1_verbose                          false
% 1.98/0.96  --bmc1_dump_clauses_tptp                false
% 1.98/0.96  --bmc1_dump_unsat_core_tptp             false
% 1.98/0.96  --bmc1_dump_file                        -
% 1.98/0.96  --bmc1_ucm_expand_uc_limit              128
% 1.98/0.96  --bmc1_ucm_n_expand_iterations          6
% 1.98/0.96  --bmc1_ucm_extend_mode                  1
% 1.98/0.96  --bmc1_ucm_init_mode                    2
% 1.98/0.96  --bmc1_ucm_cone_mode                    none
% 1.98/0.96  --bmc1_ucm_reduced_relation_type        0
% 1.98/0.96  --bmc1_ucm_relax_model                  4
% 1.98/0.96  --bmc1_ucm_full_tr_after_sat            true
% 1.98/0.96  --bmc1_ucm_expand_neg_assumptions       false
% 1.98/0.96  --bmc1_ucm_layered_model                none
% 1.98/0.96  --bmc1_ucm_max_lemma_size               10
% 1.98/0.96  
% 1.98/0.96  ------ AIG Options
% 1.98/0.96  
% 1.98/0.96  --aig_mode                              false
% 1.98/0.96  
% 1.98/0.96  ------ Instantiation Options
% 1.98/0.96  
% 1.98/0.96  --instantiation_flag                    true
% 1.98/0.96  --inst_sos_flag                         false
% 1.98/0.96  --inst_sos_phase                        true
% 1.98/0.96  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 1.98/0.96  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 1.98/0.96  --inst_lit_sel_side                     none
% 1.98/0.96  --inst_solver_per_active                1400
% 1.98/0.96  --inst_solver_calls_frac                1.
% 1.98/0.96  --inst_passive_queue_type               priority_queues
% 1.98/0.96  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 1.98/0.96  --inst_passive_queues_freq              [25;2]
% 1.98/0.96  --inst_dismatching                      true
% 1.98/0.96  --inst_eager_unprocessed_to_passive     true
% 1.98/0.96  --inst_prop_sim_given                   true
% 1.98/0.96  --inst_prop_sim_new                     false
% 1.98/0.96  --inst_subs_new                         false
% 1.98/0.96  --inst_eq_res_simp                      false
% 1.98/0.96  --inst_subs_given                       false
% 1.98/0.96  --inst_orphan_elimination               true
% 1.98/0.96  --inst_learning_loop_flag               true
% 1.98/0.96  --inst_learning_start                   3000
% 1.98/0.96  --inst_learning_factor                  2
% 1.98/0.96  --inst_start_prop_sim_after_learn       3
% 1.98/0.96  --inst_sel_renew                        solver
% 1.98/0.96  --inst_lit_activity_flag                true
% 1.98/0.96  --inst_restr_to_given                   false
% 1.98/0.96  --inst_activity_threshold               500
% 1.98/0.96  --inst_out_proof                        true
% 1.98/0.96  
% 1.98/0.96  ------ Resolution Options
% 1.98/0.96  
% 1.98/0.96  --resolution_flag                       false
% 1.98/0.96  --res_lit_sel                           adaptive
% 1.98/0.96  --res_lit_sel_side                      none
% 1.98/0.96  --res_ordering                          kbo
% 1.98/0.96  --res_to_prop_solver                    active
% 1.98/0.96  --res_prop_simpl_new                    false
% 1.98/0.96  --res_prop_simpl_given                  true
% 1.98/0.96  --res_passive_queue_type                priority_queues
% 1.98/0.96  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 1.98/0.96  --res_passive_queues_freq               [15;5]
% 1.98/0.96  --res_forward_subs                      full
% 1.98/0.96  --res_backward_subs                     full
% 1.98/0.96  --res_forward_subs_resolution           true
% 1.98/0.96  --res_backward_subs_resolution          true
% 1.98/0.96  --res_orphan_elimination                true
% 1.98/0.96  --res_time_limit                        2.
% 1.98/0.96  --res_out_proof                         true
% 1.98/0.96  
% 1.98/0.96  ------ Superposition Options
% 1.98/0.96  
% 1.98/0.96  --superposition_flag                    true
% 1.98/0.96  --sup_passive_queue_type                priority_queues
% 1.98/0.96  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 1.98/0.96  --sup_passive_queues_freq               [8;1;4]
% 1.98/0.96  --demod_completeness_check              fast
% 1.98/0.96  --demod_use_ground                      true
% 1.98/0.96  --sup_to_prop_solver                    passive
% 1.98/0.96  --sup_prop_simpl_new                    true
% 1.98/0.96  --sup_prop_simpl_given                  true
% 1.98/0.96  --sup_fun_splitting                     false
% 1.98/0.96  --sup_smt_interval                      50000
% 1.98/0.96  
% 1.98/0.96  ------ Superposition Simplification Setup
% 1.98/0.96  
% 1.98/0.96  --sup_indices_passive                   []
% 1.98/0.96  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.96  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.96  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 1.98/0.96  --sup_full_triv                         [TrivRules;PropSubs]
% 1.98/0.96  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.96  --sup_full_bw                           [BwDemod]
% 1.98/0.96  --sup_immed_triv                        [TrivRules]
% 1.98/0.96  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 1.98/0.96  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.96  --sup_immed_bw_main                     []
% 1.98/0.96  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.96  --sup_input_triv                        [Unflattening;TrivRules]
% 1.98/0.96  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 1.98/0.96  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 1.98/0.96  
% 1.98/0.96  ------ Combination Options
% 1.98/0.96  
% 1.98/0.96  --comb_res_mult                         3
% 1.98/0.96  --comb_sup_mult                         2
% 1.98/0.96  --comb_inst_mult                        10
% 1.98/0.96  
% 1.98/0.96  ------ Debug Options
% 1.98/0.96  
% 1.98/0.96  --dbg_backtrace                         false
% 1.98/0.96  --dbg_dump_prop_clauses                 false
% 1.98/0.96  --dbg_dump_prop_clauses_file            -
% 1.98/0.96  --dbg_out_stat                          false
% 1.98/0.96  
% 1.98/0.96  
% 1.98/0.96  
% 1.98/0.96  
% 1.98/0.96  ------ Proving...
% 1.98/0.96  
% 1.98/0.96  
% 1.98/0.96  % SZS status Theorem for theBenchmark.p
% 1.98/0.96  
% 1.98/0.96  % SZS output start CNFRefutation for theBenchmark.p
% 1.98/0.96  
% 1.98/0.96  fof(f5,axiom,(
% 1.98/0.96    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 1.98/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.96  
% 1.98/0.96  fof(f13,plain,(
% 1.98/0.96    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.98/0.96    inference(ennf_transformation,[],[f5])).
% 1.98/0.96  
% 1.98/0.96  fof(f14,plain,(
% 1.98/0.96    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.98/0.96    inference(flattening,[],[f13])).
% 1.98/0.96  
% 1.98/0.96  fof(f24,plain,(
% 1.98/0.96    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.98/0.96    inference(nnf_transformation,[],[f14])).
% 1.98/0.96  
% 1.98/0.96  fof(f25,plain,(
% 1.98/0.96    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.98/0.96    inference(rectify,[],[f24])).
% 1.98/0.96  
% 1.98/0.96  fof(f28,plain,(
% 1.98/0.96    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))))),
% 1.98/0.96    introduced(choice_axiom,[])).
% 1.98/0.96  
% 1.98/0.96  fof(f27,plain,(
% 1.98/0.96    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X2)) = X3 & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))))) )),
% 1.98/0.96    introduced(choice_axiom,[])).
% 1.98/0.96  
% 1.98/0.96  fof(f26,plain,(
% 1.98/0.96    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK1(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2))))),
% 1.98/0.96    introduced(choice_axiom,[])).
% 1.98/0.96  
% 1.98/0.96  fof(f29,plain,(
% 1.98/0.96    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK1(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK2(X0,X1,X2)) = sK1(X0,X1,X2) & r2_hidden(sK2(X0,X1,X2),X1) & r2_hidden(sK2(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X1,X6)) = X6 & r2_hidden(sK3(X0,X1,X6),X1) & r2_hidden(sK3(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.98/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f25,f28,f27,f26])).
% 1.98/0.96  
% 1.98/0.96  fof(f41,plain,(
% 1.98/0.96    ( ! [X6,X2,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.98/0.96    inference(cnf_transformation,[],[f29])).
% 1.98/0.96  
% 1.98/0.96  fof(f58,plain,(
% 1.98/0.96    ( ! [X6,X0,X1] : (r2_hidden(sK3(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.98/0.96    inference(equality_resolution,[],[f41])).
% 1.98/0.96  
% 1.98/0.96  fof(f8,conjecture,(
% 1.98/0.96    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.98/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.96  
% 1.98/0.96  fof(f9,negated_conjecture,(
% 1.98/0.96    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.98/0.96    inference(negated_conjecture,[],[f8])).
% 1.98/0.96  
% 1.98/0.96  fof(f10,plain,(
% 1.98/0.96    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 1.98/0.96    inference(pure_predicate_removal,[],[f9])).
% 1.98/0.96  
% 1.98/0.96  fof(f17,plain,(
% 1.98/0.96    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)))),
% 1.98/0.96    inference(ennf_transformation,[],[f10])).
% 1.98/0.96  
% 1.98/0.96  fof(f18,plain,(
% 1.98/0.96    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3))),
% 1.98/0.96    inference(flattening,[],[f17])).
% 1.98/0.96  
% 1.98/0.96  fof(f30,plain,(
% 1.98/0.96    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK7))),
% 1.98/0.96    introduced(choice_axiom,[])).
% 1.98/0.96  
% 1.98/0.96  fof(f31,plain,(
% 1.98/0.96    ! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_1(sK7)),
% 1.98/0.96    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f18,f30])).
% 1.98/0.96  
% 1.98/0.96  fof(f51,plain,(
% 1.98/0.96    v1_funct_1(sK7)),
% 1.98/0.96    inference(cnf_transformation,[],[f31])).
% 1.98/0.96  
% 1.98/0.96  fof(f2,axiom,(
% 1.98/0.96    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 1.98/0.96    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.96  
% 1.98/0.96  fof(f11,plain,(
% 1.98/0.96    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 1.98/0.96    inference(ennf_transformation,[],[f2])).
% 1.98/0.96  
% 1.98/0.96  fof(f23,plain,(
% 1.98/0.96    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 1.98/0.96    inference(nnf_transformation,[],[f11])).
% 1.98/0.96  
% 1.98/0.96  fof(f35,plain,(
% 1.98/0.96    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f23])).
% 1.98/0.97  
% 1.98/0.97  fof(f1,axiom,(
% 1.98/0.97    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.98/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.97  
% 1.98/0.97  fof(f19,plain,(
% 1.98/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 1.98/0.97    inference(nnf_transformation,[],[f1])).
% 1.98/0.97  
% 1.98/0.97  fof(f20,plain,(
% 1.98/0.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.98/0.97    inference(rectify,[],[f19])).
% 1.98/0.97  
% 1.98/0.97  fof(f21,plain,(
% 1.98/0.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 1.98/0.97    introduced(choice_axiom,[])).
% 1.98/0.97  
% 1.98/0.97  fof(f22,plain,(
% 1.98/0.97    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 1.98/0.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f20,f21])).
% 1.98/0.97  
% 1.98/0.97  fof(f32,plain,(
% 1.98/0.97    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f22])).
% 1.98/0.97  
% 1.98/0.97  fof(f52,plain,(
% 1.98/0.97    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 1.98/0.97    inference(cnf_transformation,[],[f31])).
% 1.98/0.97  
% 1.98/0.97  fof(f3,axiom,(
% 1.98/0.97    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.98/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.97  
% 1.98/0.97  fof(f12,plain,(
% 1.98/0.97    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.98/0.97    inference(ennf_transformation,[],[f3])).
% 1.98/0.97  
% 1.98/0.97  fof(f38,plain,(
% 1.98/0.97    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f12])).
% 1.98/0.97  
% 1.98/0.97  fof(f4,axiom,(
% 1.98/0.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.98/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.97  
% 1.98/0.97  fof(f39,plain,(
% 1.98/0.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.98/0.97    inference(cnf_transformation,[],[f4])).
% 1.98/0.97  
% 1.98/0.97  fof(f7,axiom,(
% 1.98/0.97    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 1.98/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.97  
% 1.98/0.97  fof(f16,plain,(
% 1.98/0.97    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.98/0.97    inference(ennf_transformation,[],[f7])).
% 1.98/0.97  
% 1.98/0.97  fof(f49,plain,(
% 1.98/0.97    ( ! [X2,X0,X1] : (k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.98/0.97    inference(cnf_transformation,[],[f16])).
% 1.98/0.97  
% 1.98/0.97  fof(f6,axiom,(
% 1.98/0.97    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 1.98/0.97    file('/export/starexec/sandbox/benchmark/theBenchmark.p',unknown)).
% 1.98/0.97  
% 1.98/0.97  fof(f15,plain,(
% 1.98/0.97    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.98/0.97    inference(ennf_transformation,[],[f6])).
% 1.98/0.97  
% 1.98/0.97  fof(f48,plain,(
% 1.98/0.97    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.98/0.97    inference(cnf_transformation,[],[f15])).
% 1.98/0.97  
% 1.98/0.97  fof(f53,plain,(
% 1.98/0.97    r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))),
% 1.98/0.97    inference(cnf_transformation,[],[f31])).
% 1.98/0.97  
% 1.98/0.97  fof(f42,plain,(
% 1.98/0.97    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f29])).
% 1.98/0.97  
% 1.98/0.97  fof(f57,plain,(
% 1.98/0.97    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK3(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.98/0.97    inference(equality_resolution,[],[f42])).
% 1.98/0.97  
% 1.98/0.97  fof(f54,plain,(
% 1.98/0.97    ( ! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) )),
% 1.98/0.97    inference(cnf_transformation,[],[f31])).
% 1.98/0.97  
% 1.98/0.97  cnf(c_14,plain,
% 1.98/0.97      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.98/0.97      | r2_hidden(sK3(X1,X2,X0),X2)
% 1.98/0.97      | ~ v1_funct_1(X1)
% 1.98/0.97      | ~ v1_relat_1(X1) ),
% 1.98/0.97      inference(cnf_transformation,[],[f58]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_22,negated_conjecture,
% 1.98/0.97      ( v1_funct_1(sK7) ),
% 1.98/0.97      inference(cnf_transformation,[],[f51]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_378,plain,
% 1.98/0.97      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.98/0.97      | r2_hidden(sK3(X1,X2,X0),X2)
% 1.98/0.97      | ~ v1_relat_1(X1)
% 1.98/0.97      | sK7 != X1 ),
% 1.98/0.97      inference(resolution_lifted,[status(thm)],[c_14,c_22]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_379,plain,
% 1.98/0.97      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 1.98/0.97      | r2_hidden(sK3(sK7,X1,X0),X1)
% 1.98/0.97      | ~ v1_relat_1(sK7) ),
% 1.98/0.97      inference(unflattening,[status(thm)],[c_378]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1475,plain,
% 1.98/0.97      ( r2_hidden(X0,k9_relat_1(sK7,X1)) != iProver_top
% 1.98/0.97      | r2_hidden(sK3(sK7,X1,X0),X1) = iProver_top
% 1.98/0.97      | v1_relat_1(sK7) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_379]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_4,plain,
% 1.98/0.97      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 1.98/0.97      inference(cnf_transformation,[],[f35]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1,plain,
% 1.98/0.97      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 1.98/0.97      inference(cnf_transformation,[],[f32]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_147,plain,
% 1.98/0.97      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 1.98/0.97      inference(global_propositional_subsumption,[status(thm)],[c_4,c_1]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_148,plain,
% 1.98/0.97      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 1.98/0.97      inference(renaming,[status(thm)],[c_147]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1482,plain,
% 1.98/0.97      ( m1_subset_1(X0,X1) = iProver_top
% 1.98/0.97      | r2_hidden(X0,X1) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_148]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_2713,plain,
% 1.98/0.97      ( m1_subset_1(sK3(sK7,X0,X1),X0) = iProver_top
% 1.98/0.97      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 1.98/0.97      | v1_relat_1(sK7) != iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_1475,c_1482]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_21,negated_conjecture,
% 1.98/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 1.98/0.97      inference(cnf_transformation,[],[f52]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_24,plain,
% 1.98/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_6,plain,
% 1.98/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 1.98/0.97      | ~ v1_relat_1(X1)
% 1.98/0.97      | v1_relat_1(X0) ),
% 1.98/0.97      inference(cnf_transformation,[],[f38]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1675,plain,
% 1.98/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.98/0.97      | v1_relat_1(X0)
% 1.98/0.97      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_6]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1808,plain,
% 1.98/0.97      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 1.98/0.97      | ~ v1_relat_1(k2_zfmisc_1(sK5,sK6))
% 1.98/0.97      | v1_relat_1(sK7) ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_1675]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1809,plain,
% 1.98/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 1.98/0.97      | v1_relat_1(k2_zfmisc_1(sK5,sK6)) != iProver_top
% 1.98/0.97      | v1_relat_1(sK7) = iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_1808]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_7,plain,
% 1.98/0.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 1.98/0.97      inference(cnf_transformation,[],[f39]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1857,plain,
% 1.98/0.97      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) ),
% 1.98/0.97      inference(instantiation,[status(thm)],[c_7]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1858,plain,
% 1.98/0.97      ( v1_relat_1(k2_zfmisc_1(sK5,sK6)) = iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_1857]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3088,plain,
% 1.98/0.97      ( r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 1.98/0.97      | m1_subset_1(sK3(sK7,X0,X1),X0) = iProver_top ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_2713,c_24,c_1809,c_1858]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3089,plain,
% 1.98/0.97      ( m1_subset_1(sK3(sK7,X0,X1),X0) = iProver_top
% 1.98/0.97      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top ),
% 1.98/0.97      inference(renaming,[status(thm)],[c_3088]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1483,plain,
% 1.98/0.97      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_18,plain,
% 1.98/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.98/0.97      | k7_relset_1(X1,X2,X0,X1) = k2_relset_1(X1,X2,X0) ),
% 1.98/0.97      inference(cnf_transformation,[],[f49]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1486,plain,
% 1.98/0.97      ( k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)
% 1.98/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3471,plain,
% 1.98/0.97      ( k7_relset_1(sK5,sK6,sK7,sK5) = k2_relset_1(sK5,sK6,sK7) ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_1483,c_1486]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_16,plain,
% 1.98/0.97      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 1.98/0.97      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 1.98/0.97      inference(cnf_transformation,[],[f48]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1488,plain,
% 1.98/0.97      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 1.98/0.97      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_2991,plain,
% 1.98/0.97      ( k7_relset_1(sK5,sK6,sK7,X0) = k9_relat_1(sK7,X0) ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_1483,c_1488]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3478,plain,
% 1.98/0.97      ( k2_relset_1(sK5,sK6,sK7) = k9_relat_1(sK7,sK5) ),
% 1.98/0.97      inference(demodulation,[status(thm)],[c_3471,c_2991]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_20,negated_conjecture,
% 1.98/0.97      ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
% 1.98/0.97      inference(cnf_transformation,[],[f53]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1484,plain,
% 1.98/0.97      ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) = iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_20]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3697,plain,
% 1.98/0.97      ( r2_hidden(sK4,k9_relat_1(sK7,sK5)) = iProver_top ),
% 1.98/0.97      inference(demodulation,[status(thm)],[c_3478,c_1484]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_13,plain,
% 1.98/0.97      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.98/0.97      | ~ v1_funct_1(X1)
% 1.98/0.97      | ~ v1_relat_1(X1)
% 1.98/0.97      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0 ),
% 1.98/0.97      inference(cnf_transformation,[],[f57]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_393,plain,
% 1.98/0.97      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 1.98/0.97      | ~ v1_relat_1(X1)
% 1.98/0.97      | k1_funct_1(X1,sK3(X1,X2,X0)) = X0
% 1.98/0.97      | sK7 != X1 ),
% 1.98/0.97      inference(resolution_lifted,[status(thm)],[c_13,c_22]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_394,plain,
% 1.98/0.97      ( ~ r2_hidden(X0,k9_relat_1(sK7,X1))
% 1.98/0.97      | ~ v1_relat_1(sK7)
% 1.98/0.97      | k1_funct_1(sK7,sK3(sK7,X1,X0)) = X0 ),
% 1.98/0.97      inference(unflattening,[status(thm)],[c_393]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1474,plain,
% 1.98/0.97      ( k1_funct_1(sK7,sK3(sK7,X0,X1)) = X1
% 1.98/0.97      | r2_hidden(X1,k9_relat_1(sK7,X0)) != iProver_top
% 1.98/0.97      | v1_relat_1(sK7) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_394]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3713,plain,
% 1.98/0.97      ( k1_funct_1(sK7,sK3(sK7,sK5,sK4)) = sK4
% 1.98/0.97      | v1_relat_1(sK7) != iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_3697,c_1474]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_3998,plain,
% 1.98/0.97      ( k1_funct_1(sK7,sK3(sK7,sK5,sK4)) = sK4 ),
% 1.98/0.97      inference(global_propositional_subsumption,
% 1.98/0.97                [status(thm)],
% 1.98/0.97                [c_3713,c_24,c_1809,c_1858]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_19,negated_conjecture,
% 1.98/0.97      ( ~ m1_subset_1(X0,sK5) | k1_funct_1(sK7,X0) != sK4 ),
% 1.98/0.97      inference(cnf_transformation,[],[f54]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_1485,plain,
% 1.98/0.97      ( k1_funct_1(sK7,X0) != sK4 | m1_subset_1(X0,sK5) != iProver_top ),
% 1.98/0.97      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_4002,plain,
% 1.98/0.97      ( m1_subset_1(sK3(sK7,sK5,sK4),sK5) != iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_3998,c_1485]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(c_4036,plain,
% 1.98/0.97      ( r2_hidden(sK4,k9_relat_1(sK7,sK5)) != iProver_top ),
% 1.98/0.97      inference(superposition,[status(thm)],[c_3089,c_4002]) ).
% 1.98/0.97  
% 1.98/0.97  cnf(contradiction,plain,
% 1.98/0.97      ( $false ),
% 1.98/0.97      inference(minisat,[status(thm)],[c_4036,c_3697]) ).
% 1.98/0.97  
% 1.98/0.97  
% 1.98/0.97  % SZS output end CNFRefutation for theBenchmark.p
% 1.98/0.97  
% 1.98/0.97  ------                               Statistics
% 1.98/0.97  
% 1.98/0.97  ------ General
% 1.98/0.97  
% 1.98/0.97  abstr_ref_over_cycles:                  0
% 1.98/0.97  abstr_ref_under_cycles:                 0
% 1.98/0.97  gc_basic_clause_elim:                   0
% 1.98/0.97  forced_gc_time:                         0
% 1.98/0.97  parsing_time:                           0.009
% 1.98/0.97  unif_index_cands_time:                  0.
% 1.98/0.97  unif_index_add_time:                    0.
% 1.98/0.97  orderings_time:                         0.
% 1.98/0.97  out_proof_time:                         0.006
% 1.98/0.97  total_time:                             0.137
% 1.98/0.97  num_of_symbols:                         53
% 1.98/0.97  num_of_terms:                           3266
% 1.98/0.97  
% 1.98/0.97  ------ Preprocessing
% 1.98/0.97  
% 1.98/0.97  num_of_splits:                          0
% 1.98/0.97  num_of_split_atoms:                     0
% 1.98/0.97  num_of_reused_defs:                     0
% 1.98/0.97  num_eq_ax_congr_red:                    65
% 1.98/0.97  num_of_sem_filtered_clauses:            1
% 1.98/0.97  num_of_subtypes:                        0
% 1.98/0.97  monotx_restored_types:                  0
% 1.98/0.97  sat_num_of_epr_types:                   0
% 1.98/0.97  sat_num_of_non_cyclic_types:            0
% 1.98/0.97  sat_guarded_non_collapsed_types:        0
% 1.98/0.97  num_pure_diseq_elim:                    0
% 1.98/0.97  simp_replaced_by:                       0
% 1.98/0.97  res_preprocessed:                       118
% 1.98/0.97  prep_upred:                             0
% 1.98/0.97  prep_unflattend:                        66
% 1.98/0.97  smt_new_axioms:                         0
% 1.98/0.97  pred_elim_cands:                        4
% 1.98/0.97  pred_elim:                              1
% 1.98/0.97  pred_elim_cl:                           1
% 1.98/0.97  pred_elim_cycles:                       3
% 1.98/0.97  merged_defs:                            0
% 1.98/0.97  merged_defs_ncl:                        0
% 1.98/0.97  bin_hyper_res:                          0
% 1.98/0.97  prep_cycles:                            4
% 1.98/0.97  pred_elim_time:                         0.01
% 1.98/0.97  splitting_time:                         0.
% 1.98/0.97  sem_filter_time:                        0.
% 1.98/0.97  monotx_time:                            0.001
% 1.98/0.97  subtype_inf_time:                       0.
% 1.98/0.97  
% 1.98/0.97  ------ Problem properties
% 1.98/0.97  
% 1.98/0.97  clauses:                                22
% 1.98/0.97  conjectures:                            3
% 1.98/0.97  epr:                                    5
% 1.98/0.97  horn:                                   17
% 1.98/0.97  ground:                                 2
% 1.98/0.97  unary:                                  3
% 1.98/0.97  binary:                                 7
% 1.98/0.97  lits:                                   60
% 1.98/0.97  lits_eq:                                11
% 1.98/0.97  fd_pure:                                0
% 1.98/0.97  fd_pseudo:                              0
% 1.98/0.97  fd_cond:                                0
% 1.98/0.97  fd_pseudo_cond:                         4
% 1.98/0.97  ac_symbols:                             0
% 1.98/0.97  
% 1.98/0.97  ------ Propositional Solver
% 1.98/0.97  
% 1.98/0.97  prop_solver_calls:                      27
% 1.98/0.97  prop_fast_solver_calls:                 892
% 1.98/0.97  smt_solver_calls:                       0
% 1.98/0.97  smt_fast_solver_calls:                  0
% 1.98/0.97  prop_num_of_clauses:                    1348
% 1.98/0.97  prop_preprocess_simplified:             4660
% 1.98/0.97  prop_fo_subsumed:                       12
% 1.98/0.97  prop_solver_time:                       0.
% 1.98/0.97  smt_solver_time:                        0.
% 1.98/0.97  smt_fast_solver_time:                   0.
% 1.98/0.97  prop_fast_solver_time:                  0.
% 1.98/0.97  prop_unsat_core_time:                   0.
% 1.98/0.97  
% 1.98/0.97  ------ QBF
% 1.98/0.97  
% 1.98/0.97  qbf_q_res:                              0
% 1.98/0.97  qbf_num_tautologies:                    0
% 1.98/0.97  qbf_prep_cycles:                        0
% 1.98/0.97  
% 1.98/0.97  ------ BMC1
% 1.98/0.97  
% 1.98/0.97  bmc1_current_bound:                     -1
% 1.98/0.97  bmc1_last_solved_bound:                 -1
% 1.98/0.97  bmc1_unsat_core_size:                   -1
% 1.98/0.97  bmc1_unsat_core_parents_size:           -1
% 1.98/0.97  bmc1_merge_next_fun:                    0
% 1.98/0.97  bmc1_unsat_core_clauses_time:           0.
% 1.98/0.97  
% 1.98/0.97  ------ Instantiation
% 1.98/0.97  
% 1.98/0.97  inst_num_of_clauses:                    300
% 1.98/0.97  inst_num_in_passive:                    60
% 1.98/0.97  inst_num_in_active:                     187
% 1.98/0.97  inst_num_in_unprocessed:                53
% 1.98/0.97  inst_num_of_loops:                      230
% 1.98/0.97  inst_num_of_learning_restarts:          0
% 1.98/0.97  inst_num_moves_active_passive:          39
% 1.98/0.97  inst_lit_activity:                      0
% 1.98/0.97  inst_lit_activity_moves:                0
% 1.98/0.97  inst_num_tautologies:                   0
% 1.98/0.97  inst_num_prop_implied:                  0
% 1.98/0.97  inst_num_existing_simplified:           0
% 1.98/0.97  inst_num_eq_res_simplified:             0
% 1.98/0.97  inst_num_child_elim:                    0
% 1.98/0.97  inst_num_of_dismatching_blockings:      65
% 1.98/0.97  inst_num_of_non_proper_insts:           259
% 1.98/0.97  inst_num_of_duplicates:                 0
% 1.98/0.97  inst_inst_num_from_inst_to_res:         0
% 1.98/0.97  inst_dismatching_checking_time:         0.
% 1.98/0.97  
% 1.98/0.97  ------ Resolution
% 1.98/0.97  
% 1.98/0.97  res_num_of_clauses:                     0
% 1.98/0.97  res_num_in_passive:                     0
% 1.98/0.97  res_num_in_active:                      0
% 1.98/0.97  res_num_of_loops:                       122
% 1.98/0.97  res_forward_subset_subsumed:            15
% 1.98/0.97  res_backward_subset_subsumed:           0
% 1.98/0.97  res_forward_subsumed:                   0
% 1.98/0.97  res_backward_subsumed:                  0
% 1.98/0.97  res_forward_subsumption_resolution:     0
% 1.98/0.97  res_backward_subsumption_resolution:    0
% 1.98/0.97  res_clause_to_clause_subsumption:       210
% 1.98/0.97  res_orphan_elimination:                 0
% 1.98/0.97  res_tautology_del:                      10
% 1.98/0.97  res_num_eq_res_simplified:              0
% 1.98/0.97  res_num_sel_changes:                    0
% 1.98/0.97  res_moves_from_active_to_pass:          0
% 1.98/0.97  
% 1.98/0.97  ------ Superposition
% 1.98/0.97  
% 1.98/0.97  sup_time_total:                         0.
% 1.98/0.97  sup_time_generating:                    0.
% 1.98/0.97  sup_time_sim_full:                      0.
% 1.98/0.97  sup_time_sim_immed:                     0.
% 1.98/0.97  
% 1.98/0.97  sup_num_of_clauses:                     105
% 1.98/0.97  sup_num_in_active:                      43
% 1.98/0.97  sup_num_in_passive:                     62
% 1.98/0.97  sup_num_of_loops:                       45
% 1.98/0.97  sup_fw_superposition:                   67
% 1.98/0.97  sup_bw_superposition:                   38
% 1.98/0.97  sup_immediate_simplified:               14
% 1.98/0.97  sup_given_eliminated:                   0
% 1.98/0.97  comparisons_done:                       0
% 1.98/0.97  comparisons_avoided:                    2
% 1.98/0.97  
% 1.98/0.97  ------ Simplifications
% 1.98/0.97  
% 1.98/0.97  
% 1.98/0.97  sim_fw_subset_subsumed:                 7
% 1.98/0.97  sim_bw_subset_subsumed:                 0
% 1.98/0.97  sim_fw_subsumed:                        7
% 1.98/0.97  sim_bw_subsumed:                        0
% 1.98/0.97  sim_fw_subsumption_res:                 0
% 1.98/0.97  sim_bw_subsumption_res:                 0
% 1.98/0.97  sim_tautology_del:                      5
% 1.98/0.97  sim_eq_tautology_del:                   0
% 1.98/0.97  sim_eq_res_simp:                        0
% 1.98/0.97  sim_fw_demodulated:                     1
% 1.98/0.97  sim_bw_demodulated:                     3
% 1.98/0.97  sim_light_normalised:                   0
% 1.98/0.97  sim_joinable_taut:                      0
% 1.98/0.97  sim_joinable_simp:                      0
% 1.98/0.97  sim_ac_normalised:                      0
% 1.98/0.97  sim_smt_subsumption:                    0
% 1.98/0.97  
%------------------------------------------------------------------------------
