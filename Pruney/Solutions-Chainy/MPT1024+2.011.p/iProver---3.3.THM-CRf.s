%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:49 EST 2020

% Result     : Theorem 39.54s
% Output     : CNFRefutation 39.54s
% Verified   : 
% Statistics : Number of formulae       :  161 ( 685 expanded)
%              Number of clauses        :   87 ( 186 expanded)
%              Number of leaves         :   19 ( 156 expanded)
%              Depth                    :   19
%              Number of atoms          :  593 (3394 expanded)
%              Number of equality atoms :  125 ( 507 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal clause size      :   13 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f40,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ~ ( ! [X5] :
                ~ ( k1_funct_1(X3,X5) = X4
                  & r2_hidden(X5,X2)
                  & r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(negated_conjecture,[],[f40])).

fof(f44,plain,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
       => ! [X4] :
            ~ ( ! [X5] :
                  ~ ( k1_funct_1(X3,X5) = X4
                    & r2_hidden(X5,X2)
                    & r2_hidden(X5,X0) )
              & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    inference(pure_predicate_removal,[],[f41])).

fof(f84,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f44])).

fof(f85,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f84])).

fof(f113,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK10
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK10,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f112,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK9,X5) != X4
              | ~ r2_hidden(X5,sK8)
              | ~ r2_hidden(X5,sK6) )
          & r2_hidden(X4,k7_relset_1(sK6,sK7,sK9,sK8)) )
      & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
      & v1_funct_1(sK9) ) ),
    introduced(choice_axiom,[])).

fof(f114,plain,
    ( ! [X5] :
        ( k1_funct_1(sK9,X5) != sK10
        | ~ r2_hidden(X5,sK8)
        | ~ r2_hidden(X5,sK6) )
    & r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))
    & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    & v1_funct_1(sK9) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f85,f113,f112])).

fof(f179,plain,(
    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f114])).

fof(f33,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f78,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f163,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f78])).

fof(f180,plain,(
    r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) ),
    inference(cnf_transformation,[],[f114])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f61,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k9_relat_1(X2,X1))
      <=> ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(k4_tarski(X3,X0),X2)
            & r2_hidden(X3,k1_relat_1(X2)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f99,plain,(
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
    inference(nnf_transformation,[],[f61])).

fof(f100,plain,(
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
    inference(rectify,[],[f99])).

fof(f101,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( r2_hidden(X4,X1)
          & r2_hidden(k4_tarski(X4,X0),X2)
          & r2_hidden(X4,k1_relat_1(X2)) )
     => ( r2_hidden(sK3(X0,X1,X2),X1)
        & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
        & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f102,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k9_relat_1(X2,X1))
          | ! [X3] :
              ( ~ r2_hidden(X3,X1)
              | ~ r2_hidden(k4_tarski(X3,X0),X2)
              | ~ r2_hidden(X3,k1_relat_1(X2)) ) )
        & ( ( r2_hidden(sK3(X0,X1,X2),X1)
            & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
            & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) )
          | ~ r2_hidden(X0,k9_relat_1(X2,X1)) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f100,f101])).

fof(f143,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f56])).

fof(f139,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f55,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f54])).

fof(f138,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f140,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3] :
      ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
    <=> ( r2_hidden(X1,X3)
        & r2_hidden(X0,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f92,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(nnf_transformation,[],[f5])).

fof(f93,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))
        | ~ r2_hidden(X1,X3)
        | ~ r2_hidden(X0,X2) )
      & ( ( r2_hidden(X1,X3)
          & r2_hidden(X0,X2) )
        | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ) ),
    inference(flattening,[],[f92])).

fof(f123,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X1,X3)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f29,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f74,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f74])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f121,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f144,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(sK3(X0,X1,X2),X1)
      | ~ r2_hidden(X0,k9_relat_1(X2,X1))
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f102])).

fof(f36,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ~ v1_xboole_0(X2)
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
                 => ! [X4] :
                      ( m1_subset_1(X4,X0)
                     => ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                      <=> ? [X5] :
                            ( r2_hidden(X5,X1)
                            & r2_hidden(k4_tarski(X5,X4),X3)
                            & m1_subset_1(X5,X2) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f36])).

fof(f106,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X5] :
                              ( r2_hidden(X5,X1)
                              & r2_hidden(k4_tarski(X5,X4),X3)
                              & m1_subset_1(X5,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f81])).

fof(f107,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ? [X6] :
                              ( r2_hidden(X6,X1)
                              & r2_hidden(k4_tarski(X6,X4),X3)
                              & m1_subset_1(X6,X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(rectify,[],[f106])).

fof(f108,plain,(
    ! [X4,X3,X2,X1] :
      ( ? [X6] :
          ( r2_hidden(X6,X1)
          & r2_hidden(k4_tarski(X6,X4),X3)
          & m1_subset_1(X6,X2) )
     => ( r2_hidden(sK4(X1,X2,X3,X4),X1)
        & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
        & m1_subset_1(sK4(X1,X2,X3,X4),X2) ) ) ),
    introduced(choice_axiom,[])).

fof(f109,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ( ( r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
                          | ! [X5] :
                              ( ~ r2_hidden(X5,X1)
                              | ~ r2_hidden(k4_tarski(X5,X4),X3)
                              | ~ m1_subset_1(X5,X2) ) )
                        & ( ( r2_hidden(sK4(X1,X2,X3,X4),X1)
                            & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
                            & m1_subset_1(sK4(X1,X2,X3,X4),X2) )
                          | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) ) )
                      | ~ m1_subset_1(X4,X0) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) )
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f107,f108])).

fof(f168,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f169,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( r2_hidden(sK4(X1,X2,X3,X4),X1)
      | ~ r2_hidden(X4,k7_relset_1(X2,X0,X3,X1))
      | ~ m1_subset_1(X4,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f109])).

fof(f27,axiom,(
    ! [X0,X1,X2] :
      ( ( v1_funct_1(X2)
        & v1_relat_1(X2) )
     => ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f72,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f27])).

fof(f73,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k4_tarski(X0,X1),X2)
      <=> ( k1_funct_1(X2,X0) = X1
          & r2_hidden(X0,k1_relat_1(X2)) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f72])).

fof(f103,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f73])).

fof(f104,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(k4_tarski(X0,X1),X2)
          | k1_funct_1(X2,X0) != X1
          | ~ r2_hidden(X0,k1_relat_1(X2)) )
        & ( ( k1_funct_1(X2,X0) = X1
            & r2_hidden(X0,k1_relat_1(X2)) )
          | ~ r2_hidden(k4_tarski(X0,X1),X2) ) )
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f103])).

fof(f155,plain,(
    ! [X2,X0,X1] :
      ( k1_funct_1(X2,X0) = X1
      | ~ r2_hidden(k4_tarski(X0,X1),X2)
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f181,plain,(
    ! [X5] :
      ( k1_funct_1(sK9,X5) != sK10
      | ~ r2_hidden(X5,sK8)
      | ~ r2_hidden(X5,sK6) ) ),
    inference(cnf_transformation,[],[f114])).

fof(f178,plain,(
    v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f114])).

fof(f122,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_hidden(X0,X2)
      | ~ r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) ) ),
    inference(cnf_transformation,[],[f93])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f137,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f156,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k4_tarski(X0,X1),X2)
      | k1_funct_1(X2,X0) != X1
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f104])).

fof(f193,plain,(
    ! [X2,X0] :
      ( r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2)
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ v1_funct_1(X2)
      | ~ v1_relat_1(X2) ) ),
    inference(equality_resolution,[],[f156])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f86,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f87,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f86])).

fof(f88,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f89,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f87,f88])).

fof(f116,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK0(X0),X0) ) ),
    inference(cnf_transformation,[],[f89])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
         => v1_xboole_0(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f76,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_xboole_0(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f161,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_62,negated_conjecture,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
    inference(cnf_transformation,[],[f179])).

cnf(c_1688,plain,
    ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_62])).

cnf(c_46,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f163])).

cnf(c_1703,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_46])).

cnf(c_5861,plain,
    ( k7_relset_1(sK6,sK7,sK9,X0) = k9_relat_1(sK9,X0) ),
    inference(superposition,[status(thm)],[c_1688,c_1703])).

cnf(c_61,negated_conjecture,
    ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) ),
    inference(cnf_transformation,[],[f180])).

cnf(c_1689,plain,
    ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_61])).

cnf(c_21966,plain,
    ( r2_hidden(sK10,k9_relat_1(sK9,sK8)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_5861,c_1689])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f143])).

cnf(c_1720,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_22,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
    | ~ r2_hidden(X0,X2) ),
    inference(cnf_transformation,[],[f139])).

cnf(c_1725,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X0,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_6810,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1688,c_1725])).

cnf(c_21,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f138])).

cnf(c_1726,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_33398,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top
    | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) = iProver_top ),
    inference(superposition,[status(thm)],[c_6810,c_1726])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f140])).

cnf(c_5604,plain,
    ( ~ r2_hidden(X0,sK9)
    | ~ v1_xboole_0(k2_zfmisc_1(sK6,sK7)) ),
    inference(resolution,[status(thm)],[c_23,c_62])).

cnf(c_5205,plain,
    ( m1_subset_1(X0,k2_zfmisc_1(sK6,sK7))
    | ~ r2_hidden(X0,sK9) ),
    inference(resolution,[status(thm)],[c_22,c_62])).

cnf(c_5215,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7))
    | ~ r2_hidden(X0,sK9)
    | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) ),
    inference(resolution,[status(thm)],[c_5205,c_21])).

cnf(c_5905,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7))
    | ~ r2_hidden(X0,sK9) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5604,c_5215])).

cnf(c_5908,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5905])).

cnf(c_95878,plain,
    ( r2_hidden(X0,sK9) != iProver_top
    | r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_33398,c_5908])).

cnf(c_95879,plain,
    ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top
    | r2_hidden(X0,sK9) != iProver_top ),
    inference(renaming,[status(thm)],[c_95878])).

cnf(c_8,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
    inference(cnf_transformation,[],[f123])).

cnf(c_1734,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_95888,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(k4_tarski(X1,X0),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_95879,c_1734])).

cnf(c_96999,plain,
    ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_1720,c_95888])).

cnf(c_42,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_2814,plain,
    ( v1_relat_1(sK9) ),
    inference(resolution,[status(thm)],[c_42,c_62])).

cnf(c_2815,plain,
    ( v1_relat_1(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2814])).

cnf(c_5568,plain,
    ( r2_hidden(X0,sK7)
    | ~ r2_hidden(k4_tarski(X1,X0),sK9)
    | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) ),
    inference(resolution,[status(thm)],[c_8,c_5215])).

cnf(c_5903,plain,
    ( r2_hidden(X0,sK7)
    | ~ r2_hidden(k4_tarski(X1,X0),sK9) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5604,c_5568])).

cnf(c_16604,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK9,X1))
    | r2_hidden(X0,sK7)
    | ~ v1_relat_1(sK9) ),
    inference(resolution,[status(thm)],[c_5903,c_27])).

cnf(c_16605,plain,
    ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top
    | v1_relat_1(sK9) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16604])).

cnf(c_97538,plain,
    ( r2_hidden(X0,sK7) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_96999,c_2815,c_16605])).

cnf(c_97539,plain,
    ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
    | r2_hidden(X0,sK7) = iProver_top ),
    inference(renaming,[status(thm)],[c_97538])).

cnf(c_97556,plain,
    ( r2_hidden(sK10,sK7) = iProver_top ),
    inference(superposition,[status(thm)],[c_21966,c_97539])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1))
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_1719,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1)) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_6,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1740,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6])).

cnf(c_8455,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(k1_relat_1(X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1719,c_1740])).

cnf(c_93550,plain,
    ( v1_relat_1(sK9) != iProver_top
    | v1_xboole_0(k1_relat_1(sK9)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21966,c_8455])).

cnf(c_9037,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1720,c_1740])).

cnf(c_83129,plain,
    ( v1_relat_1(sK9) != iProver_top
    | v1_xboole_0(sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_21966,c_9037])).

cnf(c_26,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK3(X0,X2,X1),X2)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_1721,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_7078,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_xboole_0(X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1721,c_1740])).

cnf(c_52029,plain,
    ( v1_relat_1(sK9) != iProver_top
    | v1_xboole_0(sK8) != iProver_top ),
    inference(superposition,[status(thm)],[c_21966,c_7078])).

cnf(c_52,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f168])).

cnf(c_33581,plain,
    ( ~ m1_subset_1(sK10,sK7)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | r2_hidden(k4_tarski(sK4(sK8,sK6,sK9,sK10),sK10),sK9)
    | v1_xboole_0(sK7)
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK8) ),
    inference(resolution,[status(thm)],[c_52,c_61])).

cnf(c_1697,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_52])).

cnf(c_3941,plain,
    ( m1_subset_1(sK10,sK7) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | r2_hidden(k4_tarski(sK4(sK8,sK6,sK9,sK10),sK10),sK9) = iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1689,c_1697])).

cnf(c_3969,plain,
    ( ~ m1_subset_1(sK10,sK7)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | r2_hidden(k4_tarski(sK4(sK8,sK6,sK9,sK10),sK10),sK9)
    | v1_xboole_0(sK7)
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_3941])).

cnf(c_37921,plain,
    ( ~ m1_subset_1(sK10,sK7)
    | r2_hidden(k4_tarski(sK4(sK8,sK6,sK9,sK10),sK10),sK9)
    | v1_xboole_0(sK7)
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK8) ),
    inference(global_propositional_subsumption,[status(thm)],[c_33581,c_62,c_3969])).

cnf(c_37949,plain,
    ( ~ m1_subset_1(sK10,sK7)
    | v1_xboole_0(sK7)
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK8)
    | ~ v1_xboole_0(sK9) ),
    inference(resolution,[status(thm)],[c_37921,c_6])).

cnf(c_51,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
    | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
    | r2_hidden(sK4(X4,X3,X2,X0),X4)
    | v1_xboole_0(X1)
    | v1_xboole_0(X3)
    | v1_xboole_0(X4) ),
    inference(cnf_transformation,[],[f169])).

cnf(c_1698,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
    | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
    | r2_hidden(sK4(X4,X3,X2,X0),X4) = iProver_top
    | v1_xboole_0(X1) = iProver_top
    | v1_xboole_0(X3) = iProver_top
    | v1_xboole_0(X4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51])).

cnf(c_4493,plain,
    ( m1_subset_1(sK10,sK7) != iProver_top
    | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
    | r2_hidden(sK4(sK8,sK6,sK9,sK10),sK8) = iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_1689,c_1698])).

cnf(c_4551,plain,
    ( ~ m1_subset_1(sK10,sK7)
    | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
    | r2_hidden(sK4(sK8,sK6,sK9,sK10),sK8)
    | v1_xboole_0(sK7)
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK8) ),
    inference(predicate_to_equality_rev,[status(thm)],[c_4493])).

cnf(c_38,plain,
    ( ~ r2_hidden(k4_tarski(X0,X1),X2)
    | ~ v1_funct_1(X2)
    | ~ v1_relat_1(X2)
    | k1_funct_1(X2,X0) = X1 ),
    inference(cnf_transformation,[],[f155])).

cnf(c_60,negated_conjecture,
    ( ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X0,sK8)
    | k1_funct_1(sK9,X0) != sK10 ),
    inference(cnf_transformation,[],[f181])).

cnf(c_23926,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X0,sK8)
    | ~ r2_hidden(k4_tarski(X0,sK10),sK9)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9) ),
    inference(resolution,[status(thm)],[c_38,c_60])).

cnf(c_63,negated_conjecture,
    ( v1_funct_1(sK9) ),
    inference(cnf_transformation,[],[f178])).

cnf(c_23959,plain,
    ( ~ r2_hidden(X0,sK6)
    | ~ r2_hidden(X0,sK8)
    | ~ r2_hidden(k4_tarski(X0,sK10),sK9) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23926,c_63,c_2814])).

cnf(c_9,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_5577,plain,
    ( r2_hidden(X0,sK6)
    | ~ r2_hidden(k4_tarski(X0,X1),sK9)
    | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) ),
    inference(resolution,[status(thm)],[c_9,c_5215])).

cnf(c_5904,plain,
    ( r2_hidden(X0,sK6)
    | ~ r2_hidden(k4_tarski(X0,X1),sK9) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_5604,c_5577])).

cnf(c_23968,plain,
    ( ~ r2_hidden(X0,sK8)
    | ~ r2_hidden(k4_tarski(X0,sK10),sK9) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_23959,c_5904])).

cnf(c_37962,plain,
    ( ~ m1_subset_1(sK10,sK7)
    | ~ r2_hidden(sK4(sK8,sK6,sK9,sK10),sK8)
    | v1_xboole_0(sK7)
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK8) ),
    inference(resolution,[status(thm)],[c_37921,c_23968])).

cnf(c_37965,plain,
    ( v1_xboole_0(sK8)
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK7)
    | ~ m1_subset_1(sK10,sK7) ),
    inference(global_propositional_subsumption,[status(thm)],[c_37949,c_62,c_4551,c_37962])).

cnf(c_37966,plain,
    ( ~ m1_subset_1(sK10,sK7)
    | v1_xboole_0(sK7)
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK8) ),
    inference(renaming,[status(thm)],[c_37965])).

cnf(c_20,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f137])).

cnf(c_38436,plain,
    ( ~ r2_hidden(sK10,sK7)
    | v1_xboole_0(sK7)
    | v1_xboole_0(sK6)
    | v1_xboole_0(sK8) ),
    inference(resolution,[status(thm)],[c_37966,c_20])).

cnf(c_38437,plain,
    ( r2_hidden(sK10,sK7) != iProver_top
    | v1_xboole_0(sK7) = iProver_top
    | v1_xboole_0(sK6) = iProver_top
    | v1_xboole_0(sK8) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_38436])).

cnf(c_37,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f193])).

cnf(c_23319,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK9))
    | r2_hidden(X0,sK6)
    | ~ v1_funct_1(sK9)
    | ~ v1_relat_1(sK9) ),
    inference(resolution,[status(thm)],[c_37,c_5904])).

cnf(c_24495,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK9))
    | r2_hidden(X0,sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_23319,c_63,c_2814])).

cnf(c_0,plain,
    ( r2_hidden(sK0(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f116])).

cnf(c_24513,plain,
    ( r2_hidden(sK0(k1_relat_1(sK9)),sK6)
    | v1_xboole_0(k1_relat_1(sK9)) ),
    inference(resolution,[status(thm)],[c_24495,c_0])).

cnf(c_26035,plain,
    ( v1_xboole_0(k1_relat_1(sK9))
    | ~ v1_xboole_0(sK6) ),
    inference(resolution,[status(thm)],[c_24513,c_6])).

cnf(c_26036,plain,
    ( v1_xboole_0(k1_relat_1(sK9)) = iProver_top
    | v1_xboole_0(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26035])).

cnf(c_44,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X2)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f161])).

cnf(c_5813,plain,
    ( ~ v1_xboole_0(sK7)
    | v1_xboole_0(sK9) ),
    inference(resolution,[status(thm)],[c_44,c_62])).

cnf(c_5814,plain,
    ( v1_xboole_0(sK7) != iProver_top
    | v1_xboole_0(sK9) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5813])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_97556,c_93550,c_83129,c_52029,c_38437,c_26036,c_5814,c_2815])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 11:08:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.34  % Running in FOF mode
% 39.54/5.47  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.54/5.47  
% 39.54/5.47  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.54/5.47  
% 39.54/5.47  ------  iProver source info
% 39.54/5.47  
% 39.54/5.47  git: date: 2020-06-30 10:37:57 +0100
% 39.54/5.47  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.54/5.47  git: non_committed_changes: false
% 39.54/5.47  git: last_make_outside_of_git: false
% 39.54/5.47  
% 39.54/5.47  ------ 
% 39.54/5.47  
% 39.54/5.47  ------ Input Options
% 39.54/5.47  
% 39.54/5.47  --out_options                           all
% 39.54/5.47  --tptp_safe_out                         true
% 39.54/5.47  --problem_path                          ""
% 39.54/5.47  --include_path                          ""
% 39.54/5.47  --clausifier                            res/vclausify_rel
% 39.54/5.47  --clausifier_options                    --mode clausify
% 39.54/5.47  --stdin                                 false
% 39.54/5.47  --stats_out                             sel
% 39.54/5.47  
% 39.54/5.47  ------ General Options
% 39.54/5.47  
% 39.54/5.47  --fof                                   false
% 39.54/5.47  --time_out_real                         604.99
% 39.54/5.47  --time_out_virtual                      -1.
% 39.54/5.47  --symbol_type_check                     false
% 39.54/5.47  --clausify_out                          false
% 39.54/5.47  --sig_cnt_out                           false
% 39.54/5.47  --trig_cnt_out                          false
% 39.54/5.47  --trig_cnt_out_tolerance                1.
% 39.54/5.47  --trig_cnt_out_sk_spl                   false
% 39.54/5.47  --abstr_cl_out                          false
% 39.54/5.47  
% 39.54/5.47  ------ Global Options
% 39.54/5.47  
% 39.54/5.47  --schedule                              none
% 39.54/5.47  --add_important_lit                     false
% 39.54/5.47  --prop_solver_per_cl                    1000
% 39.54/5.47  --min_unsat_core                        false
% 39.54/5.47  --soft_assumptions                      false
% 39.54/5.47  --soft_lemma_size                       3
% 39.54/5.47  --prop_impl_unit_size                   0
% 39.54/5.47  --prop_impl_unit                        []
% 39.54/5.47  --share_sel_clauses                     true
% 39.54/5.47  --reset_solvers                         false
% 39.54/5.47  --bc_imp_inh                            [conj_cone]
% 39.54/5.47  --conj_cone_tolerance                   3.
% 39.54/5.47  --extra_neg_conj                        none
% 39.54/5.47  --large_theory_mode                     true
% 39.54/5.47  --prolific_symb_bound                   200
% 39.54/5.47  --lt_threshold                          2000
% 39.54/5.47  --clause_weak_htbl                      true
% 39.54/5.47  --gc_record_bc_elim                     false
% 39.54/5.47  
% 39.54/5.47  ------ Preprocessing Options
% 39.54/5.47  
% 39.54/5.47  --preprocessing_flag                    true
% 39.54/5.47  --time_out_prep_mult                    0.1
% 39.54/5.47  --splitting_mode                        input
% 39.54/5.47  --splitting_grd                         true
% 39.54/5.47  --splitting_cvd                         false
% 39.54/5.47  --splitting_cvd_svl                     false
% 39.54/5.47  --splitting_nvd                         32
% 39.54/5.47  --sub_typing                            true
% 39.54/5.47  --prep_gs_sim                           false
% 39.54/5.47  --prep_unflatten                        true
% 39.54/5.47  --prep_res_sim                          true
% 39.54/5.47  --prep_upred                            true
% 39.54/5.47  --prep_sem_filter                       exhaustive
% 39.54/5.47  --prep_sem_filter_out                   false
% 39.54/5.47  --pred_elim                             false
% 39.54/5.47  --res_sim_input                         true
% 39.54/5.47  --eq_ax_congr_red                       true
% 39.54/5.47  --pure_diseq_elim                       true
% 39.54/5.47  --brand_transform                       false
% 39.54/5.47  --non_eq_to_eq                          false
% 39.54/5.47  --prep_def_merge                        true
% 39.54/5.47  --prep_def_merge_prop_impl              false
% 39.54/5.47  --prep_def_merge_mbd                    true
% 39.54/5.47  --prep_def_merge_tr_red                 false
% 39.54/5.47  --prep_def_merge_tr_cl                  false
% 39.54/5.47  --smt_preprocessing                     true
% 39.54/5.47  --smt_ac_axioms                         fast
% 39.54/5.47  --preprocessed_out                      false
% 39.54/5.47  --preprocessed_stats                    false
% 39.54/5.47  
% 39.54/5.47  ------ Abstraction refinement Options
% 39.54/5.47  
% 39.54/5.47  --abstr_ref                             []
% 39.54/5.47  --abstr_ref_prep                        false
% 39.54/5.47  --abstr_ref_until_sat                   false
% 39.54/5.47  --abstr_ref_sig_restrict                funpre
% 39.54/5.47  --abstr_ref_af_restrict_to_split_sk     false
% 39.54/5.47  --abstr_ref_under                       []
% 39.54/5.47  
% 39.54/5.47  ------ SAT Options
% 39.54/5.47  
% 39.54/5.47  --sat_mode                              false
% 39.54/5.47  --sat_fm_restart_options                ""
% 39.54/5.47  --sat_gr_def                            false
% 39.54/5.47  --sat_epr_types                         true
% 39.54/5.47  --sat_non_cyclic_types                  false
% 39.54/5.47  --sat_finite_models                     false
% 39.54/5.47  --sat_fm_lemmas                         false
% 39.54/5.47  --sat_fm_prep                           false
% 39.54/5.47  --sat_fm_uc_incr                        true
% 39.54/5.47  --sat_out_model                         small
% 39.54/5.47  --sat_out_clauses                       false
% 39.54/5.47  
% 39.54/5.47  ------ QBF Options
% 39.54/5.47  
% 39.54/5.47  --qbf_mode                              false
% 39.54/5.47  --qbf_elim_univ                         false
% 39.54/5.47  --qbf_dom_inst                          none
% 39.54/5.47  --qbf_dom_pre_inst                      false
% 39.54/5.47  --qbf_sk_in                             false
% 39.54/5.47  --qbf_pred_elim                         true
% 39.54/5.47  --qbf_split                             512
% 39.54/5.47  
% 39.54/5.47  ------ BMC1 Options
% 39.54/5.47  
% 39.54/5.47  --bmc1_incremental                      false
% 39.54/5.47  --bmc1_axioms                           reachable_all
% 39.54/5.47  --bmc1_min_bound                        0
% 39.54/5.47  --bmc1_max_bound                        -1
% 39.54/5.47  --bmc1_max_bound_default                -1
% 39.54/5.47  --bmc1_symbol_reachability              true
% 39.54/5.47  --bmc1_property_lemmas                  false
% 39.54/5.47  --bmc1_k_induction                      false
% 39.54/5.47  --bmc1_non_equiv_states                 false
% 39.54/5.47  --bmc1_deadlock                         false
% 39.54/5.47  --bmc1_ucm                              false
% 39.54/5.47  --bmc1_add_unsat_core                   none
% 39.54/5.47  --bmc1_unsat_core_children              false
% 39.54/5.47  --bmc1_unsat_core_extrapolate_axioms    false
% 39.54/5.47  --bmc1_out_stat                         full
% 39.54/5.47  --bmc1_ground_init                      false
% 39.54/5.47  --bmc1_pre_inst_next_state              false
% 39.54/5.47  --bmc1_pre_inst_state                   false
% 39.54/5.47  --bmc1_pre_inst_reach_state             false
% 39.54/5.47  --bmc1_out_unsat_core                   false
% 39.54/5.47  --bmc1_aig_witness_out                  false
% 39.54/5.47  --bmc1_verbose                          false
% 39.54/5.47  --bmc1_dump_clauses_tptp                false
% 39.54/5.47  --bmc1_dump_unsat_core_tptp             false
% 39.54/5.47  --bmc1_dump_file                        -
% 39.54/5.47  --bmc1_ucm_expand_uc_limit              128
% 39.54/5.47  --bmc1_ucm_n_expand_iterations          6
% 39.54/5.47  --bmc1_ucm_extend_mode                  1
% 39.54/5.47  --bmc1_ucm_init_mode                    2
% 39.54/5.47  --bmc1_ucm_cone_mode                    none
% 39.54/5.47  --bmc1_ucm_reduced_relation_type        0
% 39.54/5.47  --bmc1_ucm_relax_model                  4
% 39.54/5.47  --bmc1_ucm_full_tr_after_sat            true
% 39.54/5.47  --bmc1_ucm_expand_neg_assumptions       false
% 39.54/5.47  --bmc1_ucm_layered_model                none
% 39.54/5.47  --bmc1_ucm_max_lemma_size               10
% 39.54/5.47  
% 39.54/5.47  ------ AIG Options
% 39.54/5.47  
% 39.54/5.47  --aig_mode                              false
% 39.54/5.47  
% 39.54/5.47  ------ Instantiation Options
% 39.54/5.47  
% 39.54/5.47  --instantiation_flag                    true
% 39.54/5.47  --inst_sos_flag                         false
% 39.54/5.47  --inst_sos_phase                        true
% 39.54/5.47  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.54/5.47  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.54/5.47  --inst_lit_sel_side                     num_symb
% 39.54/5.47  --inst_solver_per_active                1400
% 39.54/5.47  --inst_solver_calls_frac                1.
% 39.54/5.47  --inst_passive_queue_type               priority_queues
% 39.54/5.47  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.54/5.47  --inst_passive_queues_freq              [25;2]
% 39.54/5.47  --inst_dismatching                      true
% 39.54/5.47  --inst_eager_unprocessed_to_passive     true
% 39.54/5.47  --inst_prop_sim_given                   true
% 39.54/5.47  --inst_prop_sim_new                     false
% 39.54/5.47  --inst_subs_new                         false
% 39.54/5.47  --inst_eq_res_simp                      false
% 39.54/5.47  --inst_subs_given                       false
% 39.54/5.47  --inst_orphan_elimination               true
% 39.54/5.47  --inst_learning_loop_flag               true
% 39.54/5.47  --inst_learning_start                   3000
% 39.54/5.47  --inst_learning_factor                  2
% 39.54/5.47  --inst_start_prop_sim_after_learn       3
% 39.54/5.47  --inst_sel_renew                        solver
% 39.54/5.47  --inst_lit_activity_flag                true
% 39.54/5.47  --inst_restr_to_given                   false
% 39.54/5.47  --inst_activity_threshold               500
% 39.54/5.47  --inst_out_proof                        true
% 39.54/5.47  
% 39.54/5.47  ------ Resolution Options
% 39.54/5.47  
% 39.54/5.47  --resolution_flag                       true
% 39.54/5.47  --res_lit_sel                           adaptive
% 39.54/5.47  --res_lit_sel_side                      none
% 39.54/5.47  --res_ordering                          kbo
% 39.54/5.47  --res_to_prop_solver                    active
% 39.54/5.47  --res_prop_simpl_new                    false
% 39.54/5.47  --res_prop_simpl_given                  true
% 39.54/5.47  --res_passive_queue_type                priority_queues
% 39.54/5.47  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.54/5.47  --res_passive_queues_freq               [15;5]
% 39.54/5.47  --res_forward_subs                      full
% 39.54/5.47  --res_backward_subs                     full
% 39.54/5.47  --res_forward_subs_resolution           true
% 39.54/5.47  --res_backward_subs_resolution          true
% 39.54/5.47  --res_orphan_elimination                true
% 39.54/5.47  --res_time_limit                        2.
% 39.54/5.47  --res_out_proof                         true
% 39.54/5.47  
% 39.54/5.47  ------ Superposition Options
% 39.54/5.47  
% 39.54/5.47  --superposition_flag                    true
% 39.54/5.47  --sup_passive_queue_type                priority_queues
% 39.54/5.47  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.54/5.47  --sup_passive_queues_freq               [1;4]
% 39.54/5.47  --demod_completeness_check              fast
% 39.54/5.47  --demod_use_ground                      true
% 39.54/5.47  --sup_to_prop_solver                    passive
% 39.54/5.47  --sup_prop_simpl_new                    true
% 39.54/5.47  --sup_prop_simpl_given                  true
% 39.54/5.47  --sup_fun_splitting                     false
% 39.54/5.47  --sup_smt_interval                      50000
% 39.54/5.47  
% 39.54/5.47  ------ Superposition Simplification Setup
% 39.54/5.47  
% 39.54/5.47  --sup_indices_passive                   []
% 39.54/5.47  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.54/5.47  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.54/5.47  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.54/5.47  --sup_full_triv                         [TrivRules;PropSubs]
% 39.54/5.47  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.54/5.47  --sup_full_bw                           [BwDemod]
% 39.54/5.47  --sup_immed_triv                        [TrivRules]
% 39.54/5.47  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.54/5.47  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.54/5.47  --sup_immed_bw_main                     []
% 39.54/5.47  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.54/5.47  --sup_input_triv                        [Unflattening;TrivRules]
% 39.54/5.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.54/5.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.54/5.48  
% 39.54/5.48  ------ Combination Options
% 39.54/5.48  
% 39.54/5.48  --comb_res_mult                         3
% 39.54/5.48  --comb_sup_mult                         2
% 39.54/5.48  --comb_inst_mult                        10
% 39.54/5.48  
% 39.54/5.48  ------ Debug Options
% 39.54/5.48  
% 39.54/5.48  --dbg_backtrace                         false
% 39.54/5.48  --dbg_dump_prop_clauses                 false
% 39.54/5.48  --dbg_dump_prop_clauses_file            -
% 39.54/5.48  --dbg_out_stat                          false
% 39.54/5.48  ------ Parsing...
% 39.54/5.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.54/5.48  
% 39.54/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 1 0s  sf_e 
% 39.54/5.48  
% 39.54/5.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.54/5.48  
% 39.54/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.54/5.48  ------ Proving...
% 39.54/5.48  ------ Problem Properties 
% 39.54/5.48  
% 39.54/5.48  
% 39.54/5.48  clauses                                 62
% 39.54/5.48  conjectures                             4
% 39.54/5.48  EPR                                     8
% 39.54/5.48  Horn                                    53
% 39.54/5.48  unary                                   20
% 39.54/5.48  binary                                  14
% 39.54/5.48  lits                                    160
% 39.54/5.48  lits eq                                 20
% 39.54/5.48  fd_pure                                 0
% 39.54/5.48  fd_pseudo                               0
% 39.54/5.48  fd_cond                                 3
% 39.54/5.48  fd_pseudo_cond                          1
% 39.54/5.48  AC symbols                              0
% 39.54/5.48  
% 39.54/5.48  ------ Input Options Time Limit: Unbounded
% 39.54/5.48  
% 39.54/5.48  
% 39.54/5.48  ------ 
% 39.54/5.48  Current options:
% 39.54/5.48  ------ 
% 39.54/5.48  
% 39.54/5.48  ------ Input Options
% 39.54/5.48  
% 39.54/5.48  --out_options                           all
% 39.54/5.48  --tptp_safe_out                         true
% 39.54/5.48  --problem_path                          ""
% 39.54/5.48  --include_path                          ""
% 39.54/5.48  --clausifier                            res/vclausify_rel
% 39.54/5.48  --clausifier_options                    --mode clausify
% 39.54/5.48  --stdin                                 false
% 39.54/5.48  --stats_out                             sel
% 39.54/5.48  
% 39.54/5.48  ------ General Options
% 39.54/5.48  
% 39.54/5.48  --fof                                   false
% 39.54/5.48  --time_out_real                         604.99
% 39.54/5.48  --time_out_virtual                      -1.
% 39.54/5.48  --symbol_type_check                     false
% 39.54/5.48  --clausify_out                          false
% 39.54/5.48  --sig_cnt_out                           false
% 39.54/5.48  --trig_cnt_out                          false
% 39.54/5.48  --trig_cnt_out_tolerance                1.
% 39.54/5.48  --trig_cnt_out_sk_spl                   false
% 39.54/5.48  --abstr_cl_out                          false
% 39.54/5.48  
% 39.54/5.48  ------ Global Options
% 39.54/5.48  
% 39.54/5.48  --schedule                              none
% 39.54/5.48  --add_important_lit                     false
% 39.54/5.48  --prop_solver_per_cl                    1000
% 39.54/5.48  --min_unsat_core                        false
% 39.54/5.48  --soft_assumptions                      false
% 39.54/5.48  --soft_lemma_size                       3
% 39.54/5.48  --prop_impl_unit_size                   0
% 39.54/5.48  --prop_impl_unit                        []
% 39.54/5.48  --share_sel_clauses                     true
% 39.54/5.48  --reset_solvers                         false
% 39.54/5.48  --bc_imp_inh                            [conj_cone]
% 39.54/5.48  --conj_cone_tolerance                   3.
% 39.54/5.48  --extra_neg_conj                        none
% 39.54/5.48  --large_theory_mode                     true
% 39.54/5.48  --prolific_symb_bound                   200
% 39.54/5.48  --lt_threshold                          2000
% 39.54/5.48  --clause_weak_htbl                      true
% 39.54/5.48  --gc_record_bc_elim                     false
% 39.54/5.48  
% 39.54/5.48  ------ Preprocessing Options
% 39.54/5.48  
% 39.54/5.48  --preprocessing_flag                    true
% 39.54/5.48  --time_out_prep_mult                    0.1
% 39.54/5.48  --splitting_mode                        input
% 39.54/5.48  --splitting_grd                         true
% 39.54/5.48  --splitting_cvd                         false
% 39.54/5.48  --splitting_cvd_svl                     false
% 39.54/5.48  --splitting_nvd                         32
% 39.54/5.48  --sub_typing                            true
% 39.54/5.48  --prep_gs_sim                           false
% 39.54/5.48  --prep_unflatten                        true
% 39.54/5.48  --prep_res_sim                          true
% 39.54/5.48  --prep_upred                            true
% 39.54/5.48  --prep_sem_filter                       exhaustive
% 39.54/5.48  --prep_sem_filter_out                   false
% 39.54/5.48  --pred_elim                             false
% 39.54/5.48  --res_sim_input                         true
% 39.54/5.48  --eq_ax_congr_red                       true
% 39.54/5.48  --pure_diseq_elim                       true
% 39.54/5.48  --brand_transform                       false
% 39.54/5.48  --non_eq_to_eq                          false
% 39.54/5.48  --prep_def_merge                        true
% 39.54/5.48  --prep_def_merge_prop_impl              false
% 39.54/5.48  --prep_def_merge_mbd                    true
% 39.54/5.48  --prep_def_merge_tr_red                 false
% 39.54/5.48  --prep_def_merge_tr_cl                  false
% 39.54/5.48  --smt_preprocessing                     true
% 39.54/5.48  --smt_ac_axioms                         fast
% 39.54/5.48  --preprocessed_out                      false
% 39.54/5.48  --preprocessed_stats                    false
% 39.54/5.48  
% 39.54/5.48  ------ Abstraction refinement Options
% 39.54/5.48  
% 39.54/5.48  --abstr_ref                             []
% 39.54/5.48  --abstr_ref_prep                        false
% 39.54/5.48  --abstr_ref_until_sat                   false
% 39.54/5.48  --abstr_ref_sig_restrict                funpre
% 39.54/5.48  --abstr_ref_af_restrict_to_split_sk     false
% 39.54/5.48  --abstr_ref_under                       []
% 39.54/5.48  
% 39.54/5.48  ------ SAT Options
% 39.54/5.48  
% 39.54/5.48  --sat_mode                              false
% 39.54/5.48  --sat_fm_restart_options                ""
% 39.54/5.48  --sat_gr_def                            false
% 39.54/5.48  --sat_epr_types                         true
% 39.54/5.48  --sat_non_cyclic_types                  false
% 39.54/5.48  --sat_finite_models                     false
% 39.54/5.48  --sat_fm_lemmas                         false
% 39.54/5.48  --sat_fm_prep                           false
% 39.54/5.48  --sat_fm_uc_incr                        true
% 39.54/5.48  --sat_out_model                         small
% 39.54/5.48  --sat_out_clauses                       false
% 39.54/5.48  
% 39.54/5.48  ------ QBF Options
% 39.54/5.48  
% 39.54/5.48  --qbf_mode                              false
% 39.54/5.48  --qbf_elim_univ                         false
% 39.54/5.48  --qbf_dom_inst                          none
% 39.54/5.48  --qbf_dom_pre_inst                      false
% 39.54/5.48  --qbf_sk_in                             false
% 39.54/5.48  --qbf_pred_elim                         true
% 39.54/5.48  --qbf_split                             512
% 39.54/5.48  
% 39.54/5.48  ------ BMC1 Options
% 39.54/5.48  
% 39.54/5.48  --bmc1_incremental                      false
% 39.54/5.48  --bmc1_axioms                           reachable_all
% 39.54/5.48  --bmc1_min_bound                        0
% 39.54/5.48  --bmc1_max_bound                        -1
% 39.54/5.48  --bmc1_max_bound_default                -1
% 39.54/5.48  --bmc1_symbol_reachability              true
% 39.54/5.48  --bmc1_property_lemmas                  false
% 39.54/5.48  --bmc1_k_induction                      false
% 39.54/5.48  --bmc1_non_equiv_states                 false
% 39.54/5.48  --bmc1_deadlock                         false
% 39.54/5.48  --bmc1_ucm                              false
% 39.54/5.48  --bmc1_add_unsat_core                   none
% 39.54/5.48  --bmc1_unsat_core_children              false
% 39.54/5.48  --bmc1_unsat_core_extrapolate_axioms    false
% 39.54/5.48  --bmc1_out_stat                         full
% 39.54/5.48  --bmc1_ground_init                      false
% 39.54/5.48  --bmc1_pre_inst_next_state              false
% 39.54/5.48  --bmc1_pre_inst_state                   false
% 39.54/5.48  --bmc1_pre_inst_reach_state             false
% 39.54/5.48  --bmc1_out_unsat_core                   false
% 39.54/5.48  --bmc1_aig_witness_out                  false
% 39.54/5.48  --bmc1_verbose                          false
% 39.54/5.48  --bmc1_dump_clauses_tptp                false
% 39.54/5.48  --bmc1_dump_unsat_core_tptp             false
% 39.54/5.48  --bmc1_dump_file                        -
% 39.54/5.48  --bmc1_ucm_expand_uc_limit              128
% 39.54/5.48  --bmc1_ucm_n_expand_iterations          6
% 39.54/5.48  --bmc1_ucm_extend_mode                  1
% 39.54/5.48  --bmc1_ucm_init_mode                    2
% 39.54/5.48  --bmc1_ucm_cone_mode                    none
% 39.54/5.48  --bmc1_ucm_reduced_relation_type        0
% 39.54/5.48  --bmc1_ucm_relax_model                  4
% 39.54/5.48  --bmc1_ucm_full_tr_after_sat            true
% 39.54/5.48  --bmc1_ucm_expand_neg_assumptions       false
% 39.54/5.48  --bmc1_ucm_layered_model                none
% 39.54/5.48  --bmc1_ucm_max_lemma_size               10
% 39.54/5.48  
% 39.54/5.48  ------ AIG Options
% 39.54/5.48  
% 39.54/5.48  --aig_mode                              false
% 39.54/5.48  
% 39.54/5.48  ------ Instantiation Options
% 39.54/5.48  
% 39.54/5.48  --instantiation_flag                    true
% 39.54/5.48  --inst_sos_flag                         false
% 39.54/5.48  --inst_sos_phase                        true
% 39.54/5.48  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 39.54/5.48  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 39.54/5.48  --inst_lit_sel_side                     num_symb
% 39.54/5.48  --inst_solver_per_active                1400
% 39.54/5.48  --inst_solver_calls_frac                1.
% 39.54/5.48  --inst_passive_queue_type               priority_queues
% 39.54/5.48  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 39.54/5.48  --inst_passive_queues_freq              [25;2]
% 39.54/5.48  --inst_dismatching                      true
% 39.54/5.48  --inst_eager_unprocessed_to_passive     true
% 39.54/5.48  --inst_prop_sim_given                   true
% 39.54/5.48  --inst_prop_sim_new                     false
% 39.54/5.48  --inst_subs_new                         false
% 39.54/5.48  --inst_eq_res_simp                      false
% 39.54/5.48  --inst_subs_given                       false
% 39.54/5.48  --inst_orphan_elimination               true
% 39.54/5.48  --inst_learning_loop_flag               true
% 39.54/5.48  --inst_learning_start                   3000
% 39.54/5.48  --inst_learning_factor                  2
% 39.54/5.48  --inst_start_prop_sim_after_learn       3
% 39.54/5.48  --inst_sel_renew                        solver
% 39.54/5.48  --inst_lit_activity_flag                true
% 39.54/5.48  --inst_restr_to_given                   false
% 39.54/5.48  --inst_activity_threshold               500
% 39.54/5.48  --inst_out_proof                        true
% 39.54/5.48  
% 39.54/5.48  ------ Resolution Options
% 39.54/5.48  
% 39.54/5.48  --resolution_flag                       true
% 39.54/5.48  --res_lit_sel                           adaptive
% 39.54/5.48  --res_lit_sel_side                      none
% 39.54/5.48  --res_ordering                          kbo
% 39.54/5.48  --res_to_prop_solver                    active
% 39.54/5.48  --res_prop_simpl_new                    false
% 39.54/5.48  --res_prop_simpl_given                  true
% 39.54/5.48  --res_passive_queue_type                priority_queues
% 39.54/5.48  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 39.54/5.48  --res_passive_queues_freq               [15;5]
% 39.54/5.48  --res_forward_subs                      full
% 39.54/5.48  --res_backward_subs                     full
% 39.54/5.48  --res_forward_subs_resolution           true
% 39.54/5.48  --res_backward_subs_resolution          true
% 39.54/5.48  --res_orphan_elimination                true
% 39.54/5.48  --res_time_limit                        2.
% 39.54/5.48  --res_out_proof                         true
% 39.54/5.48  
% 39.54/5.48  ------ Superposition Options
% 39.54/5.48  
% 39.54/5.48  --superposition_flag                    true
% 39.54/5.48  --sup_passive_queue_type                priority_queues
% 39.54/5.48  --sup_passive_queues                    [[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 39.54/5.48  --sup_passive_queues_freq               [1;4]
% 39.54/5.48  --demod_completeness_check              fast
% 39.54/5.48  --demod_use_ground                      true
% 39.54/5.48  --sup_to_prop_solver                    passive
% 39.54/5.48  --sup_prop_simpl_new                    true
% 39.54/5.48  --sup_prop_simpl_given                  true
% 39.54/5.48  --sup_fun_splitting                     false
% 39.54/5.48  --sup_smt_interval                      50000
% 39.54/5.48  
% 39.54/5.48  ------ Superposition Simplification Setup
% 39.54/5.48  
% 39.54/5.48  --sup_indices_passive                   []
% 39.54/5.48  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.54/5.48  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.54/5.48  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 39.54/5.48  --sup_full_triv                         [TrivRules;PropSubs]
% 39.54/5.48  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.54/5.48  --sup_full_bw                           [BwDemod]
% 39.54/5.48  --sup_immed_triv                        [TrivRules]
% 39.54/5.48  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 39.54/5.48  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.54/5.48  --sup_immed_bw_main                     []
% 39.54/5.48  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.54/5.48  --sup_input_triv                        [Unflattening;TrivRules]
% 39.54/5.48  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 39.54/5.48  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 39.54/5.48  
% 39.54/5.48  ------ Combination Options
% 39.54/5.48  
% 39.54/5.48  --comb_res_mult                         3
% 39.54/5.48  --comb_sup_mult                         2
% 39.54/5.48  --comb_inst_mult                        10
% 39.54/5.48  
% 39.54/5.48  ------ Debug Options
% 39.54/5.48  
% 39.54/5.48  --dbg_backtrace                         false
% 39.54/5.48  --dbg_dump_prop_clauses                 false
% 39.54/5.48  --dbg_dump_prop_clauses_file            -
% 39.54/5.48  --dbg_out_stat                          false
% 39.54/5.48  
% 39.54/5.48  
% 39.54/5.48  
% 39.54/5.48  
% 39.54/5.48  ------ Proving...
% 39.54/5.48  
% 39.54/5.48  
% 39.54/5.48  % SZS status Theorem for theBenchmark.p
% 39.54/5.48  
% 39.54/5.48  % SZS output start CNFRefutation for theBenchmark.p
% 39.54/5.48  
% 39.54/5.48  fof(f40,conjecture,(
% 39.54/5.48    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f41,negated_conjecture,(
% 39.54/5.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 39.54/5.48    inference(negated_conjecture,[],[f40])).
% 39.54/5.48  
% 39.54/5.48  fof(f44,plain,(
% 39.54/5.48    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 39.54/5.48    inference(pure_predicate_removal,[],[f41])).
% 39.54/5.48  
% 39.54/5.48  fof(f84,plain,(
% 39.54/5.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)))),
% 39.54/5.48    inference(ennf_transformation,[],[f44])).
% 39.54/5.48  
% 39.54/5.48  fof(f85,plain,(
% 39.54/5.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))),
% 39.54/5.48    inference(flattening,[],[f84])).
% 39.54/5.48  
% 39.54/5.48  fof(f113,plain,(
% 39.54/5.48    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK10 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK10,k7_relset_1(X0,X1,X3,X2)))) )),
% 39.54/5.48    introduced(choice_axiom,[])).
% 39.54/5.48  
% 39.54/5.48  fof(f112,plain,(
% 39.54/5.48    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK9,X5) != X4 | ~r2_hidden(X5,sK8) | ~r2_hidden(X5,sK6)) & r2_hidden(X4,k7_relset_1(sK6,sK7,sK9,sK8))) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK9))),
% 39.54/5.48    introduced(choice_axiom,[])).
% 39.54/5.48  
% 39.54/5.48  fof(f114,plain,(
% 39.54/5.48    (! [X5] : (k1_funct_1(sK9,X5) != sK10 | ~r2_hidden(X5,sK8) | ~r2_hidden(X5,sK6)) & r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))) & m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) & v1_funct_1(sK9)),
% 39.54/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK6,sK7,sK8,sK9,sK10])],[f85,f113,f112])).
% 39.54/5.48  
% 39.54/5.48  fof(f179,plain,(
% 39.54/5.48    m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))),
% 39.54/5.48    inference(cnf_transformation,[],[f114])).
% 39.54/5.48  
% 39.54/5.48  fof(f33,axiom,(
% 39.54/5.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f78,plain,(
% 39.54/5.48    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.54/5.48    inference(ennf_transformation,[],[f33])).
% 39.54/5.48  
% 39.54/5.48  fof(f163,plain,(
% 39.54/5.48    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.54/5.48    inference(cnf_transformation,[],[f78])).
% 39.54/5.48  
% 39.54/5.48  fof(f180,plain,(
% 39.54/5.48    r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8))),
% 39.54/5.48    inference(cnf_transformation,[],[f114])).
% 39.54/5.48  
% 39.54/5.48  fof(f19,axiom,(
% 39.54/5.48    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f61,plain,(
% 39.54/5.48    ! [X0,X1,X2] : ((r2_hidden(X0,k9_relat_1(X2,X1)) <=> ? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2)))) | ~v1_relat_1(X2))),
% 39.54/5.48    inference(ennf_transformation,[],[f19])).
% 39.54/5.48  
% 39.54/5.48  fof(f99,plain,(
% 39.54/5.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(k4_tarski(X3,X0),X2) & r2_hidden(X3,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 39.54/5.48    inference(nnf_transformation,[],[f61])).
% 39.54/5.48  
% 39.54/5.48  fof(f100,plain,(
% 39.54/5.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 39.54/5.48    inference(rectify,[],[f99])).
% 39.54/5.48  
% 39.54/5.48  fof(f101,plain,(
% 39.54/5.48    ! [X2,X1,X0] : (? [X4] : (r2_hidden(X4,X1) & r2_hidden(k4_tarski(X4,X0),X2) & r2_hidden(X4,k1_relat_1(X2))) => (r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))))),
% 39.54/5.48    introduced(choice_axiom,[])).
% 39.54/5.48  
% 39.54/5.48  fof(f102,plain,(
% 39.54/5.48    ! [X0,X1,X2] : (((r2_hidden(X0,k9_relat_1(X2,X1)) | ! [X3] : (~r2_hidden(X3,X1) | ~r2_hidden(k4_tarski(X3,X0),X2) | ~r2_hidden(X3,k1_relat_1(X2)))) & ((r2_hidden(sK3(X0,X1,X2),X1) & r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) & r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2))) | ~r2_hidden(X0,k9_relat_1(X2,X1)))) | ~v1_relat_1(X2))),
% 39.54/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3])],[f100,f101])).
% 39.54/5.48  
% 39.54/5.48  fof(f143,plain,(
% 39.54/5.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(sK3(X0,X1,X2),X0),X2) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f102])).
% 39.54/5.48  
% 39.54/5.48  fof(f16,axiom,(
% 39.54/5.48    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f56,plain,(
% 39.54/5.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 39.54/5.48    inference(ennf_transformation,[],[f16])).
% 39.54/5.48  
% 39.54/5.48  fof(f57,plain,(
% 39.54/5.48    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 39.54/5.48    inference(flattening,[],[f56])).
% 39.54/5.48  
% 39.54/5.48  fof(f139,plain,(
% 39.54/5.48    ( ! [X2,X0,X1] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f57])).
% 39.54/5.48  
% 39.54/5.48  fof(f15,axiom,(
% 39.54/5.48    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f54,plain,(
% 39.54/5.48    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 39.54/5.48    inference(ennf_transformation,[],[f15])).
% 39.54/5.48  
% 39.54/5.48  fof(f55,plain,(
% 39.54/5.48    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 39.54/5.48    inference(flattening,[],[f54])).
% 39.54/5.48  
% 39.54/5.48  fof(f138,plain,(
% 39.54/5.48    ( ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f55])).
% 39.54/5.48  
% 39.54/5.48  fof(f17,axiom,(
% 39.54/5.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f58,plain,(
% 39.54/5.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 39.54/5.48    inference(ennf_transformation,[],[f17])).
% 39.54/5.48  
% 39.54/5.48  fof(f140,plain,(
% 39.54/5.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f58])).
% 39.54/5.48  
% 39.54/5.48  fof(f5,axiom,(
% 39.54/5.48    ! [X0,X1,X2,X3] : (r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) <=> (r2_hidden(X1,X3) & r2_hidden(X0,X2)))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f92,plain,(
% 39.54/5.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | (~r2_hidden(X1,X3) | ~r2_hidden(X0,X2))) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 39.54/5.48    inference(nnf_transformation,[],[f5])).
% 39.54/5.48  
% 39.54/5.48  fof(f93,plain,(
% 39.54/5.48    ! [X0,X1,X2,X3] : ((r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3)) | ~r2_hidden(X1,X3) | ~r2_hidden(X0,X2)) & ((r2_hidden(X1,X3) & r2_hidden(X0,X2)) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))))),
% 39.54/5.48    inference(flattening,[],[f92])).
% 39.54/5.48  
% 39.54/5.48  fof(f123,plain,(
% 39.54/5.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X1,X3) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 39.54/5.48    inference(cnf_transformation,[],[f93])).
% 39.54/5.48  
% 39.54/5.48  fof(f29,axiom,(
% 39.54/5.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f74,plain,(
% 39.54/5.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.54/5.48    inference(ennf_transformation,[],[f29])).
% 39.54/5.48  
% 39.54/5.48  fof(f159,plain,(
% 39.54/5.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.54/5.48    inference(cnf_transformation,[],[f74])).
% 39.54/5.48  
% 39.54/5.48  fof(f142,plain,(
% 39.54/5.48    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),k1_relat_1(X2)) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f102])).
% 39.54/5.48  
% 39.54/5.48  fof(f4,axiom,(
% 39.54/5.48    ! [X0,X1] : ~(v1_xboole_0(X1) & r2_hidden(X0,X1))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f51,plain,(
% 39.54/5.48    ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1))),
% 39.54/5.48    inference(ennf_transformation,[],[f4])).
% 39.54/5.48  
% 39.54/5.48  fof(f121,plain,(
% 39.54/5.48    ( ! [X0,X1] : (~v1_xboole_0(X1) | ~r2_hidden(X0,X1)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f51])).
% 39.54/5.48  
% 39.54/5.48  fof(f144,plain,(
% 39.54/5.48    ( ! [X2,X0,X1] : (r2_hidden(sK3(X0,X1,X2),X1) | ~r2_hidden(X0,k9_relat_1(X2,X1)) | ~v1_relat_1(X2)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f102])).
% 39.54/5.48  
% 39.54/5.48  fof(f36,axiom,(
% 39.54/5.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : (~v1_xboole_0(X2) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) => ! [X4] : (m1_subset_1(X4,X0) => (r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))))))))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f81,plain,(
% 39.54/5.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : ((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) <=> ? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 39.54/5.48    inference(ennf_transformation,[],[f36])).
% 39.54/5.48  
% 39.54/5.48  fof(f106,plain,(
% 39.54/5.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X5] : (r2_hidden(X5,X1) & r2_hidden(k4_tarski(X5,X4),X3) & m1_subset_1(X5,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 39.54/5.48    inference(nnf_transformation,[],[f81])).
% 39.54/5.48  
% 39.54/5.48  fof(f107,plain,(
% 39.54/5.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 39.54/5.48    inference(rectify,[],[f106])).
% 39.54/5.48  
% 39.54/5.48  fof(f108,plain,(
% 39.54/5.48    ! [X4,X3,X2,X1] : (? [X6] : (r2_hidden(X6,X1) & r2_hidden(k4_tarski(X6,X4),X3) & m1_subset_1(X6,X2)) => (r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)))),
% 39.54/5.48    introduced(choice_axiom,[])).
% 39.54/5.48  
% 39.54/5.48  fof(f109,plain,(
% 39.54/5.48    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (((r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ! [X5] : (~r2_hidden(X5,X1) | ~r2_hidden(k4_tarski(X5,X4),X3) | ~m1_subset_1(X5,X2))) & ((r2_hidden(sK4(X1,X2,X3,X4),X1) & r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) & m1_subset_1(sK4(X1,X2,X3,X4),X2)) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)))) | ~m1_subset_1(X4,X0)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 39.54/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f107,f108])).
% 39.54/5.48  
% 39.54/5.48  fof(f168,plain,(
% 39.54/5.48    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(k4_tarski(sK4(X1,X2,X3,X4),X4),X3) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f109])).
% 39.54/5.48  
% 39.54/5.48  fof(f169,plain,(
% 39.54/5.48    ( ! [X4,X2,X0,X3,X1] : (r2_hidden(sK4(X1,X2,X3,X4),X1) | ~r2_hidden(X4,k7_relset_1(X2,X0,X3,X1)) | ~m1_subset_1(X4,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f109])).
% 39.54/5.48  
% 39.54/5.48  fof(f27,axiom,(
% 39.54/5.48    ! [X0,X1,X2] : ((v1_funct_1(X2) & v1_relat_1(X2)) => (r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f72,plain,(
% 39.54/5.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | (~v1_funct_1(X2) | ~v1_relat_1(X2)))),
% 39.54/5.48    inference(ennf_transformation,[],[f27])).
% 39.54/5.48  
% 39.54/5.48  fof(f73,plain,(
% 39.54/5.48    ! [X0,X1,X2] : ((r2_hidden(k4_tarski(X0,X1),X2) <=> (k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2)))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 39.54/5.48    inference(flattening,[],[f72])).
% 39.54/5.48  
% 39.54/5.48  fof(f103,plain,(
% 39.54/5.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | (k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 39.54/5.48    inference(nnf_transformation,[],[f73])).
% 39.54/5.48  
% 39.54/5.48  fof(f104,plain,(
% 39.54/5.48    ! [X0,X1,X2] : (((r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2))) & ((k1_funct_1(X2,X0) = X1 & r2_hidden(X0,k1_relat_1(X2))) | ~r2_hidden(k4_tarski(X0,X1),X2))) | ~v1_funct_1(X2) | ~v1_relat_1(X2))),
% 39.54/5.48    inference(flattening,[],[f103])).
% 39.54/5.48  
% 39.54/5.48  fof(f155,plain,(
% 39.54/5.48    ( ! [X2,X0,X1] : (k1_funct_1(X2,X0) = X1 | ~r2_hidden(k4_tarski(X0,X1),X2) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f104])).
% 39.54/5.48  
% 39.54/5.48  fof(f181,plain,(
% 39.54/5.48    ( ! [X5] : (k1_funct_1(sK9,X5) != sK10 | ~r2_hidden(X5,sK8) | ~r2_hidden(X5,sK6)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f114])).
% 39.54/5.48  
% 39.54/5.48  fof(f178,plain,(
% 39.54/5.48    v1_funct_1(sK9)),
% 39.54/5.48    inference(cnf_transformation,[],[f114])).
% 39.54/5.48  
% 39.54/5.48  fof(f122,plain,(
% 39.54/5.48    ( ! [X2,X0,X3,X1] : (r2_hidden(X0,X2) | ~r2_hidden(k4_tarski(X0,X1),k2_zfmisc_1(X2,X3))) )),
% 39.54/5.48    inference(cnf_transformation,[],[f93])).
% 39.54/5.48  
% 39.54/5.48  fof(f14,axiom,(
% 39.54/5.48    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f53,plain,(
% 39.54/5.48    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 39.54/5.48    inference(ennf_transformation,[],[f14])).
% 39.54/5.48  
% 39.54/5.48  fof(f137,plain,(
% 39.54/5.48    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f53])).
% 39.54/5.48  
% 39.54/5.48  fof(f156,plain,(
% 39.54/5.48    ( ! [X2,X0,X1] : (r2_hidden(k4_tarski(X0,X1),X2) | k1_funct_1(X2,X0) != X1 | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f104])).
% 39.54/5.48  
% 39.54/5.48  fof(f193,plain,(
% 39.54/5.48    ( ! [X2,X0] : (r2_hidden(k4_tarski(X0,k1_funct_1(X2,X0)),X2) | ~r2_hidden(X0,k1_relat_1(X2)) | ~v1_funct_1(X2) | ~v1_relat_1(X2)) )),
% 39.54/5.48    inference(equality_resolution,[],[f156])).
% 39.54/5.48  
% 39.54/5.48  fof(f1,axiom,(
% 39.54/5.48    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f86,plain,(
% 39.54/5.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 39.54/5.48    inference(nnf_transformation,[],[f1])).
% 39.54/5.48  
% 39.54/5.48  fof(f87,plain,(
% 39.54/5.48    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 39.54/5.48    inference(rectify,[],[f86])).
% 39.54/5.48  
% 39.54/5.48  fof(f88,plain,(
% 39.54/5.48    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 39.54/5.48    introduced(choice_axiom,[])).
% 39.54/5.48  
% 39.54/5.48  fof(f89,plain,(
% 39.54/5.48    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 39.54/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f87,f88])).
% 39.54/5.48  
% 39.54/5.48  fof(f116,plain,(
% 39.54/5.48    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f89])).
% 39.54/5.48  
% 39.54/5.48  fof(f31,axiom,(
% 39.54/5.48    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => v1_xboole_0(X2)))),
% 39.54/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.54/5.48  
% 39.54/5.48  fof(f76,plain,(
% 39.54/5.48    ! [X0,X1] : (! [X2] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) | ~v1_xboole_0(X0))),
% 39.54/5.48    inference(ennf_transformation,[],[f31])).
% 39.54/5.48  
% 39.54/5.48  fof(f161,plain,(
% 39.54/5.48    ( ! [X2,X0,X1] : (v1_xboole_0(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_xboole_0(X0)) )),
% 39.54/5.48    inference(cnf_transformation,[],[f76])).
% 39.54/5.48  
% 39.54/5.48  cnf(c_62,negated_conjecture,
% 39.54/5.48      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) ),
% 39.54/5.48      inference(cnf_transformation,[],[f179]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_1688,plain,
% 39.54/5.48      ( m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) = iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_62]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_46,plain,
% 39.54/5.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.54/5.48      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 39.54/5.48      inference(cnf_transformation,[],[f163]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_1703,plain,
% 39.54/5.48      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 39.54/5.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_46]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_5861,plain,
% 39.54/5.48      ( k7_relset_1(sK6,sK7,sK9,X0) = k9_relat_1(sK9,X0) ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_1688,c_1703]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_61,negated_conjecture,
% 39.54/5.48      ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) ),
% 39.54/5.48      inference(cnf_transformation,[],[f180]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_1689,plain,
% 39.54/5.48      ( r2_hidden(sK10,k7_relset_1(sK6,sK7,sK9,sK8)) = iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_61]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_21966,plain,
% 39.54/5.48      ( r2_hidden(sK10,k9_relat_1(sK9,sK8)) = iProver_top ),
% 39.54/5.48      inference(demodulation,[status(thm)],[c_5861,c_1689]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_27,plain,
% 39.54/5.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 39.54/5.48      | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1)
% 39.54/5.48      | ~ v1_relat_1(X1) ),
% 39.54/5.48      inference(cnf_transformation,[],[f143]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_1720,plain,
% 39.54/5.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 39.54/5.48      | r2_hidden(k4_tarski(sK3(X0,X2,X1),X0),X1) = iProver_top
% 39.54/5.48      | v1_relat_1(X1) != iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_22,plain,
% 39.54/5.48      ( m1_subset_1(X0,X1)
% 39.54/5.48      | ~ m1_subset_1(X2,k1_zfmisc_1(X1))
% 39.54/5.48      | ~ r2_hidden(X0,X2) ),
% 39.54/5.48      inference(cnf_transformation,[],[f139]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_1725,plain,
% 39.54/5.48      ( m1_subset_1(X0,X1) = iProver_top
% 39.54/5.48      | m1_subset_1(X2,k1_zfmisc_1(X1)) != iProver_top
% 39.54/5.48      | r2_hidden(X0,X2) != iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_6810,plain,
% 39.54/5.48      ( m1_subset_1(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top
% 39.54/5.48      | r2_hidden(X0,sK9) != iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_1688,c_1725]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_21,plain,
% 39.54/5.48      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 39.54/5.48      inference(cnf_transformation,[],[f138]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_1726,plain,
% 39.54/5.48      ( m1_subset_1(X0,X1) != iProver_top
% 39.54/5.48      | r2_hidden(X0,X1) = iProver_top
% 39.54/5.48      | v1_xboole_0(X1) = iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_33398,plain,
% 39.54/5.48      ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top
% 39.54/5.48      | r2_hidden(X0,sK9) != iProver_top
% 39.54/5.48      | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) = iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_6810,c_1726]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_23,plain,
% 39.54/5.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.54/5.48      | ~ r2_hidden(X2,X0)
% 39.54/5.48      | ~ v1_xboole_0(X1) ),
% 39.54/5.48      inference(cnf_transformation,[],[f140]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_5604,plain,
% 39.54/5.48      ( ~ r2_hidden(X0,sK9) | ~ v1_xboole_0(k2_zfmisc_1(sK6,sK7)) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_23,c_62]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_5205,plain,
% 39.54/5.48      ( m1_subset_1(X0,k2_zfmisc_1(sK6,sK7)) | ~ r2_hidden(X0,sK9) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_22,c_62]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_5215,plain,
% 39.54/5.48      ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7))
% 39.54/5.48      | ~ r2_hidden(X0,sK9)
% 39.54/5.48      | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_5205,c_21]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_5905,plain,
% 39.54/5.48      ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) | ~ r2_hidden(X0,sK9) ),
% 39.54/5.48      inference(backward_subsumption_resolution,
% 39.54/5.48                [status(thm)],
% 39.54/5.48                [c_5604,c_5215]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_5908,plain,
% 39.54/5.48      ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top
% 39.54/5.48      | r2_hidden(X0,sK9) != iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_5905]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_95878,plain,
% 39.54/5.48      ( r2_hidden(X0,sK9) != iProver_top
% 39.54/5.48      | r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top ),
% 39.54/5.48      inference(global_propositional_subsumption,
% 39.54/5.48                [status(thm)],
% 39.54/5.48                [c_33398,c_5908]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_95879,plain,
% 39.54/5.48      ( r2_hidden(X0,k2_zfmisc_1(sK6,sK7)) = iProver_top
% 39.54/5.48      | r2_hidden(X0,sK9) != iProver_top ),
% 39.54/5.48      inference(renaming,[status(thm)],[c_95878]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_8,plain,
% 39.54/5.48      ( r2_hidden(X0,X1)
% 39.54/5.48      | ~ r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) ),
% 39.54/5.48      inference(cnf_transformation,[],[f123]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_1734,plain,
% 39.54/5.48      ( r2_hidden(X0,X1) = iProver_top
% 39.54/5.48      | r2_hidden(k4_tarski(X2,X0),k2_zfmisc_1(X3,X1)) != iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_95888,plain,
% 39.54/5.48      ( r2_hidden(X0,sK7) = iProver_top
% 39.54/5.48      | r2_hidden(k4_tarski(X1,X0),sK9) != iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_95879,c_1734]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_96999,plain,
% 39.54/5.48      ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 39.54/5.48      | r2_hidden(X0,sK7) = iProver_top
% 39.54/5.48      | v1_relat_1(sK9) != iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_1720,c_95888]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_42,plain,
% 39.54/5.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.54/5.48      | v1_relat_1(X0) ),
% 39.54/5.48      inference(cnf_transformation,[],[f159]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_2814,plain,
% 39.54/5.48      ( v1_relat_1(sK9) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_42,c_62]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_2815,plain,
% 39.54/5.48      ( v1_relat_1(sK9) = iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_2814]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_5568,plain,
% 39.54/5.48      ( r2_hidden(X0,sK7)
% 39.54/5.48      | ~ r2_hidden(k4_tarski(X1,X0),sK9)
% 39.54/5.48      | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_8,c_5215]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_5903,plain,
% 39.54/5.48      ( r2_hidden(X0,sK7) | ~ r2_hidden(k4_tarski(X1,X0),sK9) ),
% 39.54/5.48      inference(backward_subsumption_resolution,
% 39.54/5.48                [status(thm)],
% 39.54/5.48                [c_5604,c_5568]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_16604,plain,
% 39.54/5.48      ( ~ r2_hidden(X0,k9_relat_1(sK9,X1))
% 39.54/5.48      | r2_hidden(X0,sK7)
% 39.54/5.48      | ~ v1_relat_1(sK9) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_5903,c_27]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_16605,plain,
% 39.54/5.48      ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 39.54/5.48      | r2_hidden(X0,sK7) = iProver_top
% 39.54/5.48      | v1_relat_1(sK9) != iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_16604]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_97538,plain,
% 39.54/5.48      ( r2_hidden(X0,sK7) = iProver_top
% 39.54/5.48      | r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top ),
% 39.54/5.48      inference(global_propositional_subsumption,
% 39.54/5.48                [status(thm)],
% 39.54/5.48                [c_96999,c_2815,c_16605]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_97539,plain,
% 39.54/5.48      ( r2_hidden(X0,k9_relat_1(sK9,X1)) != iProver_top
% 39.54/5.48      | r2_hidden(X0,sK7) = iProver_top ),
% 39.54/5.48      inference(renaming,[status(thm)],[c_97538]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_97556,plain,
% 39.54/5.48      ( r2_hidden(sK10,sK7) = iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_21966,c_97539]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_28,plain,
% 39.54/5.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 39.54/5.48      | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1))
% 39.54/5.48      | ~ v1_relat_1(X1) ),
% 39.54/5.48      inference(cnf_transformation,[],[f142]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_1719,plain,
% 39.54/5.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 39.54/5.48      | r2_hidden(sK3(X0,X2,X1),k1_relat_1(X1)) = iProver_top
% 39.54/5.48      | v1_relat_1(X1) != iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_6,plain,
% 39.54/5.48      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 39.54/5.48      inference(cnf_transformation,[],[f121]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_1740,plain,
% 39.54/5.48      ( r2_hidden(X0,X1) != iProver_top
% 39.54/5.48      | v1_xboole_0(X1) != iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_6]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_8455,plain,
% 39.54/5.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 39.54/5.48      | v1_relat_1(X1) != iProver_top
% 39.54/5.48      | v1_xboole_0(k1_relat_1(X1)) != iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_1719,c_1740]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_93550,plain,
% 39.54/5.48      ( v1_relat_1(sK9) != iProver_top
% 39.54/5.48      | v1_xboole_0(k1_relat_1(sK9)) != iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_21966,c_8455]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_9037,plain,
% 39.54/5.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 39.54/5.48      | v1_relat_1(X1) != iProver_top
% 39.54/5.48      | v1_xboole_0(X1) != iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_1720,c_1740]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_83129,plain,
% 39.54/5.48      ( v1_relat_1(sK9) != iProver_top
% 39.54/5.48      | v1_xboole_0(sK9) != iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_21966,c_9037]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_26,plain,
% 39.54/5.48      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 39.54/5.48      | r2_hidden(sK3(X0,X2,X1),X2)
% 39.54/5.48      | ~ v1_relat_1(X1) ),
% 39.54/5.48      inference(cnf_transformation,[],[f144]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_1721,plain,
% 39.54/5.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 39.54/5.48      | r2_hidden(sK3(X0,X2,X1),X2) = iProver_top
% 39.54/5.48      | v1_relat_1(X1) != iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_7078,plain,
% 39.54/5.48      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 39.54/5.48      | v1_relat_1(X1) != iProver_top
% 39.54/5.48      | v1_xboole_0(X2) != iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_1721,c_1740]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_52029,plain,
% 39.54/5.48      ( v1_relat_1(sK9) != iProver_top
% 39.54/5.48      | v1_xboole_0(sK8) != iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_21966,c_7078]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_52,plain,
% 39.54/5.48      ( ~ m1_subset_1(X0,X1)
% 39.54/5.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 39.54/5.48      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 39.54/5.48      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2)
% 39.54/5.48      | v1_xboole_0(X1)
% 39.54/5.48      | v1_xboole_0(X3)
% 39.54/5.48      | v1_xboole_0(X4) ),
% 39.54/5.48      inference(cnf_transformation,[],[f168]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_33581,plain,
% 39.54/5.48      ( ~ m1_subset_1(sK10,sK7)
% 39.54/5.48      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 39.54/5.48      | r2_hidden(k4_tarski(sK4(sK8,sK6,sK9,sK10),sK10),sK9)
% 39.54/5.48      | v1_xboole_0(sK7)
% 39.54/5.48      | v1_xboole_0(sK6)
% 39.54/5.48      | v1_xboole_0(sK8) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_52,c_61]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_1697,plain,
% 39.54/5.48      ( m1_subset_1(X0,X1) != iProver_top
% 39.54/5.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 39.54/5.48      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 39.54/5.48      | r2_hidden(k4_tarski(sK4(X4,X3,X2,X0),X0),X2) = iProver_top
% 39.54/5.48      | v1_xboole_0(X1) = iProver_top
% 39.54/5.48      | v1_xboole_0(X3) = iProver_top
% 39.54/5.48      | v1_xboole_0(X4) = iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_52]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_3941,plain,
% 39.54/5.48      ( m1_subset_1(sK10,sK7) != iProver_top
% 39.54/5.48      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 39.54/5.48      | r2_hidden(k4_tarski(sK4(sK8,sK6,sK9,sK10),sK10),sK9) = iProver_top
% 39.54/5.48      | v1_xboole_0(sK7) = iProver_top
% 39.54/5.48      | v1_xboole_0(sK6) = iProver_top
% 39.54/5.48      | v1_xboole_0(sK8) = iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_1689,c_1697]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_3969,plain,
% 39.54/5.48      ( ~ m1_subset_1(sK10,sK7)
% 39.54/5.48      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 39.54/5.48      | r2_hidden(k4_tarski(sK4(sK8,sK6,sK9,sK10),sK10),sK9)
% 39.54/5.48      | v1_xboole_0(sK7)
% 39.54/5.48      | v1_xboole_0(sK6)
% 39.54/5.48      | v1_xboole_0(sK8) ),
% 39.54/5.48      inference(predicate_to_equality_rev,[status(thm)],[c_3941]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_37921,plain,
% 39.54/5.48      ( ~ m1_subset_1(sK10,sK7)
% 39.54/5.48      | r2_hidden(k4_tarski(sK4(sK8,sK6,sK9,sK10),sK10),sK9)
% 39.54/5.48      | v1_xboole_0(sK7)
% 39.54/5.48      | v1_xboole_0(sK6)
% 39.54/5.48      | v1_xboole_0(sK8) ),
% 39.54/5.48      inference(global_propositional_subsumption,
% 39.54/5.48                [status(thm)],
% 39.54/5.48                [c_33581,c_62,c_3969]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_37949,plain,
% 39.54/5.48      ( ~ m1_subset_1(sK10,sK7)
% 39.54/5.48      | v1_xboole_0(sK7)
% 39.54/5.48      | v1_xboole_0(sK6)
% 39.54/5.48      | v1_xboole_0(sK8)
% 39.54/5.48      | ~ v1_xboole_0(sK9) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_37921,c_6]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_51,plain,
% 39.54/5.48      ( ~ m1_subset_1(X0,X1)
% 39.54/5.48      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
% 39.54/5.48      | ~ r2_hidden(X0,k7_relset_1(X3,X1,X2,X4))
% 39.54/5.48      | r2_hidden(sK4(X4,X3,X2,X0),X4)
% 39.54/5.48      | v1_xboole_0(X1)
% 39.54/5.48      | v1_xboole_0(X3)
% 39.54/5.48      | v1_xboole_0(X4) ),
% 39.54/5.48      inference(cnf_transformation,[],[f169]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_1698,plain,
% 39.54/5.48      ( m1_subset_1(X0,X1) != iProver_top
% 39.54/5.48      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) != iProver_top
% 39.54/5.48      | r2_hidden(X0,k7_relset_1(X3,X1,X2,X4)) != iProver_top
% 39.54/5.48      | r2_hidden(sK4(X4,X3,X2,X0),X4) = iProver_top
% 39.54/5.48      | v1_xboole_0(X1) = iProver_top
% 39.54/5.48      | v1_xboole_0(X3) = iProver_top
% 39.54/5.48      | v1_xboole_0(X4) = iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_51]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_4493,plain,
% 39.54/5.48      ( m1_subset_1(sK10,sK7) != iProver_top
% 39.54/5.48      | m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7))) != iProver_top
% 39.54/5.48      | r2_hidden(sK4(sK8,sK6,sK9,sK10),sK8) = iProver_top
% 39.54/5.48      | v1_xboole_0(sK7) = iProver_top
% 39.54/5.48      | v1_xboole_0(sK6) = iProver_top
% 39.54/5.48      | v1_xboole_0(sK8) = iProver_top ),
% 39.54/5.48      inference(superposition,[status(thm)],[c_1689,c_1698]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_4551,plain,
% 39.54/5.48      ( ~ m1_subset_1(sK10,sK7)
% 39.54/5.48      | ~ m1_subset_1(sK9,k1_zfmisc_1(k2_zfmisc_1(sK6,sK7)))
% 39.54/5.48      | r2_hidden(sK4(sK8,sK6,sK9,sK10),sK8)
% 39.54/5.48      | v1_xboole_0(sK7)
% 39.54/5.48      | v1_xboole_0(sK6)
% 39.54/5.48      | v1_xboole_0(sK8) ),
% 39.54/5.48      inference(predicate_to_equality_rev,[status(thm)],[c_4493]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_38,plain,
% 39.54/5.48      ( ~ r2_hidden(k4_tarski(X0,X1),X2)
% 39.54/5.48      | ~ v1_funct_1(X2)
% 39.54/5.48      | ~ v1_relat_1(X2)
% 39.54/5.48      | k1_funct_1(X2,X0) = X1 ),
% 39.54/5.48      inference(cnf_transformation,[],[f155]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_60,negated_conjecture,
% 39.54/5.48      ( ~ r2_hidden(X0,sK6)
% 39.54/5.48      | ~ r2_hidden(X0,sK8)
% 39.54/5.48      | k1_funct_1(sK9,X0) != sK10 ),
% 39.54/5.48      inference(cnf_transformation,[],[f181]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_23926,plain,
% 39.54/5.48      ( ~ r2_hidden(X0,sK6)
% 39.54/5.48      | ~ r2_hidden(X0,sK8)
% 39.54/5.48      | ~ r2_hidden(k4_tarski(X0,sK10),sK9)
% 39.54/5.48      | ~ v1_funct_1(sK9)
% 39.54/5.48      | ~ v1_relat_1(sK9) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_38,c_60]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_63,negated_conjecture,
% 39.54/5.48      ( v1_funct_1(sK9) ),
% 39.54/5.48      inference(cnf_transformation,[],[f178]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_23959,plain,
% 39.54/5.48      ( ~ r2_hidden(X0,sK6)
% 39.54/5.48      | ~ r2_hidden(X0,sK8)
% 39.54/5.48      | ~ r2_hidden(k4_tarski(X0,sK10),sK9) ),
% 39.54/5.48      inference(global_propositional_subsumption,
% 39.54/5.48                [status(thm)],
% 39.54/5.48                [c_23926,c_63,c_2814]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_9,plain,
% 39.54/5.48      ( r2_hidden(X0,X1)
% 39.54/5.48      | ~ r2_hidden(k4_tarski(X0,X2),k2_zfmisc_1(X1,X3)) ),
% 39.54/5.48      inference(cnf_transformation,[],[f122]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_5577,plain,
% 39.54/5.48      ( r2_hidden(X0,sK6)
% 39.54/5.48      | ~ r2_hidden(k4_tarski(X0,X1),sK9)
% 39.54/5.48      | v1_xboole_0(k2_zfmisc_1(sK6,sK7)) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_9,c_5215]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_5904,plain,
% 39.54/5.48      ( r2_hidden(X0,sK6) | ~ r2_hidden(k4_tarski(X0,X1),sK9) ),
% 39.54/5.48      inference(backward_subsumption_resolution,
% 39.54/5.48                [status(thm)],
% 39.54/5.48                [c_5604,c_5577]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_23968,plain,
% 39.54/5.48      ( ~ r2_hidden(X0,sK8) | ~ r2_hidden(k4_tarski(X0,sK10),sK9) ),
% 39.54/5.48      inference(forward_subsumption_resolution,
% 39.54/5.48                [status(thm)],
% 39.54/5.48                [c_23959,c_5904]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_37962,plain,
% 39.54/5.48      ( ~ m1_subset_1(sK10,sK7)
% 39.54/5.48      | ~ r2_hidden(sK4(sK8,sK6,sK9,sK10),sK8)
% 39.54/5.48      | v1_xboole_0(sK7)
% 39.54/5.48      | v1_xboole_0(sK6)
% 39.54/5.48      | v1_xboole_0(sK8) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_37921,c_23968]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_37965,plain,
% 39.54/5.48      ( v1_xboole_0(sK8)
% 39.54/5.48      | v1_xboole_0(sK6)
% 39.54/5.48      | v1_xboole_0(sK7)
% 39.54/5.48      | ~ m1_subset_1(sK10,sK7) ),
% 39.54/5.48      inference(global_propositional_subsumption,
% 39.54/5.48                [status(thm)],
% 39.54/5.48                [c_37949,c_62,c_4551,c_37962]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_37966,plain,
% 39.54/5.48      ( ~ m1_subset_1(sK10,sK7)
% 39.54/5.48      | v1_xboole_0(sK7)
% 39.54/5.48      | v1_xboole_0(sK6)
% 39.54/5.48      | v1_xboole_0(sK8) ),
% 39.54/5.48      inference(renaming,[status(thm)],[c_37965]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_20,plain,
% 39.54/5.48      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 39.54/5.48      inference(cnf_transformation,[],[f137]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_38436,plain,
% 39.54/5.48      ( ~ r2_hidden(sK10,sK7)
% 39.54/5.48      | v1_xboole_0(sK7)
% 39.54/5.48      | v1_xboole_0(sK6)
% 39.54/5.48      | v1_xboole_0(sK8) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_37966,c_20]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_38437,plain,
% 39.54/5.48      ( r2_hidden(sK10,sK7) != iProver_top
% 39.54/5.48      | v1_xboole_0(sK7) = iProver_top
% 39.54/5.48      | v1_xboole_0(sK6) = iProver_top
% 39.54/5.48      | v1_xboole_0(sK8) = iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_38436]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_37,plain,
% 39.54/5.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 39.54/5.48      | r2_hidden(k4_tarski(X0,k1_funct_1(X1,X0)),X1)
% 39.54/5.48      | ~ v1_funct_1(X1)
% 39.54/5.48      | ~ v1_relat_1(X1) ),
% 39.54/5.48      inference(cnf_transformation,[],[f193]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_23319,plain,
% 39.54/5.48      ( ~ r2_hidden(X0,k1_relat_1(sK9))
% 39.54/5.48      | r2_hidden(X0,sK6)
% 39.54/5.48      | ~ v1_funct_1(sK9)
% 39.54/5.48      | ~ v1_relat_1(sK9) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_37,c_5904]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_24495,plain,
% 39.54/5.48      ( ~ r2_hidden(X0,k1_relat_1(sK9)) | r2_hidden(X0,sK6) ),
% 39.54/5.48      inference(global_propositional_subsumption,
% 39.54/5.48                [status(thm)],
% 39.54/5.48                [c_23319,c_63,c_2814]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_0,plain,
% 39.54/5.48      ( r2_hidden(sK0(X0),X0) | v1_xboole_0(X0) ),
% 39.54/5.48      inference(cnf_transformation,[],[f116]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_24513,plain,
% 39.54/5.48      ( r2_hidden(sK0(k1_relat_1(sK9)),sK6)
% 39.54/5.48      | v1_xboole_0(k1_relat_1(sK9)) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_24495,c_0]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_26035,plain,
% 39.54/5.48      ( v1_xboole_0(k1_relat_1(sK9)) | ~ v1_xboole_0(sK6) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_24513,c_6]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_26036,plain,
% 39.54/5.48      ( v1_xboole_0(k1_relat_1(sK9)) = iProver_top
% 39.54/5.48      | v1_xboole_0(sK6) != iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_26035]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_44,plain,
% 39.54/5.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.54/5.48      | ~ v1_xboole_0(X2)
% 39.54/5.48      | v1_xboole_0(X0) ),
% 39.54/5.48      inference(cnf_transformation,[],[f161]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_5813,plain,
% 39.54/5.48      ( ~ v1_xboole_0(sK7) | v1_xboole_0(sK9) ),
% 39.54/5.48      inference(resolution,[status(thm)],[c_44,c_62]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(c_5814,plain,
% 39.54/5.48      ( v1_xboole_0(sK7) != iProver_top
% 39.54/5.48      | v1_xboole_0(sK9) = iProver_top ),
% 39.54/5.48      inference(predicate_to_equality,[status(thm)],[c_5813]) ).
% 39.54/5.48  
% 39.54/5.48  cnf(contradiction,plain,
% 39.54/5.48      ( $false ),
% 39.54/5.48      inference(minisat,
% 39.54/5.48                [status(thm)],
% 39.54/5.48                [c_97556,c_93550,c_83129,c_52029,c_38437,c_26036,c_5814,
% 39.54/5.48                 c_2815]) ).
% 39.54/5.48  
% 39.54/5.48  
% 39.54/5.48  % SZS output end CNFRefutation for theBenchmark.p
% 39.54/5.48  
% 39.54/5.48  ------                               Statistics
% 39.54/5.48  
% 39.54/5.48  ------ Selected
% 39.54/5.48  
% 39.54/5.48  total_time:                             4.842
% 39.54/5.48  
%------------------------------------------------------------------------------
