%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:07:56 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 385 expanded)
%              Number of clauses        :   77 ( 130 expanded)
%              Number of leaves         :   19 (  99 expanded)
%              Depth                    :   19
%              Number of atoms          :  470 (2149 expanded)
%              Number of equality atoms :  187 ( 522 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f16])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f5])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

fof(f23,plain,(
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
    inference(nnf_transformation,[],[f15])).

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
    inference(rectify,[],[f23])).

fof(f27,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
        & r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f26,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) = X3
        & r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
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
              ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
              | ~ r2_hidden(X4,X1)
              | ~ r2_hidden(X4,k1_relat_1(X0)) )
          | ~ r2_hidden(sK0(X0,X1,X2),X2) )
        & ( ? [X5] :
              ( k1_funct_1(X0,X5) = sK0(X0,X1,X2)
              & r2_hidden(X5,X1)
              & r2_hidden(X5,k1_relat_1(X0)) )
          | r2_hidden(sK0(X0,X1,X2),X2) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1,X2] :
          ( ( k9_relat_1(X0,X1) = X2
            | ( ( ! [X4] :
                    ( k1_funct_1(X0,X4) != sK0(X0,X1,X2)
                    | ~ r2_hidden(X4,X1)
                    | ~ r2_hidden(X4,k1_relat_1(X0)) )
                | ~ r2_hidden(sK0(X0,X1,X2),X2) )
              & ( ( k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2)
                  & r2_hidden(sK1(X0,X1,X2),X1)
                  & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) )
                | r2_hidden(sK0(X0,X1,X2),X2) ) ) )
          & ( ! [X6] :
                ( ( r2_hidden(X6,X2)
                  | ! [X7] :
                      ( k1_funct_1(X0,X7) != X6
                      | ~ r2_hidden(X7,X1)
                      | ~ r2_hidden(X7,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
                    & r2_hidden(sK2(X0,X1,X6),X1)
                    & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) )
                  | ~ r2_hidden(X6,X2) ) )
            | k9_relat_1(X0,X1) != X2 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).

fof(f38,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f62,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f38])).

fof(f10,conjecture,(
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

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f21,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f21])).

fof(f31,plain,(
    ! [X2,X0,X3,X1] :
      ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(X3,X5) != X4
              | ~ r2_hidden(X5,X2)
              | ~ r2_hidden(X5,X0) )
          & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
     => ( ! [X5] :
            ( k1_funct_1(X3,X5) != sK7
            | ~ r2_hidden(X5,X2)
            | ~ r2_hidden(X5,X0) )
        & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X0,X1,X2,X3] :
        ( ? [X4] :
            ( ! [X5] :
                ( k1_funct_1(X3,X5) != X4
                | ~ r2_hidden(X5,X2)
                | ~ r2_hidden(X5,X0) )
            & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2)) )
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ? [X4] :
          ( ! [X5] :
              ( k1_funct_1(sK6,X5) != X4
              | ~ r2_hidden(X5,sK5)
              | ~ r2_hidden(X5,sK3) )
          & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5)) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ! [X5] :
        ( k1_funct_1(sK6,X5) != sK7
        | ~ r2_hidden(X5,sK5)
        | ~ r2_hidden(X5,sK3) )
    & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f22,f31,f30])).

fof(f54,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f32])).

fof(f56,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f32])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f35,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f36,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f9,axiom,(
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
    inference(ennf_transformation,[],[f9])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f29,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f55,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f32])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f37,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f63,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f37])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f57,plain,(
    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f32])).

fof(f39,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f61,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f39])).

fof(f58,plain,(
    ! [X5] :
      ( k1_funct_1(sK6,X5) != sK7
      | ~ r2_hidden(X5,sK5)
      | ~ r2_hidden(X5,sK3) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f12])).

cnf(c_12,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_4017,plain,
    ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,X0),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_6492,plain,
    ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_4017])).

cnf(c_10,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_25,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_417,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_25])).

cnf(c_418,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(sK2(sK6,X1,X0),X1)
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_417])).

cnf(c_1025,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_28,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_419,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_418])).

cnf(c_2,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f35])).

cnf(c_1088,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
    | ~ v1_relat_1(X0)
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1132,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1088])).

cnf(c_1176,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1132])).

cnf(c_1177,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1176])).

cnf(c_3,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1184,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1185,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1184])).

cnf(c_1224,plain,
    ( r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1025,c_28,c_419,c_1177,c_1185])).

cnf(c_1225,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_1224])).

cnf(c_20,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f48])).

cnf(c_24,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_531,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK4 != X2
    | sK3 != X1
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_20,c_24])).

cnf(c_532,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_531])).

cnf(c_534,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_532,c_23])).

cnf(c_1033,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_13,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1037,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_1373,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1033,c_1037])).

cnf(c_1400,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_534,c_1373])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_402,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_25])).

cnf(c_403,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_402])).

cnf(c_1026,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_404,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_403])).

cnf(c_1235,plain,
    ( r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1026,c_28,c_404,c_1177,c_1185])).

cnf(c_1236,plain,
    ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_1235])).

cnf(c_1690,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
    | r2_hidden(sK2(sK6,X1,X0),sK3) = iProver_top ),
    inference(superposition,[status(thm)],[c_1400,c_1236])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1036,plain,
    ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_1398,plain,
    ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
    inference(superposition,[status(thm)],[c_1033,c_1036])).

cnf(c_22,negated_conjecture,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1034,plain,
    ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1493,plain,
    ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1398,c_1034])).

cnf(c_9,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f61])).

cnf(c_432,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_25])).

cnf(c_433,plain,
    ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,X1,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_432])).

cnf(c_1024,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0,X1)) = X1
    | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_433])).

cnf(c_1496,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5,sK7)) = sK7
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1493,c_1024])).

cnf(c_1994,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5,sK7)) = sK7 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1496,c_28,c_1177,c_1185])).

cnf(c_21,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,X0) != sK7 ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1035,plain,
    ( k1_funct_1(sK6,X0) != sK7
    | r2_hidden(X0,sK3) != iProver_top
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1997,plain,
    ( r2_hidden(sK2(sK6,sK5,sK7),sK3) != iProver_top
    | r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1994,c_1035])).

cnf(c_3801,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1690,c_1997])).

cnf(c_4029,plain,
    ( r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3801,c_1493])).

cnf(c_4030,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top ),
    inference(renaming,[status(thm)],[c_4029])).

cnf(c_4033,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1225,c_4030])).

cnf(c_690,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_3395,plain,
    ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK4)
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_690])).

cnf(c_691,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1109,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k1_xboole_0))
    | k7_relset_1(sK3,sK4,sK6,sK5) != X0
    | k1_zfmisc_1(k1_xboole_0) != X1 ),
    inference(instantiation,[status(thm)],[c_691])).

cnf(c_1149,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k1_xboole_0))
    | k7_relset_1(sK3,sK4,sK6,sK5) != X0
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X1) ),
    inference(instantiation,[status(thm)],[c_1109])).

cnf(c_1216,plain,
    ( ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(X0))
    | m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k1_xboole_0))
    | k7_relset_1(sK3,sK4,sK6,sK5) != k7_relset_1(sK3,sK4,sK6,sK5)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X0) ),
    inference(instantiation,[status(thm)],[c_1149])).

cnf(c_1891,plain,
    ( ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4))
    | m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k1_xboole_0))
    | k7_relset_1(sK3,sK4,sK6,sK5) != k7_relset_1(sK3,sK4,sK6,sK5)
    | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK4) ),
    inference(instantiation,[status(thm)],[c_1216])).

cnf(c_688,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1391,plain,
    ( k7_relset_1(sK3,sK4,sK6,sK5) = k7_relset_1(sK3,sK4,sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(c_689,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1243,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_689])).

cnf(c_1244,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1243])).

cnf(c_0,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f33])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | ~ v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f34])).

cnf(c_291,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
    | k1_xboole_0 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_1])).

cnf(c_292,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(unflattening,[status(thm)],[c_291])).

cnf(c_1073,plain,
    ( ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
    | ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_292])).

cnf(c_717,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_688])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_6492,c_4033,c_3395,c_1891,c_1493,c_1391,c_1244,c_1073,c_717,c_22,c_23])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.33  % Computer   : n014.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:57:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 3.15/1.03  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.03  
% 3.15/1.03  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.15/1.03  
% 3.15/1.03  ------  iProver source info
% 3.15/1.03  
% 3.15/1.03  git: date: 2020-06-30 10:37:57 +0100
% 3.15/1.03  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.15/1.03  git: non_committed_changes: false
% 3.15/1.03  git: last_make_outside_of_git: false
% 3.15/1.03  
% 3.15/1.03  ------ 
% 3.15/1.03  
% 3.15/1.03  ------ Input Options
% 3.15/1.03  
% 3.15/1.03  --out_options                           all
% 3.15/1.03  --tptp_safe_out                         true
% 3.15/1.03  --problem_path                          ""
% 3.15/1.03  --include_path                          ""
% 3.15/1.03  --clausifier                            res/vclausify_rel
% 3.15/1.03  --clausifier_options                    ""
% 3.15/1.03  --stdin                                 false
% 3.15/1.03  --stats_out                             all
% 3.15/1.03  
% 3.15/1.03  ------ General Options
% 3.15/1.03  
% 3.15/1.03  --fof                                   false
% 3.15/1.03  --time_out_real                         305.
% 3.15/1.03  --time_out_virtual                      -1.
% 3.15/1.03  --symbol_type_check                     false
% 3.15/1.03  --clausify_out                          false
% 3.15/1.03  --sig_cnt_out                           false
% 3.15/1.03  --trig_cnt_out                          false
% 3.15/1.03  --trig_cnt_out_tolerance                1.
% 3.15/1.03  --trig_cnt_out_sk_spl                   false
% 3.15/1.03  --abstr_cl_out                          false
% 3.15/1.03  
% 3.15/1.03  ------ Global Options
% 3.15/1.03  
% 3.15/1.03  --schedule                              default
% 3.15/1.03  --add_important_lit                     false
% 3.15/1.03  --prop_solver_per_cl                    1000
% 3.15/1.03  --min_unsat_core                        false
% 3.15/1.03  --soft_assumptions                      false
% 3.15/1.03  --soft_lemma_size                       3
% 3.15/1.03  --prop_impl_unit_size                   0
% 3.15/1.03  --prop_impl_unit                        []
% 3.15/1.03  --share_sel_clauses                     true
% 3.15/1.03  --reset_solvers                         false
% 3.15/1.03  --bc_imp_inh                            [conj_cone]
% 3.15/1.03  --conj_cone_tolerance                   3.
% 3.15/1.03  --extra_neg_conj                        none
% 3.15/1.03  --large_theory_mode                     true
% 3.15/1.03  --prolific_symb_bound                   200
% 3.15/1.03  --lt_threshold                          2000
% 3.15/1.03  --clause_weak_htbl                      true
% 3.15/1.03  --gc_record_bc_elim                     false
% 3.15/1.03  
% 3.15/1.03  ------ Preprocessing Options
% 3.15/1.03  
% 3.15/1.03  --preprocessing_flag                    true
% 3.15/1.03  --time_out_prep_mult                    0.1
% 3.15/1.03  --splitting_mode                        input
% 3.15/1.03  --splitting_grd                         true
% 3.15/1.03  --splitting_cvd                         false
% 3.15/1.03  --splitting_cvd_svl                     false
% 3.15/1.03  --splitting_nvd                         32
% 3.15/1.03  --sub_typing                            true
% 3.15/1.03  --prep_gs_sim                           true
% 3.15/1.03  --prep_unflatten                        true
% 3.15/1.03  --prep_res_sim                          true
% 3.15/1.03  --prep_upred                            true
% 3.15/1.03  --prep_sem_filter                       exhaustive
% 3.15/1.03  --prep_sem_filter_out                   false
% 3.15/1.03  --pred_elim                             true
% 3.15/1.03  --res_sim_input                         true
% 3.15/1.03  --eq_ax_congr_red                       true
% 3.15/1.03  --pure_diseq_elim                       true
% 3.15/1.03  --brand_transform                       false
% 3.15/1.03  --non_eq_to_eq                          false
% 3.15/1.03  --prep_def_merge                        true
% 3.15/1.03  --prep_def_merge_prop_impl              false
% 3.15/1.03  --prep_def_merge_mbd                    true
% 3.15/1.03  --prep_def_merge_tr_red                 false
% 3.15/1.03  --prep_def_merge_tr_cl                  false
% 3.15/1.03  --smt_preprocessing                     true
% 3.15/1.03  --smt_ac_axioms                         fast
% 3.15/1.03  --preprocessed_out                      false
% 3.15/1.03  --preprocessed_stats                    false
% 3.15/1.03  
% 3.15/1.03  ------ Abstraction refinement Options
% 3.15/1.03  
% 3.15/1.03  --abstr_ref                             []
% 3.15/1.03  --abstr_ref_prep                        false
% 3.15/1.03  --abstr_ref_until_sat                   false
% 3.15/1.03  --abstr_ref_sig_restrict                funpre
% 3.15/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.15/1.03  --abstr_ref_under                       []
% 3.15/1.03  
% 3.15/1.03  ------ SAT Options
% 3.15/1.03  
% 3.15/1.03  --sat_mode                              false
% 3.15/1.03  --sat_fm_restart_options                ""
% 3.15/1.03  --sat_gr_def                            false
% 3.15/1.03  --sat_epr_types                         true
% 3.15/1.03  --sat_non_cyclic_types                  false
% 3.15/1.03  --sat_finite_models                     false
% 3.15/1.03  --sat_fm_lemmas                         false
% 3.15/1.03  --sat_fm_prep                           false
% 3.15/1.03  --sat_fm_uc_incr                        true
% 3.15/1.03  --sat_out_model                         small
% 3.15/1.03  --sat_out_clauses                       false
% 3.15/1.03  
% 3.15/1.03  ------ QBF Options
% 3.15/1.03  
% 3.15/1.03  --qbf_mode                              false
% 3.15/1.03  --qbf_elim_univ                         false
% 3.15/1.03  --qbf_dom_inst                          none
% 3.15/1.03  --qbf_dom_pre_inst                      false
% 3.15/1.03  --qbf_sk_in                             false
% 3.15/1.03  --qbf_pred_elim                         true
% 3.15/1.03  --qbf_split                             512
% 3.15/1.03  
% 3.15/1.03  ------ BMC1 Options
% 3.15/1.03  
% 3.15/1.03  --bmc1_incremental                      false
% 3.15/1.03  --bmc1_axioms                           reachable_all
% 3.15/1.03  --bmc1_min_bound                        0
% 3.15/1.03  --bmc1_max_bound                        -1
% 3.15/1.03  --bmc1_max_bound_default                -1
% 3.15/1.03  --bmc1_symbol_reachability              true
% 3.15/1.03  --bmc1_property_lemmas                  false
% 3.15/1.03  --bmc1_k_induction                      false
% 3.15/1.03  --bmc1_non_equiv_states                 false
% 3.15/1.03  --bmc1_deadlock                         false
% 3.15/1.03  --bmc1_ucm                              false
% 3.15/1.03  --bmc1_add_unsat_core                   none
% 3.15/1.03  --bmc1_unsat_core_children              false
% 3.15/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.15/1.03  --bmc1_out_stat                         full
% 3.15/1.03  --bmc1_ground_init                      false
% 3.15/1.03  --bmc1_pre_inst_next_state              false
% 3.15/1.03  --bmc1_pre_inst_state                   false
% 3.15/1.03  --bmc1_pre_inst_reach_state             false
% 3.15/1.03  --bmc1_out_unsat_core                   false
% 3.15/1.03  --bmc1_aig_witness_out                  false
% 3.15/1.03  --bmc1_verbose                          false
% 3.15/1.03  --bmc1_dump_clauses_tptp                false
% 3.15/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.15/1.03  --bmc1_dump_file                        -
% 3.15/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.15/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.15/1.03  --bmc1_ucm_extend_mode                  1
% 3.15/1.03  --bmc1_ucm_init_mode                    2
% 3.15/1.03  --bmc1_ucm_cone_mode                    none
% 3.15/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.15/1.03  --bmc1_ucm_relax_model                  4
% 3.15/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.15/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.15/1.03  --bmc1_ucm_layered_model                none
% 3.15/1.03  --bmc1_ucm_max_lemma_size               10
% 3.15/1.03  
% 3.15/1.03  ------ AIG Options
% 3.15/1.03  
% 3.15/1.03  --aig_mode                              false
% 3.15/1.03  
% 3.15/1.03  ------ Instantiation Options
% 3.15/1.03  
% 3.15/1.03  --instantiation_flag                    true
% 3.15/1.03  --inst_sos_flag                         true
% 3.15/1.03  --inst_sos_phase                        true
% 3.15/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.15/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.15/1.03  --inst_lit_sel_side                     num_symb
% 3.15/1.03  --inst_solver_per_active                1400
% 3.15/1.03  --inst_solver_calls_frac                1.
% 3.15/1.03  --inst_passive_queue_type               priority_queues
% 3.15/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.15/1.03  --inst_passive_queues_freq              [25;2]
% 3.15/1.03  --inst_dismatching                      true
% 3.15/1.03  --inst_eager_unprocessed_to_passive     true
% 3.15/1.03  --inst_prop_sim_given                   true
% 3.15/1.03  --inst_prop_sim_new                     false
% 3.15/1.03  --inst_subs_new                         false
% 3.15/1.03  --inst_eq_res_simp                      false
% 3.15/1.03  --inst_subs_given                       false
% 3.15/1.03  --inst_orphan_elimination               true
% 3.15/1.03  --inst_learning_loop_flag               true
% 3.15/1.03  --inst_learning_start                   3000
% 3.15/1.03  --inst_learning_factor                  2
% 3.15/1.03  --inst_start_prop_sim_after_learn       3
% 3.15/1.03  --inst_sel_renew                        solver
% 3.15/1.03  --inst_lit_activity_flag                true
% 3.15/1.03  --inst_restr_to_given                   false
% 3.15/1.03  --inst_activity_threshold               500
% 3.15/1.03  --inst_out_proof                        true
% 3.15/1.03  
% 3.15/1.03  ------ Resolution Options
% 3.15/1.03  
% 3.15/1.03  --resolution_flag                       true
% 3.15/1.03  --res_lit_sel                           adaptive
% 3.15/1.03  --res_lit_sel_side                      none
% 3.15/1.03  --res_ordering                          kbo
% 3.15/1.03  --res_to_prop_solver                    active
% 3.15/1.03  --res_prop_simpl_new                    false
% 3.15/1.03  --res_prop_simpl_given                  true
% 3.15/1.03  --res_passive_queue_type                priority_queues
% 3.15/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.15/1.03  --res_passive_queues_freq               [15;5]
% 3.15/1.03  --res_forward_subs                      full
% 3.15/1.03  --res_backward_subs                     full
% 3.15/1.03  --res_forward_subs_resolution           true
% 3.15/1.03  --res_backward_subs_resolution          true
% 3.15/1.03  --res_orphan_elimination                true
% 3.15/1.03  --res_time_limit                        2.
% 3.15/1.03  --res_out_proof                         true
% 3.15/1.03  
% 3.15/1.03  ------ Superposition Options
% 3.15/1.03  
% 3.15/1.03  --superposition_flag                    true
% 3.15/1.03  --sup_passive_queue_type                priority_queues
% 3.15/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.15/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.15/1.03  --demod_completeness_check              fast
% 3.15/1.03  --demod_use_ground                      true
% 3.15/1.03  --sup_to_prop_solver                    passive
% 3.15/1.03  --sup_prop_simpl_new                    true
% 3.15/1.03  --sup_prop_simpl_given                  true
% 3.15/1.03  --sup_fun_splitting                     true
% 3.15/1.03  --sup_smt_interval                      50000
% 3.15/1.03  
% 3.15/1.03  ------ Superposition Simplification Setup
% 3.15/1.03  
% 3.15/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.15/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.15/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.15/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.15/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.15/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.15/1.03  --sup_immed_triv                        [TrivRules]
% 3.15/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/1.03  --sup_immed_bw_main                     []
% 3.15/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.15/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.15/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/1.03  --sup_input_bw                          []
% 3.15/1.03  
% 3.15/1.03  ------ Combination Options
% 3.15/1.03  
% 3.15/1.03  --comb_res_mult                         3
% 3.15/1.03  --comb_sup_mult                         2
% 3.15/1.03  --comb_inst_mult                        10
% 3.15/1.03  
% 3.15/1.03  ------ Debug Options
% 3.15/1.03  
% 3.15/1.03  --dbg_backtrace                         false
% 3.15/1.03  --dbg_dump_prop_clauses                 false
% 3.15/1.03  --dbg_dump_prop_clauses_file            -
% 3.15/1.03  --dbg_out_stat                          false
% 3.15/1.03  ------ Parsing...
% 3.15/1.03  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.15/1.03  
% 3.15/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 3.15/1.03  
% 3.15/1.03  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.15/1.03  
% 3.15/1.03  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.15/1.03  ------ Proving...
% 3.15/1.03  ------ Problem Properties 
% 3.15/1.03  
% 3.15/1.03  
% 3.15/1.03  clauses                                 20
% 3.15/1.03  conjectures                             3
% 3.15/1.03  EPR                                     0
% 3.15/1.03  Horn                                    15
% 3.15/1.03  unary                                   3
% 3.15/1.03  binary                                  5
% 3.15/1.03  lits                                    57
% 3.15/1.03  lits eq                                 17
% 3.15/1.03  fd_pure                                 0
% 3.15/1.03  fd_pseudo                               0
% 3.15/1.03  fd_cond                                 0
% 3.15/1.03  fd_pseudo_cond                          4
% 3.15/1.03  AC symbols                              0
% 3.15/1.03  
% 3.15/1.03  ------ Schedule dynamic 5 is on 
% 3.15/1.03  
% 3.15/1.03  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 3.15/1.03  
% 3.15/1.03  
% 3.15/1.03  ------ 
% 3.15/1.03  Current options:
% 3.15/1.03  ------ 
% 3.15/1.03  
% 3.15/1.03  ------ Input Options
% 3.15/1.03  
% 3.15/1.03  --out_options                           all
% 3.15/1.03  --tptp_safe_out                         true
% 3.15/1.03  --problem_path                          ""
% 3.15/1.03  --include_path                          ""
% 3.15/1.03  --clausifier                            res/vclausify_rel
% 3.15/1.03  --clausifier_options                    ""
% 3.15/1.03  --stdin                                 false
% 3.15/1.03  --stats_out                             all
% 3.15/1.03  
% 3.15/1.03  ------ General Options
% 3.15/1.03  
% 3.15/1.03  --fof                                   false
% 3.15/1.03  --time_out_real                         305.
% 3.15/1.03  --time_out_virtual                      -1.
% 3.15/1.03  --symbol_type_check                     false
% 3.15/1.03  --clausify_out                          false
% 3.15/1.03  --sig_cnt_out                           false
% 3.15/1.03  --trig_cnt_out                          false
% 3.15/1.03  --trig_cnt_out_tolerance                1.
% 3.15/1.03  --trig_cnt_out_sk_spl                   false
% 3.15/1.03  --abstr_cl_out                          false
% 3.15/1.03  
% 3.15/1.03  ------ Global Options
% 3.15/1.03  
% 3.15/1.03  --schedule                              default
% 3.15/1.03  --add_important_lit                     false
% 3.15/1.03  --prop_solver_per_cl                    1000
% 3.15/1.03  --min_unsat_core                        false
% 3.15/1.03  --soft_assumptions                      false
% 3.15/1.03  --soft_lemma_size                       3
% 3.15/1.03  --prop_impl_unit_size                   0
% 3.15/1.03  --prop_impl_unit                        []
% 3.15/1.03  --share_sel_clauses                     true
% 3.15/1.03  --reset_solvers                         false
% 3.15/1.03  --bc_imp_inh                            [conj_cone]
% 3.15/1.03  --conj_cone_tolerance                   3.
% 3.15/1.03  --extra_neg_conj                        none
% 3.15/1.03  --large_theory_mode                     true
% 3.15/1.03  --prolific_symb_bound                   200
% 3.15/1.03  --lt_threshold                          2000
% 3.15/1.03  --clause_weak_htbl                      true
% 3.15/1.03  --gc_record_bc_elim                     false
% 3.15/1.03  
% 3.15/1.03  ------ Preprocessing Options
% 3.15/1.03  
% 3.15/1.03  --preprocessing_flag                    true
% 3.15/1.03  --time_out_prep_mult                    0.1
% 3.15/1.03  --splitting_mode                        input
% 3.15/1.03  --splitting_grd                         true
% 3.15/1.03  --splitting_cvd                         false
% 3.15/1.03  --splitting_cvd_svl                     false
% 3.15/1.03  --splitting_nvd                         32
% 3.15/1.03  --sub_typing                            true
% 3.15/1.03  --prep_gs_sim                           true
% 3.15/1.03  --prep_unflatten                        true
% 3.15/1.03  --prep_res_sim                          true
% 3.15/1.03  --prep_upred                            true
% 3.15/1.03  --prep_sem_filter                       exhaustive
% 3.15/1.03  --prep_sem_filter_out                   false
% 3.15/1.03  --pred_elim                             true
% 3.15/1.03  --res_sim_input                         true
% 3.15/1.03  --eq_ax_congr_red                       true
% 3.15/1.03  --pure_diseq_elim                       true
% 3.15/1.03  --brand_transform                       false
% 3.15/1.03  --non_eq_to_eq                          false
% 3.15/1.03  --prep_def_merge                        true
% 3.15/1.03  --prep_def_merge_prop_impl              false
% 3.15/1.03  --prep_def_merge_mbd                    true
% 3.15/1.03  --prep_def_merge_tr_red                 false
% 3.15/1.03  --prep_def_merge_tr_cl                  false
% 3.15/1.03  --smt_preprocessing                     true
% 3.15/1.03  --smt_ac_axioms                         fast
% 3.15/1.03  --preprocessed_out                      false
% 3.15/1.03  --preprocessed_stats                    false
% 3.15/1.03  
% 3.15/1.03  ------ Abstraction refinement Options
% 3.15/1.03  
% 3.15/1.03  --abstr_ref                             []
% 3.15/1.03  --abstr_ref_prep                        false
% 3.15/1.03  --abstr_ref_until_sat                   false
% 3.15/1.03  --abstr_ref_sig_restrict                funpre
% 3.15/1.03  --abstr_ref_af_restrict_to_split_sk     false
% 3.15/1.03  --abstr_ref_under                       []
% 3.15/1.03  
% 3.15/1.03  ------ SAT Options
% 3.15/1.03  
% 3.15/1.03  --sat_mode                              false
% 3.15/1.03  --sat_fm_restart_options                ""
% 3.15/1.03  --sat_gr_def                            false
% 3.15/1.03  --sat_epr_types                         true
% 3.15/1.03  --sat_non_cyclic_types                  false
% 3.15/1.03  --sat_finite_models                     false
% 3.15/1.03  --sat_fm_lemmas                         false
% 3.15/1.03  --sat_fm_prep                           false
% 3.15/1.03  --sat_fm_uc_incr                        true
% 3.15/1.03  --sat_out_model                         small
% 3.15/1.03  --sat_out_clauses                       false
% 3.15/1.03  
% 3.15/1.03  ------ QBF Options
% 3.15/1.03  
% 3.15/1.03  --qbf_mode                              false
% 3.15/1.03  --qbf_elim_univ                         false
% 3.15/1.03  --qbf_dom_inst                          none
% 3.15/1.03  --qbf_dom_pre_inst                      false
% 3.15/1.03  --qbf_sk_in                             false
% 3.15/1.03  --qbf_pred_elim                         true
% 3.15/1.03  --qbf_split                             512
% 3.15/1.03  
% 3.15/1.03  ------ BMC1 Options
% 3.15/1.03  
% 3.15/1.03  --bmc1_incremental                      false
% 3.15/1.03  --bmc1_axioms                           reachable_all
% 3.15/1.03  --bmc1_min_bound                        0
% 3.15/1.03  --bmc1_max_bound                        -1
% 3.15/1.03  --bmc1_max_bound_default                -1
% 3.15/1.03  --bmc1_symbol_reachability              true
% 3.15/1.03  --bmc1_property_lemmas                  false
% 3.15/1.03  --bmc1_k_induction                      false
% 3.15/1.03  --bmc1_non_equiv_states                 false
% 3.15/1.03  --bmc1_deadlock                         false
% 3.15/1.03  --bmc1_ucm                              false
% 3.15/1.03  --bmc1_add_unsat_core                   none
% 3.15/1.03  --bmc1_unsat_core_children              false
% 3.15/1.03  --bmc1_unsat_core_extrapolate_axioms    false
% 3.15/1.03  --bmc1_out_stat                         full
% 3.15/1.03  --bmc1_ground_init                      false
% 3.15/1.03  --bmc1_pre_inst_next_state              false
% 3.15/1.03  --bmc1_pre_inst_state                   false
% 3.15/1.03  --bmc1_pre_inst_reach_state             false
% 3.15/1.03  --bmc1_out_unsat_core                   false
% 3.15/1.03  --bmc1_aig_witness_out                  false
% 3.15/1.03  --bmc1_verbose                          false
% 3.15/1.03  --bmc1_dump_clauses_tptp                false
% 3.15/1.03  --bmc1_dump_unsat_core_tptp             false
% 3.15/1.03  --bmc1_dump_file                        -
% 3.15/1.03  --bmc1_ucm_expand_uc_limit              128
% 3.15/1.03  --bmc1_ucm_n_expand_iterations          6
% 3.15/1.03  --bmc1_ucm_extend_mode                  1
% 3.15/1.03  --bmc1_ucm_init_mode                    2
% 3.15/1.03  --bmc1_ucm_cone_mode                    none
% 3.15/1.03  --bmc1_ucm_reduced_relation_type        0
% 3.15/1.03  --bmc1_ucm_relax_model                  4
% 3.15/1.03  --bmc1_ucm_full_tr_after_sat            true
% 3.15/1.03  --bmc1_ucm_expand_neg_assumptions       false
% 3.15/1.03  --bmc1_ucm_layered_model                none
% 3.15/1.03  --bmc1_ucm_max_lemma_size               10
% 3.15/1.03  
% 3.15/1.03  ------ AIG Options
% 3.15/1.03  
% 3.15/1.03  --aig_mode                              false
% 3.15/1.03  
% 3.15/1.03  ------ Instantiation Options
% 3.15/1.03  
% 3.15/1.03  --instantiation_flag                    true
% 3.15/1.03  --inst_sos_flag                         true
% 3.15/1.03  --inst_sos_phase                        true
% 3.15/1.03  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 3.15/1.03  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 3.15/1.03  --inst_lit_sel_side                     none
% 3.15/1.03  --inst_solver_per_active                1400
% 3.15/1.03  --inst_solver_calls_frac                1.
% 3.15/1.03  --inst_passive_queue_type               priority_queues
% 3.15/1.03  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 3.15/1.03  --inst_passive_queues_freq              [25;2]
% 3.15/1.03  --inst_dismatching                      true
% 3.15/1.03  --inst_eager_unprocessed_to_passive     true
% 3.15/1.03  --inst_prop_sim_given                   true
% 3.15/1.03  --inst_prop_sim_new                     false
% 3.15/1.03  --inst_subs_new                         false
% 3.15/1.03  --inst_eq_res_simp                      false
% 3.15/1.03  --inst_subs_given                       false
% 3.15/1.03  --inst_orphan_elimination               true
% 3.15/1.03  --inst_learning_loop_flag               true
% 3.15/1.03  --inst_learning_start                   3000
% 3.15/1.03  --inst_learning_factor                  2
% 3.15/1.03  --inst_start_prop_sim_after_learn       3
% 3.15/1.03  --inst_sel_renew                        solver
% 3.15/1.03  --inst_lit_activity_flag                true
% 3.15/1.03  --inst_restr_to_given                   false
% 3.15/1.03  --inst_activity_threshold               500
% 3.15/1.03  --inst_out_proof                        true
% 3.15/1.03  
% 3.15/1.03  ------ Resolution Options
% 3.15/1.03  
% 3.15/1.03  --resolution_flag                       false
% 3.15/1.03  --res_lit_sel                           adaptive
% 3.15/1.03  --res_lit_sel_side                      none
% 3.15/1.03  --res_ordering                          kbo
% 3.15/1.03  --res_to_prop_solver                    active
% 3.15/1.03  --res_prop_simpl_new                    false
% 3.15/1.03  --res_prop_simpl_given                  true
% 3.15/1.03  --res_passive_queue_type                priority_queues
% 3.15/1.03  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 3.15/1.03  --res_passive_queues_freq               [15;5]
% 3.15/1.03  --res_forward_subs                      full
% 3.15/1.03  --res_backward_subs                     full
% 3.15/1.03  --res_forward_subs_resolution           true
% 3.15/1.03  --res_backward_subs_resolution          true
% 3.15/1.03  --res_orphan_elimination                true
% 3.15/1.03  --res_time_limit                        2.
% 3.15/1.03  --res_out_proof                         true
% 3.15/1.03  
% 3.15/1.03  ------ Superposition Options
% 3.15/1.03  
% 3.15/1.03  --superposition_flag                    true
% 3.15/1.03  --sup_passive_queue_type                priority_queues
% 3.15/1.03  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 3.15/1.03  --sup_passive_queues_freq               [8;1;4]
% 3.15/1.03  --demod_completeness_check              fast
% 3.15/1.03  --demod_use_ground                      true
% 3.15/1.03  --sup_to_prop_solver                    passive
% 3.15/1.03  --sup_prop_simpl_new                    true
% 3.15/1.03  --sup_prop_simpl_given                  true
% 3.15/1.03  --sup_fun_splitting                     true
% 3.15/1.03  --sup_smt_interval                      50000
% 3.15/1.03  
% 3.15/1.03  ------ Superposition Simplification Setup
% 3.15/1.03  
% 3.15/1.03  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 3.15/1.03  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 3.15/1.03  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 3.15/1.03  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 3.15/1.03  --sup_full_triv                         [TrivRules;PropSubs]
% 3.15/1.03  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 3.15/1.03  --sup_full_bw                           [BwDemod;BwSubsumption]
% 3.15/1.03  --sup_immed_triv                        [TrivRules]
% 3.15/1.03  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/1.03  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/1.03  --sup_immed_bw_main                     []
% 3.15/1.03  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 3.15/1.03  --sup_input_triv                        [Unflattening;TrivRules]
% 3.15/1.03  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 3.15/1.03  --sup_input_bw                          []
% 3.15/1.03  
% 3.15/1.03  ------ Combination Options
% 3.15/1.03  
% 3.15/1.03  --comb_res_mult                         3
% 3.15/1.03  --comb_sup_mult                         2
% 3.15/1.03  --comb_inst_mult                        10
% 3.15/1.03  
% 3.15/1.03  ------ Debug Options
% 3.15/1.03  
% 3.15/1.03  --dbg_backtrace                         false
% 3.15/1.03  --dbg_dump_prop_clauses                 false
% 3.15/1.03  --dbg_dump_prop_clauses_file            -
% 3.15/1.03  --dbg_out_stat                          false
% 3.15/1.03  
% 3.15/1.03  
% 3.15/1.03  
% 3.15/1.03  
% 3.15/1.03  ------ Proving...
% 3.15/1.03  
% 3.15/1.03  
% 3.15/1.03  % SZS status Theorem for theBenchmark.p
% 3.15/1.03  
% 3.15/1.03  % SZS output start CNFRefutation for theBenchmark.p
% 3.15/1.03  
% 3.15/1.03  fof(f6,axiom,(
% 3.15/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)))),
% 3.15/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.03  
% 3.15/1.03  fof(f16,plain,(
% 3.15/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.03    inference(ennf_transformation,[],[f6])).
% 3.15/1.03  
% 3.15/1.03  fof(f45,plain,(
% 3.15/1.03    ( ! [X2,X0,X3,X1] : (m1_subset_1(k7_relset_1(X0,X1,X2,X3),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/1.03    inference(cnf_transformation,[],[f16])).
% 3.15/1.03  
% 3.15/1.03  fof(f5,axiom,(
% 3.15/1.03    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 3.15/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.03  
% 3.15/1.03  fof(f14,plain,(
% 3.15/1.03    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.15/1.03    inference(ennf_transformation,[],[f5])).
% 3.15/1.03  
% 3.15/1.03  fof(f15,plain,(
% 3.15/1.03    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/1.03    inference(flattening,[],[f14])).
% 3.15/1.03  
% 3.15/1.03  fof(f23,plain,(
% 3.15/1.03    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/1.03    inference(nnf_transformation,[],[f15])).
% 3.15/1.03  
% 3.15/1.03  fof(f24,plain,(
% 3.15/1.03    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/1.03    inference(rectify,[],[f23])).
% 3.15/1.03  
% 3.15/1.03  fof(f27,plain,(
% 3.15/1.03    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 & r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))))),
% 3.15/1.03    introduced(choice_axiom,[])).
% 3.15/1.03  
% 3.15/1.03  fof(f26,plain,(
% 3.15/1.03    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1,X2)) = X3 & r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))))) )),
% 3.15/1.03    introduced(choice_axiom,[])).
% 3.15/1.03  
% 3.15/1.03  fof(f25,plain,(
% 3.15/1.03    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK0(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK0(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.15/1.03    introduced(choice_axiom,[])).
% 3.15/1.03  
% 3.15/1.03  fof(f28,plain,(
% 3.15/1.03    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK0(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2) & r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X1,X6)) = X6 & r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.15/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f24,f27,f26,f25])).
% 3.15/1.03  
% 3.15/1.03  fof(f38,plain,(
% 3.15/1.03    ( ! [X6,X2,X0,X1] : (r2_hidden(sK2(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/1.03    inference(cnf_transformation,[],[f28])).
% 3.15/1.03  
% 3.15/1.03  fof(f62,plain,(
% 3.15/1.03    ( ! [X6,X0,X1] : (r2_hidden(sK2(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/1.03    inference(equality_resolution,[],[f38])).
% 3.15/1.03  
% 3.15/1.03  fof(f10,conjecture,(
% 3.15/1.03    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.15/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.03  
% 3.15/1.03  fof(f11,negated_conjecture,(
% 3.15/1.03    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ~(! [X5] : ~(k1_funct_1(X3,X5) = X4 & r2_hidden(X5,X2) & r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))))),
% 3.15/1.03    inference(negated_conjecture,[],[f10])).
% 3.15/1.03  
% 3.15/1.03  fof(f21,plain,(
% 3.15/1.03    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.15/1.03    inference(ennf_transformation,[],[f11])).
% 3.15/1.03  
% 3.15/1.03  fof(f22,plain,(
% 3.15/1.03    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.15/1.03    inference(flattening,[],[f21])).
% 3.15/1.03  
% 3.15/1.03  fof(f31,plain,(
% 3.15/1.03    ( ! [X2,X0,X3,X1] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) => (! [X5] : (k1_funct_1(X3,X5) != sK7 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(sK7,k7_relset_1(X0,X1,X3,X2)))) )),
% 3.15/1.03    introduced(choice_axiom,[])).
% 3.15/1.03  
% 3.15/1.03  fof(f30,plain,(
% 3.15/1.03    ? [X0,X1,X2,X3] : (? [X4] : (! [X5] : (k1_funct_1(X3,X5) != X4 | ~r2_hidden(X5,X2) | ~r2_hidden(X5,X0)) & r2_hidden(X4,k7_relset_1(X0,X1,X3,X2))) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (? [X4] : (! [X5] : (k1_funct_1(sK6,X5) != X4 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(X4,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 3.15/1.03    introduced(choice_axiom,[])).
% 3.15/1.03  
% 3.15/1.03  fof(f32,plain,(
% 3.15/1.03    (! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) & r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 3.15/1.03    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6,sK7])],[f22,f31,f30])).
% 3.15/1.03  
% 3.15/1.03  fof(f54,plain,(
% 3.15/1.03    v1_funct_1(sK6)),
% 3.15/1.03    inference(cnf_transformation,[],[f32])).
% 3.15/1.03  
% 3.15/1.03  fof(f56,plain,(
% 3.15/1.03    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.15/1.03    inference(cnf_transformation,[],[f32])).
% 3.15/1.03  
% 3.15/1.03  fof(f3,axiom,(
% 3.15/1.03    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.15/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.03  
% 3.15/1.03  fof(f13,plain,(
% 3.15/1.03    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.15/1.03    inference(ennf_transformation,[],[f3])).
% 3.15/1.03  
% 3.15/1.03  fof(f35,plain,(
% 3.15/1.03    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.15/1.03    inference(cnf_transformation,[],[f13])).
% 3.15/1.03  
% 3.15/1.03  fof(f4,axiom,(
% 3.15/1.03    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.15/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.03  
% 3.15/1.03  fof(f36,plain,(
% 3.15/1.03    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.15/1.03    inference(cnf_transformation,[],[f4])).
% 3.15/1.03  
% 3.15/1.03  fof(f9,axiom,(
% 3.15/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.15/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.03  
% 3.15/1.03  fof(f19,plain,(
% 3.15/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.03    inference(ennf_transformation,[],[f9])).
% 3.15/1.03  
% 3.15/1.03  fof(f20,plain,(
% 3.15/1.03    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.03    inference(flattening,[],[f19])).
% 3.15/1.03  
% 3.15/1.03  fof(f29,plain,(
% 3.15/1.03    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.03    inference(nnf_transformation,[],[f20])).
% 3.15/1.03  
% 3.15/1.03  fof(f48,plain,(
% 3.15/1.03    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/1.03    inference(cnf_transformation,[],[f29])).
% 3.15/1.03  
% 3.15/1.03  fof(f55,plain,(
% 3.15/1.03    v1_funct_2(sK6,sK3,sK4)),
% 3.15/1.03    inference(cnf_transformation,[],[f32])).
% 3.15/1.03  
% 3.15/1.03  fof(f7,axiom,(
% 3.15/1.03    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.15/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.03  
% 3.15/1.03  fof(f17,plain,(
% 3.15/1.03    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.03    inference(ennf_transformation,[],[f7])).
% 3.15/1.03  
% 3.15/1.03  fof(f46,plain,(
% 3.15/1.03    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/1.03    inference(cnf_transformation,[],[f17])).
% 3.15/1.03  
% 3.15/1.03  fof(f37,plain,(
% 3.15/1.03    ( ! [X6,X2,X0,X1] : (r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/1.03    inference(cnf_transformation,[],[f28])).
% 3.15/1.03  
% 3.15/1.03  fof(f63,plain,(
% 3.15/1.03    ( ! [X6,X0,X1] : (r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/1.03    inference(equality_resolution,[],[f37])).
% 3.15/1.03  
% 3.15/1.03  fof(f8,axiom,(
% 3.15/1.03    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3))),
% 3.15/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.03  
% 3.15/1.03  fof(f18,plain,(
% 3.15/1.03    ! [X0,X1,X2,X3] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.15/1.03    inference(ennf_transformation,[],[f8])).
% 3.15/1.03  
% 3.15/1.03  fof(f47,plain,(
% 3.15/1.03    ( ! [X2,X0,X3,X1] : (k9_relat_1(X2,X3) = k7_relset_1(X0,X1,X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.15/1.03    inference(cnf_transformation,[],[f18])).
% 3.15/1.03  
% 3.15/1.03  fof(f57,plain,(
% 3.15/1.03    r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))),
% 3.15/1.03    inference(cnf_transformation,[],[f32])).
% 3.15/1.03  
% 3.15/1.03  fof(f39,plain,(
% 3.15/1.03    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/1.03    inference(cnf_transformation,[],[f28])).
% 3.15/1.03  
% 3.15/1.03  fof(f61,plain,(
% 3.15/1.03    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.15/1.03    inference(equality_resolution,[],[f39])).
% 3.15/1.03  
% 3.15/1.03  fof(f58,plain,(
% 3.15/1.03    ( ! [X5] : (k1_funct_1(sK6,X5) != sK7 | ~r2_hidden(X5,sK5) | ~r2_hidden(X5,sK3)) )),
% 3.15/1.03    inference(cnf_transformation,[],[f32])).
% 3.15/1.03  
% 3.15/1.03  fof(f1,axiom,(
% 3.15/1.03    v1_xboole_0(k1_xboole_0)),
% 3.15/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.03  
% 3.15/1.03  fof(f33,plain,(
% 3.15/1.03    v1_xboole_0(k1_xboole_0)),
% 3.15/1.03    inference(cnf_transformation,[],[f1])).
% 3.15/1.03  
% 3.15/1.03  fof(f2,axiom,(
% 3.15/1.03    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 3.15/1.03    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.15/1.03  
% 3.15/1.03  fof(f12,plain,(
% 3.15/1.03    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 3.15/1.03    inference(ennf_transformation,[],[f2])).
% 3.15/1.03  
% 3.15/1.03  fof(f34,plain,(
% 3.15/1.03    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 3.15/1.03    inference(cnf_transformation,[],[f12])).
% 3.15/1.03  
% 3.15/1.03  cnf(c_12,plain,
% 3.15/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.03      | m1_subset_1(k7_relset_1(X1,X2,X0,X3),k1_zfmisc_1(X2)) ),
% 3.15/1.03      inference(cnf_transformation,[],[f45]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_4017,plain,
% 3.15/1.03      ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,X0),k1_zfmisc_1(sK4))
% 3.15/1.03      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_12]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_6492,plain,
% 3.15/1.03      ( m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4))
% 3.15/1.03      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_4017]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_10,plain,
% 3.15/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.15/1.03      | r2_hidden(sK2(X1,X2,X0),X2)
% 3.15/1.03      | ~ v1_funct_1(X1)
% 3.15/1.03      | ~ v1_relat_1(X1) ),
% 3.15/1.03      inference(cnf_transformation,[],[f62]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_25,negated_conjecture,
% 3.15/1.03      ( v1_funct_1(sK6) ),
% 3.15/1.03      inference(cnf_transformation,[],[f54]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_417,plain,
% 3.15/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.15/1.03      | r2_hidden(sK2(X1,X2,X0),X2)
% 3.15/1.03      | ~ v1_relat_1(X1)
% 3.15/1.03      | sK6 != X1 ),
% 3.15/1.03      inference(resolution_lifted,[status(thm)],[c_10,c_25]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_418,plain,
% 3.15/1.03      ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
% 3.15/1.03      | r2_hidden(sK2(sK6,X1,X0),X1)
% 3.15/1.03      | ~ v1_relat_1(sK6) ),
% 3.15/1.03      inference(unflattening,[status(thm)],[c_417]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1025,plain,
% 3.15/1.03      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.15/1.03      | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
% 3.15/1.03      | v1_relat_1(sK6) != iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_23,negated_conjecture,
% 3.15/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.15/1.03      inference(cnf_transformation,[],[f56]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_28,plain,
% 3.15/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_419,plain,
% 3.15/1.03      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.15/1.03      | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
% 3.15/1.03      | v1_relat_1(sK6) != iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_418]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_2,plain,
% 3.15/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.15/1.03      | ~ v1_relat_1(X1)
% 3.15/1.03      | v1_relat_1(X0) ),
% 3.15/1.03      inference(cnf_transformation,[],[f35]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1088,plain,
% 3.15/1.03      ( ~ m1_subset_1(sK6,k1_zfmisc_1(X0))
% 3.15/1.03      | ~ v1_relat_1(X0)
% 3.15/1.03      | v1_relat_1(sK6) ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_2]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1132,plain,
% 3.15/1.03      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 3.15/1.03      | ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 3.15/1.03      | v1_relat_1(sK6) ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_1088]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1176,plain,
% 3.15/1.03      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.15/1.03      | ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
% 3.15/1.03      | v1_relat_1(sK6) ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_1132]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1177,plain,
% 3.15/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 3.15/1.03      | v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.15/1.03      | v1_relat_1(sK6) = iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_1176]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_3,plain,
% 3.15/1.03      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.15/1.03      inference(cnf_transformation,[],[f36]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1184,plain,
% 3.15/1.03      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_3]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1185,plain,
% 3.15/1.03      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) = iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_1184]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1224,plain,
% 3.15/1.03      ( r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top
% 3.15/1.03      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.15/1.03      inference(global_propositional_subsumption,
% 3.15/1.03                [status(thm)],
% 3.15/1.03                [c_1025,c_28,c_419,c_1177,c_1185]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1225,plain,
% 3.15/1.03      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.15/1.03      | r2_hidden(sK2(sK6,X1,X0),X1) = iProver_top ),
% 3.15/1.03      inference(renaming,[status(thm)],[c_1224]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_20,plain,
% 3.15/1.03      ( ~ v1_funct_2(X0,X1,X2)
% 3.15/1.03      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.15/1.03      | k1_xboole_0 = X2 ),
% 3.15/1.03      inference(cnf_transformation,[],[f48]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_24,negated_conjecture,
% 3.15/1.03      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.15/1.03      inference(cnf_transformation,[],[f55]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_531,plain,
% 3.15/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.03      | k1_relset_1(X1,X2,X0) = X1
% 3.15/1.03      | sK4 != X2
% 3.15/1.03      | sK3 != X1
% 3.15/1.03      | sK6 != X0
% 3.15/1.03      | k1_xboole_0 = X2 ),
% 3.15/1.03      inference(resolution_lifted,[status(thm)],[c_20,c_24]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_532,plain,
% 3.15/1.03      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.15/1.03      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.15/1.03      | k1_xboole_0 = sK4 ),
% 3.15/1.03      inference(unflattening,[status(thm)],[c_531]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_534,plain,
% 3.15/1.03      ( k1_relset_1(sK3,sK4,sK6) = sK3 | k1_xboole_0 = sK4 ),
% 3.15/1.03      inference(global_propositional_subsumption,
% 3.15/1.03                [status(thm)],
% 3.15/1.03                [c_532,c_23]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1033,plain,
% 3.15/1.03      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_13,plain,
% 3.15/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.03      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.15/1.03      inference(cnf_transformation,[],[f46]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1037,plain,
% 3.15/1.03      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.15/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1373,plain,
% 3.15/1.03      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.15/1.03      inference(superposition,[status(thm)],[c_1033,c_1037]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1400,plain,
% 3.15/1.03      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.15/1.03      inference(superposition,[status(thm)],[c_534,c_1373]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_11,plain,
% 3.15/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.15/1.03      | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
% 3.15/1.03      | ~ v1_funct_1(X1)
% 3.15/1.03      | ~ v1_relat_1(X1) ),
% 3.15/1.03      inference(cnf_transformation,[],[f63]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_402,plain,
% 3.15/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.15/1.03      | r2_hidden(sK2(X1,X2,X0),k1_relat_1(X1))
% 3.15/1.03      | ~ v1_relat_1(X1)
% 3.15/1.03      | sK6 != X1 ),
% 3.15/1.03      inference(resolution_lifted,[status(thm)],[c_11,c_25]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_403,plain,
% 3.15/1.03      ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
% 3.15/1.03      | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6))
% 3.15/1.03      | ~ v1_relat_1(sK6) ),
% 3.15/1.03      inference(unflattening,[status(thm)],[c_402]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1026,plain,
% 3.15/1.03      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.15/1.03      | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
% 3.15/1.03      | v1_relat_1(sK6) != iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_404,plain,
% 3.15/1.03      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.15/1.03      | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
% 3.15/1.03      | v1_relat_1(sK6) != iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_403]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1235,plain,
% 3.15/1.03      ( r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top
% 3.15/1.03      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top ),
% 3.15/1.03      inference(global_propositional_subsumption,
% 3.15/1.03                [status(thm)],
% 3.15/1.03                [c_1026,c_28,c_404,c_1177,c_1185]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1236,plain,
% 3.15/1.03      ( r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.15/1.03      | r2_hidden(sK2(sK6,X1,X0),k1_relat_1(sK6)) = iProver_top ),
% 3.15/1.03      inference(renaming,[status(thm)],[c_1235]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1690,plain,
% 3.15/1.03      ( sK4 = k1_xboole_0
% 3.15/1.03      | r2_hidden(X0,k9_relat_1(sK6,X1)) != iProver_top
% 3.15/1.03      | r2_hidden(sK2(sK6,X1,X0),sK3) = iProver_top ),
% 3.15/1.03      inference(superposition,[status(thm)],[c_1400,c_1236]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_14,plain,
% 3.15/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.15/1.03      | k7_relset_1(X1,X2,X0,X3) = k9_relat_1(X0,X3) ),
% 3.15/1.03      inference(cnf_transformation,[],[f47]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1036,plain,
% 3.15/1.03      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
% 3.15/1.03      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1398,plain,
% 3.15/1.03      ( k7_relset_1(sK3,sK4,sK6,X0) = k9_relat_1(sK6,X0) ),
% 3.15/1.03      inference(superposition,[status(thm)],[c_1033,c_1036]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_22,negated_conjecture,
% 3.15/1.03      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) ),
% 3.15/1.03      inference(cnf_transformation,[],[f57]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1034,plain,
% 3.15/1.03      ( r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5)) = iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1493,plain,
% 3.15/1.03      ( r2_hidden(sK7,k9_relat_1(sK6,sK5)) = iProver_top ),
% 3.15/1.03      inference(demodulation,[status(thm)],[c_1398,c_1034]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_9,plain,
% 3.15/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.15/1.03      | ~ v1_funct_1(X1)
% 3.15/1.03      | ~ v1_relat_1(X1)
% 3.15/1.03      | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
% 3.15/1.03      inference(cnf_transformation,[],[f61]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_432,plain,
% 3.15/1.03      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.15/1.03      | ~ v1_relat_1(X1)
% 3.15/1.03      | k1_funct_1(X1,sK2(X1,X2,X0)) = X0
% 3.15/1.03      | sK6 != X1 ),
% 3.15/1.03      inference(resolution_lifted,[status(thm)],[c_9,c_25]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_433,plain,
% 3.15/1.03      ( ~ r2_hidden(X0,k9_relat_1(sK6,X1))
% 3.15/1.03      | ~ v1_relat_1(sK6)
% 3.15/1.03      | k1_funct_1(sK6,sK2(sK6,X1,X0)) = X0 ),
% 3.15/1.03      inference(unflattening,[status(thm)],[c_432]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1024,plain,
% 3.15/1.03      ( k1_funct_1(sK6,sK2(sK6,X0,X1)) = X1
% 3.15/1.03      | r2_hidden(X1,k9_relat_1(sK6,X0)) != iProver_top
% 3.15/1.03      | v1_relat_1(sK6) != iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_433]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1496,plain,
% 3.15/1.03      ( k1_funct_1(sK6,sK2(sK6,sK5,sK7)) = sK7
% 3.15/1.03      | v1_relat_1(sK6) != iProver_top ),
% 3.15/1.03      inference(superposition,[status(thm)],[c_1493,c_1024]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1994,plain,
% 3.15/1.03      ( k1_funct_1(sK6,sK2(sK6,sK5,sK7)) = sK7 ),
% 3.15/1.03      inference(global_propositional_subsumption,
% 3.15/1.03                [status(thm)],
% 3.15/1.03                [c_1496,c_28,c_1177,c_1185]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_21,negated_conjecture,
% 3.15/1.03      ( ~ r2_hidden(X0,sK3)
% 3.15/1.03      | ~ r2_hidden(X0,sK5)
% 3.15/1.03      | k1_funct_1(sK6,X0) != sK7 ),
% 3.15/1.03      inference(cnf_transformation,[],[f58]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1035,plain,
% 3.15/1.03      ( k1_funct_1(sK6,X0) != sK7
% 3.15/1.03      | r2_hidden(X0,sK3) != iProver_top
% 3.15/1.03      | r2_hidden(X0,sK5) != iProver_top ),
% 3.15/1.03      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1997,plain,
% 3.15/1.03      ( r2_hidden(sK2(sK6,sK5,sK7),sK3) != iProver_top
% 3.15/1.03      | r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top ),
% 3.15/1.03      inference(superposition,[status(thm)],[c_1994,c_1035]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_3801,plain,
% 3.15/1.03      ( sK4 = k1_xboole_0
% 3.15/1.03      | r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top
% 3.15/1.03      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
% 3.15/1.03      inference(superposition,[status(thm)],[c_1690,c_1997]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_4029,plain,
% 3.15/1.03      ( r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top
% 3.15/1.03      | sK4 = k1_xboole_0 ),
% 3.15/1.03      inference(global_propositional_subsumption,
% 3.15/1.03                [status(thm)],
% 3.15/1.03                [c_3801,c_1493]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_4030,plain,
% 3.15/1.03      ( sK4 = k1_xboole_0
% 3.15/1.03      | r2_hidden(sK2(sK6,sK5,sK7),sK5) != iProver_top ),
% 3.15/1.03      inference(renaming,[status(thm)],[c_4029]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_4033,plain,
% 3.15/1.03      ( sK4 = k1_xboole_0
% 3.15/1.03      | r2_hidden(sK7,k9_relat_1(sK6,sK5)) != iProver_top ),
% 3.15/1.03      inference(superposition,[status(thm)],[c_1225,c_4030]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_690,plain,
% 3.15/1.03      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 3.15/1.03      theory(equality) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_3395,plain,
% 3.15/1.03      ( k1_zfmisc_1(k1_xboole_0) = k1_zfmisc_1(sK4)
% 3.15/1.03      | k1_xboole_0 != sK4 ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_690]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_691,plain,
% 3.15/1.03      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.15/1.03      theory(equality) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1109,plain,
% 3.15/1.03      ( ~ m1_subset_1(X0,X1)
% 3.15/1.03      | m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k1_xboole_0))
% 3.15/1.03      | k7_relset_1(sK3,sK4,sK6,sK5) != X0
% 3.15/1.03      | k1_zfmisc_1(k1_xboole_0) != X1 ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_691]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1149,plain,
% 3.15/1.03      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.15/1.03      | m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k1_xboole_0))
% 3.15/1.03      | k7_relset_1(sK3,sK4,sK6,sK5) != X0
% 3.15/1.03      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X1) ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_1109]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1216,plain,
% 3.15/1.03      ( ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(X0))
% 3.15/1.03      | m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k1_xboole_0))
% 3.15/1.03      | k7_relset_1(sK3,sK4,sK6,sK5) != k7_relset_1(sK3,sK4,sK6,sK5)
% 3.15/1.03      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(X0) ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_1149]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1891,plain,
% 3.15/1.03      ( ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(sK4))
% 3.15/1.03      | m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k1_xboole_0))
% 3.15/1.03      | k7_relset_1(sK3,sK4,sK6,sK5) != k7_relset_1(sK3,sK4,sK6,sK5)
% 3.15/1.03      | k1_zfmisc_1(k1_xboole_0) != k1_zfmisc_1(sK4) ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_1216]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_688,plain,( X0 = X0 ),theory(equality) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1391,plain,
% 3.15/1.03      ( k7_relset_1(sK3,sK4,sK6,sK5) = k7_relset_1(sK3,sK4,sK6,sK5) ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_688]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_689,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1243,plain,
% 3.15/1.03      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_689]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1244,plain,
% 3.15/1.03      ( sK4 != k1_xboole_0
% 3.15/1.03      | k1_xboole_0 = sK4
% 3.15/1.03      | k1_xboole_0 != k1_xboole_0 ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_1243]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_0,plain,
% 3.15/1.03      ( v1_xboole_0(k1_xboole_0) ),
% 3.15/1.03      inference(cnf_transformation,[],[f33]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1,plain,
% 3.15/1.03      ( ~ r2_hidden(X0,X1)
% 3.15/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.15/1.03      | ~ v1_xboole_0(X2) ),
% 3.15/1.03      inference(cnf_transformation,[],[f34]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_291,plain,
% 3.15/1.03      ( ~ r2_hidden(X0,X1)
% 3.15/1.03      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
% 3.15/1.03      | k1_xboole_0 != X2 ),
% 3.15/1.03      inference(resolution_lifted,[status(thm)],[c_0,c_1]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_292,plain,
% 3.15/1.03      ( ~ r2_hidden(X0,X1) | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) ),
% 3.15/1.03      inference(unflattening,[status(thm)],[c_291]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_1073,plain,
% 3.15/1.03      ( ~ r2_hidden(sK7,k7_relset_1(sK3,sK4,sK6,sK5))
% 3.15/1.03      | ~ m1_subset_1(k7_relset_1(sK3,sK4,sK6,sK5),k1_zfmisc_1(k1_xboole_0)) ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_292]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(c_717,plain,
% 3.15/1.03      ( k1_xboole_0 = k1_xboole_0 ),
% 3.15/1.03      inference(instantiation,[status(thm)],[c_688]) ).
% 3.15/1.03  
% 3.15/1.03  cnf(contradiction,plain,
% 3.15/1.03      ( $false ),
% 3.15/1.03      inference(minisat,
% 3.15/1.03                [status(thm)],
% 3.15/1.03                [c_6492,c_4033,c_3395,c_1891,c_1493,c_1391,c_1244,c_1073,
% 3.15/1.03                 c_717,c_22,c_23]) ).
% 3.15/1.03  
% 3.15/1.03  
% 3.15/1.03  % SZS output end CNFRefutation for theBenchmark.p
% 3.15/1.03  
% 3.15/1.03  ------                               Statistics
% 3.15/1.03  
% 3.15/1.03  ------ General
% 3.15/1.03  
% 3.15/1.03  abstr_ref_over_cycles:                  0
% 3.15/1.03  abstr_ref_under_cycles:                 0
% 3.15/1.03  gc_basic_clause_elim:                   0
% 3.15/1.03  forced_gc_time:                         0
% 3.15/1.03  parsing_time:                           0.007
% 3.15/1.03  unif_index_cands_time:                  0.
% 3.15/1.03  unif_index_add_time:                    0.
% 3.15/1.03  orderings_time:                         0.
% 3.15/1.03  out_proof_time:                         0.011
% 3.15/1.03  total_time:                             0.236
% 3.15/1.03  num_of_symbols:                         53
% 3.15/1.03  num_of_terms:                           9698
% 3.15/1.03  
% 3.15/1.03  ------ Preprocessing
% 3.15/1.03  
% 3.15/1.03  num_of_splits:                          0
% 3.15/1.03  num_of_split_atoms:                     0
% 3.15/1.03  num_of_reused_defs:                     0
% 3.15/1.03  num_eq_ax_congr_red:                    28
% 3.15/1.03  num_of_sem_filtered_clauses:            1
% 3.15/1.03  num_of_subtypes:                        0
% 3.15/1.03  monotx_restored_types:                  0
% 3.15/1.03  sat_num_of_epr_types:                   0
% 3.15/1.03  sat_num_of_non_cyclic_types:            0
% 3.15/1.03  sat_guarded_non_collapsed_types:        0
% 3.15/1.03  num_pure_diseq_elim:                    0
% 3.15/1.03  simp_replaced_by:                       0
% 3.15/1.03  res_preprocessed:                       117
% 3.15/1.03  prep_upred:                             0
% 3.15/1.03  prep_unflattend:                        36
% 3.15/1.03  smt_new_axioms:                         0
% 3.15/1.03  pred_elim_cands:                        3
% 3.15/1.03  pred_elim:                              3
% 3.15/1.03  pred_elim_cl:                           6
% 3.15/1.03  pred_elim_cycles:                       5
% 3.15/1.03  merged_defs:                            0
% 3.15/1.03  merged_defs_ncl:                        0
% 3.15/1.03  bin_hyper_res:                          0
% 3.15/1.03  prep_cycles:                            4
% 3.15/1.03  pred_elim_time:                         0.004
% 3.15/1.03  splitting_time:                         0.
% 3.15/1.03  sem_filter_time:                        0.
% 3.15/1.03  monotx_time:                            0.
% 3.15/1.03  subtype_inf_time:                       0.
% 3.15/1.03  
% 3.15/1.03  ------ Problem properties
% 3.15/1.03  
% 3.15/1.03  clauses:                                20
% 3.15/1.03  conjectures:                            3
% 3.15/1.03  epr:                                    0
% 3.15/1.03  horn:                                   15
% 3.15/1.03  ground:                                 5
% 3.15/1.03  unary:                                  3
% 3.15/1.03  binary:                                 5
% 3.15/1.03  lits:                                   57
% 3.15/1.03  lits_eq:                                17
% 3.15/1.03  fd_pure:                                0
% 3.15/1.03  fd_pseudo:                              0
% 3.15/1.03  fd_cond:                                0
% 3.15/1.03  fd_pseudo_cond:                         4
% 3.15/1.03  ac_symbols:                             0
% 3.15/1.03  
% 3.15/1.03  ------ Propositional Solver
% 3.15/1.03  
% 3.15/1.03  prop_solver_calls:                      32
% 3.15/1.03  prop_fast_solver_calls:                 1053
% 3.15/1.03  smt_solver_calls:                       0
% 3.15/1.03  smt_fast_solver_calls:                  0
% 3.15/1.03  prop_num_of_clauses:                    3179
% 3.15/1.03  prop_preprocess_simplified:             6042
% 3.15/1.03  prop_fo_subsumed:                       27
% 3.15/1.03  prop_solver_time:                       0.
% 3.15/1.03  smt_solver_time:                        0.
% 3.15/1.03  smt_fast_solver_time:                   0.
% 3.15/1.03  prop_fast_solver_time:                  0.
% 3.15/1.03  prop_unsat_core_time:                   0.
% 3.15/1.03  
% 3.15/1.03  ------ QBF
% 3.15/1.03  
% 3.15/1.03  qbf_q_res:                              0
% 3.15/1.03  qbf_num_tautologies:                    0
% 3.15/1.03  qbf_prep_cycles:                        0
% 3.15/1.03  
% 3.15/1.03  ------ BMC1
% 3.15/1.03  
% 3.15/1.03  bmc1_current_bound:                     -1
% 3.15/1.03  bmc1_last_solved_bound:                 -1
% 3.15/1.03  bmc1_unsat_core_size:                   -1
% 3.15/1.03  bmc1_unsat_core_parents_size:           -1
% 3.15/1.03  bmc1_merge_next_fun:                    0
% 3.15/1.03  bmc1_unsat_core_clauses_time:           0.
% 3.15/1.03  
% 3.15/1.03  ------ Instantiation
% 3.15/1.03  
% 3.15/1.03  inst_num_of_clauses:                    678
% 3.15/1.03  inst_num_in_passive:                    55
% 3.15/1.03  inst_num_in_active:                     476
% 3.15/1.03  inst_num_in_unprocessed:                146
% 3.15/1.03  inst_num_of_loops:                      579
% 3.15/1.03  inst_num_of_learning_restarts:          0
% 3.15/1.03  inst_num_moves_active_passive:          97
% 3.15/1.03  inst_lit_activity:                      0
% 3.15/1.03  inst_lit_activity_moves:                0
% 3.15/1.03  inst_num_tautologies:                   0
% 3.15/1.03  inst_num_prop_implied:                  0
% 3.15/1.03  inst_num_existing_simplified:           0
% 3.15/1.03  inst_num_eq_res_simplified:             0
% 3.15/1.03  inst_num_child_elim:                    0
% 3.15/1.03  inst_num_of_dismatching_blockings:      339
% 3.15/1.03  inst_num_of_non_proper_insts:           963
% 3.15/1.03  inst_num_of_duplicates:                 0
% 3.15/1.03  inst_inst_num_from_inst_to_res:         0
% 3.15/1.03  inst_dismatching_checking_time:         0.
% 3.15/1.03  
% 3.15/1.03  ------ Resolution
% 3.15/1.03  
% 3.15/1.03  res_num_of_clauses:                     0
% 3.15/1.03  res_num_in_passive:                     0
% 3.15/1.03  res_num_in_active:                      0
% 3.15/1.03  res_num_of_loops:                       121
% 3.15/1.03  res_forward_subset_subsumed:            57
% 3.15/1.03  res_backward_subset_subsumed:           0
% 3.15/1.03  res_forward_subsumed:                   0
% 3.15/1.03  res_backward_subsumed:                  0
% 3.15/1.03  res_forward_subsumption_resolution:     0
% 3.15/1.03  res_backward_subsumption_resolution:    0
% 3.15/1.03  res_clause_to_clause_subsumption:       982
% 3.15/1.03  res_orphan_elimination:                 0
% 3.15/1.03  res_tautology_del:                      145
% 3.15/1.03  res_num_eq_res_simplified:              0
% 3.15/1.03  res_num_sel_changes:                    0
% 3.15/1.03  res_moves_from_active_to_pass:          0
% 3.15/1.03  
% 3.15/1.03  ------ Superposition
% 3.15/1.03  
% 3.15/1.03  sup_time_total:                         0.
% 3.15/1.03  sup_time_generating:                    0.
% 3.15/1.03  sup_time_sim_full:                      0.
% 3.15/1.03  sup_time_sim_immed:                     0.
% 3.15/1.03  
% 3.15/1.03  sup_num_of_clauses:                     320
% 3.15/1.03  sup_num_in_active:                      97
% 3.15/1.03  sup_num_in_passive:                     223
% 3.15/1.03  sup_num_of_loops:                       114
% 3.15/1.03  sup_fw_superposition:                   296
% 3.15/1.03  sup_bw_superposition:                   77
% 3.15/1.03  sup_immediate_simplified:               44
% 3.15/1.03  sup_given_eliminated:                   0
% 3.15/1.03  comparisons_done:                       0
% 3.15/1.03  comparisons_avoided:                    11
% 3.15/1.03  
% 3.15/1.03  ------ Simplifications
% 3.15/1.03  
% 3.15/1.03  
% 3.15/1.03  sim_fw_subset_subsumed:                 3
% 3.15/1.03  sim_bw_subset_subsumed:                 10
% 3.15/1.03  sim_fw_subsumed:                        22
% 3.15/1.03  sim_bw_subsumed:                        14
% 3.15/1.03  sim_fw_subsumption_res:                 0
% 3.15/1.03  sim_bw_subsumption_res:                 0
% 3.15/1.03  sim_tautology_del:                      2
% 3.15/1.03  sim_eq_tautology_del:                   8
% 3.15/1.03  sim_eq_res_simp:                        1
% 3.15/1.03  sim_fw_demodulated:                     0
% 3.15/1.03  sim_bw_demodulated:                     9
% 3.15/1.03  sim_light_normalised:                   9
% 3.15/1.03  sim_joinable_taut:                      0
% 3.15/1.03  sim_joinable_simp:                      0
% 3.15/1.03  sim_ac_normalised:                      0
% 3.15/1.03  sim_smt_subsumption:                    0
% 3.15/1.03  
%------------------------------------------------------------------------------
