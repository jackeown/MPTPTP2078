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
% DateTime   : Thu Dec  3 12:01:05 EST 2020

% Result     : Theorem 3.73s
% Output     : CNFRefutation 3.73s
% Verified   : 
% Statistics : Number of formulae       :  204 (67568 expanded)
%              Number of clauses        :  145 (23258 expanded)
%              Number of leaves         :   21 (13530 expanded)
%              Depth                    :   40
%              Number of atoms          :  616 (313117 expanded)
%              Number of equality atoms :  347 (95273 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

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
    inference(ennf_transformation,[],[f7])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f28,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f29,plain,(
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
    inference(rectify,[],[f28])).

fof(f32,plain,(
    ! [X6,X1,X0] :
      ( ? [X8] :
          ( k1_funct_1(X0,X8) = X6
          & r2_hidden(X8,X1)
          & r2_hidden(X8,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
        & r2_hidden(sK2(X0,X1,X6),X1)
        & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X5] :
          ( k1_funct_1(X0,X5) = X3
          & r2_hidden(X5,X1)
          & r2_hidden(X5,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK1(X0,X1,X2)) = X3
        & r2_hidden(sK1(X0,X1,X2),X1)
        & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,(
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

fof(f33,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).

fof(f44,plain,(
    ! [X6,X2,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f68,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(sK2(X0,X1,X6),X1)
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f44])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ~ ( k1_funct_1(X3,X4) = X2
                & r2_hidden(X4,X0) )
          & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ~ ( k1_funct_1(X3,X4) = X2
                  & r2_hidden(X4,X0) )
            & r2_hidden(X2,k2_relset_1(X0,X1,X3)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f26,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f27,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X2
          | ~ r2_hidden(X4,X0) )
      & r2_hidden(X2,k2_relset_1(X0,X1,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f26])).

fof(f35,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X2
            | ~ r2_hidden(X4,X0) )
        & r2_hidden(X2,k2_relset_1(X0,X1,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK6,X4) != sK5
          | ~ r2_hidden(X4,sK3) )
      & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_2(sK6,sK3,sK4)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ! [X4] :
        ( k1_funct_1(sK6,X4) != sK5
        | ~ r2_hidden(X4,sK3) )
    & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_2(sK6,sK3,sK4)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f27,f35])).

fof(f62,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f36])).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
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
    inference(flattening,[],[f24])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f25])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f61,plain,(
    v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f36])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f63,plain,(
    r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f36])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f40,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f42,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f45,plain,(
    ! [X6,X2,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,X2)
      | k9_relat_1(X0,X1) != X2
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f67,plain,(
    ! [X6,X0,X1] :
      ( k1_funct_1(X0,sK2(X0,X1,X6)) = X6
      | ~ r2_hidden(X6,k9_relat_1(X0,X1))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f45])).

fof(f60,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f36])).

fof(f64,plain,(
    ! [X4] :
      ( k1_funct_1(sK6,X4) != sK5
      | ~ r2_hidden(X4,sK3) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f72,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f58])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f74,plain,(
    ! [X2,X1] :
      ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f55])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(unused_predicate_definition_removal,[],[f3])).

fof(f16,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f1,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f37,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X2,X0)
      | ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | r2_hidden(sK2(X1,X2,X0),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_753,plain,
    ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
    | r2_hidden(sK2(X1,X2,X0),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_relat_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_25,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f62])).

cnf(c_740,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_22,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f54])).

cnf(c_743,plain,
    ( k1_relset_1(X0,X1,X2) = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X2,X0,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_1230,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | sK4 = k1_xboole_0
    | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_740,c_743])).

cnf(c_26,negated_conjecture,
    ( v1_funct_2(sK6,sK3,sK4) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_1231,plain,
    ( ~ v1_funct_2(sK6,sK3,sK4)
    | k1_relset_1(sK3,sK4,sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(predicate_to_equality_rev,[status(thm)],[c_1230])).

cnf(c_1729,plain,
    ( sK4 = k1_xboole_0
    | k1_relset_1(sK3,sK4,sK6) = sK3 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1230,c_26,c_1231])).

cnf(c_1730,plain,
    ( k1_relset_1(sK3,sK4,sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_1729])).

cnf(c_15,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_750,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_1393,plain,
    ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_740,c_750])).

cnf(c_1731,plain,
    ( k1_relat_1(sK6) = sK3
    | sK4 = k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_1730,c_1393])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_749,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_1379,plain,
    ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_740,c_749])).

cnf(c_24,negated_conjecture,
    ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
    inference(cnf_transformation,[],[f63])).

cnf(c_741,plain,
    ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1548,plain,
    ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_1379,c_741])).

cnf(c_3,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_762,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | v1_relat_1(X1) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_1534,plain,
    ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_740,c_762])).

cnf(c_1079,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK4))
    | v1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_3,c_25])).

cnf(c_4,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_1114,plain,
    ( v1_relat_1(sK6) ),
    inference(forward_subsumption_resolution,[status(thm)],[c_1079,c_4])).

cnf(c_1115,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1114])).

cnf(c_1722,plain,
    ( v1_relat_1(sK6) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1534,c_1115])).

cnf(c_5,plain,
    ( ~ v1_relat_1(X0)
    | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_760,plain,
    ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_1727,plain,
    ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
    inference(superposition,[status(thm)],[c_1722,c_760])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
    inference(cnf_transformation,[],[f67])).

cnf(c_754,plain,
    ( k1_funct_1(X0,sK2(X0,X1,X2)) = X2
    | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_3269,plain,
    ( k1_funct_1(sK6,sK2(sK6,k1_relat_1(sK6),X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1727,c_754])).

cnf(c_27,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_28,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_3518,plain,
    ( k1_funct_1(sK6,sK2(sK6,k1_relat_1(sK6),X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3269,c_28,c_1115])).

cnf(c_3527,plain,
    ( k1_funct_1(sK6,sK2(sK6,k1_relat_1(sK6),sK5)) = sK5 ),
    inference(superposition,[status(thm)],[c_1548,c_3518])).

cnf(c_3727,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK3,sK5)) = sK5
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1731,c_3527])).

cnf(c_1890,plain,
    ( k9_relat_1(sK6,sK3) = k2_relat_1(sK6)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1731,c_1727])).

cnf(c_23,negated_conjecture,
    ( ~ r2_hidden(X0,sK3)
    | k1_funct_1(sK6,X0) != sK5 ),
    inference(cnf_transformation,[],[f64])).

cnf(c_742,plain,
    ( k1_funct_1(sK6,X0) != sK5
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3728,plain,
    ( r2_hidden(sK2(sK6,k1_relat_1(sK6),sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_3527,c_742])).

cnf(c_3738,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK2(sK6,sK3,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_1731,c_3728])).

cnf(c_3861,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK5,k9_relat_1(sK6,sK3)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_3738])).

cnf(c_3864,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK5,k9_relat_1(sK6,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3861,c_28,c_1115])).

cnf(c_3870,plain,
    ( sK4 = k1_xboole_0
    | r2_hidden(sK5,k2_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1890,c_3864])).

cnf(c_4008,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3727,c_1548,c_3870])).

cnf(c_4019,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4008,c_740])).

cnf(c_18,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_747,plain,
    ( k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_4259,plain,
    ( sK3 = k1_xboole_0
    | sK6 = k1_xboole_0
    | v1_funct_2(sK6,sK3,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_4019,c_747])).

cnf(c_29,plain,
    ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_262,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_289,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_1278,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_275,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_funct_2(X3,X4,X5)
    | X3 != X0
    | X4 != X1
    | X5 != X2 ),
    theory(equality)).

cnf(c_1131,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ v1_funct_2(sK6,sK3,sK4)
    | X2 != sK4
    | X1 != sK3
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_275])).

cnf(c_1277,plain,
    ( v1_funct_2(sK6,X0,X1)
    | ~ v1_funct_2(sK6,sK3,sK4)
    | X1 != sK4
    | X0 != sK3
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1131])).

cnf(c_1588,plain,
    ( v1_funct_2(sK6,sK3,X0)
    | ~ v1_funct_2(sK6,sK3,sK4)
    | X0 != sK4
    | sK3 != sK3
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1277])).

cnf(c_1590,plain,
    ( X0 != sK4
    | sK3 != sK3
    | sK6 != sK6
    | v1_funct_2(sK6,sK3,X0) = iProver_top
    | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1588])).

cnf(c_1592,plain,
    ( sK3 != sK3
    | sK6 != sK6
    | k1_xboole_0 != sK4
    | v1_funct_2(sK6,sK3,sK4) != iProver_top
    | v1_funct_2(sK6,sK3,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1590])).

cnf(c_1589,plain,
    ( sK3 = sK3 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_263,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2317,plain,
    ( X0 != X1
    | X0 = sK4
    | sK4 != X1 ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_2318,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_2317])).

cnf(c_5038,plain,
    ( sK6 = k1_xboole_0
    | sK3 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4259,c_29,c_289,c_1278,c_1548,c_1592,c_1589,c_2318,c_3870])).

cnf(c_5039,plain,
    ( sK3 = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_5038])).

cnf(c_5045,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_5039,c_4019])).

cnf(c_21,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f74])).

cnf(c_744,plain,
    ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
    | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_5386,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | sK6 = k1_xboole_0
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5045,c_744])).

cnf(c_739,plain,
    ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_4020,plain,
    ( v1_funct_2(sK6,sK3,k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_4008,c_739])).

cnf(c_5046,plain,
    ( sK6 = k1_xboole_0
    | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_5039,c_4020])).

cnf(c_7589,plain,
    ( sK6 = k1_xboole_0
    | k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_5386,c_5046])).

cnf(c_7590,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(renaming,[status(thm)],[c_7589])).

cnf(c_4017,plain,
    ( k1_relset_1(sK3,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
    inference(demodulation,[status(thm)],[c_4008,c_1393])).

cnf(c_5044,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6)
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_5039,c_4017])).

cnf(c_7596,plain,
    ( k1_relat_1(sK6) = k1_xboole_0
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7590,c_5044])).

cnf(c_8569,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7596,c_3728])).

cnf(c_31,plain,
    ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_1092,plain,
    ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_1218,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_262])).

cnf(c_265,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1095,plain,
    ( r2_hidden(X0,X1)
    | ~ r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
    | X1 != k2_relset_1(sK3,sK4,sK6)
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_265])).

cnf(c_1217,plain,
    ( r2_hidden(sK5,X0)
    | ~ r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
    | X0 != k2_relset_1(sK3,sK4,sK6)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1095])).

cnf(c_1468,plain,
    ( ~ r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
    | r2_hidden(sK5,k9_relat_1(sK6,X0))
    | k9_relat_1(sK6,X0) != k2_relset_1(sK3,sK4,sK6)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1217])).

cnf(c_1472,plain,
    ( k9_relat_1(sK6,X0) != k2_relset_1(sK3,sK4,sK6)
    | sK5 != sK5
    | r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) != iProver_top
    | r2_hidden(sK5,k9_relat_1(sK6,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1468])).

cnf(c_1474,plain,
    ( k9_relat_1(sK6,k1_xboole_0) != k2_relset_1(sK3,sK4,sK6)
    | sK5 != sK5
    | r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) != iProver_top
    | r2_hidden(sK5,k9_relat_1(sK6,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1472])).

cnf(c_1865,plain,
    ( r2_hidden(sK2(sK6,X0,sK5),X0)
    | ~ r2_hidden(sK5,k9_relat_1(sK6,X0))
    | ~ v1_funct_1(sK6)
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_1866,plain,
    ( r2_hidden(sK2(sK6,X0,sK5),X0) = iProver_top
    | r2_hidden(sK5,k9_relat_1(sK6,X0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1865])).

cnf(c_1868,plain,
    ( r2_hidden(sK2(sK6,k1_xboole_0,sK5),k1_xboole_0) = iProver_top
    | r2_hidden(sK5,k9_relat_1(sK6,k1_xboole_0)) != iProver_top
    | v1_funct_1(sK6) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1866])).

cnf(c_1459,plain,
    ( X0 != X1
    | X0 = k2_relset_1(sK3,sK4,sK6)
    | k2_relset_1(sK3,sK4,sK6) != X1 ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_2585,plain,
    ( X0 = k2_relset_1(sK3,sK4,sK6)
    | X0 != k2_relat_1(sK6)
    | k2_relset_1(sK3,sK4,sK6) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1459])).

cnf(c_3471,plain,
    ( k2_relset_1(sK3,sK4,sK6) != k2_relat_1(sK6)
    | k9_relat_1(sK6,X0) = k2_relset_1(sK3,sK4,sK6)
    | k9_relat_1(sK6,X0) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_2585])).

cnf(c_3475,plain,
    ( k2_relset_1(sK3,sK4,sK6) != k2_relat_1(sK6)
    | k9_relat_1(sK6,k1_xboole_0) = k2_relset_1(sK3,sK4,sK6)
    | k9_relat_1(sK6,k1_xboole_0) != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_3471])).

cnf(c_5047,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK2(sK6,k1_relat_1(sK6),sK5),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_5039,c_3728])).

cnf(c_8568,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0,sK5),k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7596,c_5047])).

cnf(c_8571,plain,
    ( k9_relat_1(sK6,k1_xboole_0) = k2_relat_1(sK6)
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_7596,c_1727])).

cnf(c_8726,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_8569,c_28,c_25,c_31,c_1092,c_1115,c_1218,c_1474,c_1868,c_3475,c_8568,c_8571])).

cnf(c_738,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_8759,plain,
    ( v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8726,c_738])).

cnf(c_8757,plain,
    ( r2_hidden(sK5,k2_relat_1(k1_xboole_0)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_8726,c_1548])).

cnf(c_2,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_763,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_0,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f37])).

cnf(c_765,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_1378,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
    inference(superposition,[status(thm)],[c_763,c_749])).

cnf(c_2897,plain,
    ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_765,c_1378])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_751,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_2900,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
    | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_2897,c_751])).

cnf(c_6873,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_763,c_2900])).

cnf(c_7036,plain,
    ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_6873,c_765])).

cnf(c_1,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f38])).

cnf(c_764,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_7040,plain,
    ( r2_hidden(X0,X1) = iProver_top
    | r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_7036,c_764])).

cnf(c_10301,plain,
    ( r2_hidden(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_8757,c_7040])).

cnf(c_10633,plain,
    ( k1_funct_1(X0,sK2(X0,X1,sK5)) = sK5
    | v1_funct_1(X0) != iProver_top
    | v1_relat_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_10301,c_754])).

cnf(c_12379,plain,
    ( k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,X0,sK5)) = sK5
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_8759,c_10633])).

cnf(c_89,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_91,plain,
    ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_89])).

cnf(c_1008,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
    | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_1009,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1008])).

cnf(c_1011,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
    | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_1009])).

cnf(c_1013,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0)
    | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_1014,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top
    | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1013])).

cnf(c_1016,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1014])).

cnf(c_1314,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_1315,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1314])).

cnf(c_1317,plain,
    ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1315])).

cnf(c_12384,plain,
    ( k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,X0,sK5)) = sK5 ),
    inference(global_propositional_subsumption,[status(thm)],[c_12379,c_91,c_1011,c_1016,c_1317])).

cnf(c_8758,plain,
    ( k1_funct_1(k1_xboole_0,X0) != sK5
    | r2_hidden(X0,sK3) != iProver_top ),
    inference(demodulation,[status(thm)],[c_8726,c_742])).

cnf(c_12391,plain,
    ( r2_hidden(sK2(k1_xboole_0,X0,sK5),sK3) != iProver_top ),
    inference(superposition,[status(thm)],[c_12384,c_8758])).

cnf(c_12466,plain,
    ( r2_hidden(sK5,k9_relat_1(k1_xboole_0,sK3)) != iProver_top
    | v1_funct_1(k1_xboole_0) != iProver_top
    | v1_relat_1(k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_753,c_12391])).

cnf(c_272,plain,
    ( ~ v1_funct_1(X0)
    | v1_funct_1(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_1046,plain,
    ( v1_funct_1(X0)
    | ~ v1_funct_1(sK6)
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_272])).

cnf(c_1047,plain,
    ( X0 != sK6
    | v1_funct_1(X0) = iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1046])).

cnf(c_1049,plain,
    ( k1_xboole_0 != sK6
    | v1_funct_1(sK6) != iProver_top
    | v1_funct_1(k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_1047])).

cnf(c_1198,plain,
    ( X0 != X1
    | X0 = sK6
    | sK6 != X1 ),
    inference(instantiation,[status(thm)],[c_263])).

cnf(c_1199,plain,
    ( sK6 != k1_xboole_0
    | k1_xboole_0 = sK6
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1198])).

cnf(c_12476,plain,
    ( r2_hidden(sK5,k9_relat_1(k1_xboole_0,sK3)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_12466,c_28,c_25,c_31,c_91,c_289,c_1011,c_1016,c_1049,c_1092,c_1115,c_1199,c_1218,c_1317,c_1474,c_1868,c_3475,c_8568,c_8571])).

cnf(c_12481,plain,
    ( $false ),
    inference(forward_subsumption_resolution,[status(thm)],[c_12476,c_10301])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 19:53:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 3.73/0.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 3.73/0.98  
% 3.73/0.98  ------  iProver source info
% 3.73/0.98  
% 3.73/0.98  git: date: 2020-06-30 10:37:57 +0100
% 3.73/0.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 3.73/0.98  git: non_committed_changes: false
% 3.73/0.98  git: last_make_outside_of_git: false
% 3.73/0.98  
% 3.73/0.98  ------ 
% 3.73/0.98  ------ Parsing...
% 3.73/0.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e 
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 3.73/0.98  
% 3.73/0.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 3.73/0.98  ------ Proving...
% 3.73/0.98  ------ Problem Properties 
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  clauses                                 28
% 3.73/0.98  conjectures                             5
% 3.73/0.98  EPR                                     3
% 3.73/0.98  Horn                                    21
% 3.73/0.98  unary                                   6
% 3.73/0.98  binary                                  6
% 3.73/0.98  lits                                    84
% 3.73/0.98  lits eq                                 20
% 3.73/0.98  fd_pure                                 0
% 3.73/0.98  fd_pseudo                               0
% 3.73/0.98  fd_cond                                 3
% 3.73/0.98  fd_pseudo_cond                          4
% 3.73/0.98  AC symbols                              0
% 3.73/0.98  
% 3.73/0.98  ------ Input Options Time Limit: Unbounded
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  ------ 
% 3.73/0.98  Current options:
% 3.73/0.98  ------ 
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  ------ Proving...
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  % SZS status Theorem for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98   Resolution empty clause
% 3.73/0.98  
% 3.73/0.98  % SZS output start CNFRefutation for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  fof(f7,axiom,(
% 3.73/0.98    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f19,plain,(
% 3.73/0.98    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f7])).
% 3.73/0.98  
% 3.73/0.98  fof(f20,plain,(
% 3.73/0.98    ! [X0] : (! [X1,X2] : (k9_relat_1(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> ? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.73/0.98    inference(flattening,[],[f19])).
% 3.73/0.98  
% 3.73/0.98  fof(f28,plain,(
% 3.73/0.98    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X3] : ((r2_hidden(X3,X2) | ! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0)))) & (? [X4] : (k1_funct_1(X0,X4) = X3 & r2_hidden(X4,X1) & r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.73/0.98    inference(nnf_transformation,[],[f20])).
% 3.73/0.98  
% 3.73/0.98  fof(f29,plain,(
% 3.73/0.98    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.73/0.98    inference(rectify,[],[f28])).
% 3.73/0.98  
% 3.73/0.98  fof(f32,plain,(
% 3.73/0.98    ! [X6,X1,X0] : (? [X8] : (k1_funct_1(X0,X8) = X6 & r2_hidden(X8,X1) & r2_hidden(X8,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 & r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f31,plain,(
% 3.73/0.98    ( ! [X3] : (! [X2,X1,X0] : (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) => (k1_funct_1(X0,sK1(X0,X1,X2)) = X3 & r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))))) )),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f30,plain,(
% 3.73/0.98    ! [X2,X1,X0] : (? [X3] : ((! [X4] : (k1_funct_1(X0,X4) != X3 | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(X3,X2)) & (? [X5] : (k1_funct_1(X0,X5) = X3 & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(X3,X2))) => ((! [X4] : (k1_funct_1(X0,X4) != sK0(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & (? [X5] : (k1_funct_1(X0,X5) = sK0(X0,X1,X2) & r2_hidden(X5,X1) & r2_hidden(X5,k1_relat_1(X0))) | r2_hidden(sK0(X0,X1,X2),X2))))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f33,plain,(
% 3.73/0.98    ! [X0] : (! [X1,X2] : ((k9_relat_1(X0,X1) = X2 | ((! [X4] : (k1_funct_1(X0,X4) != sK0(X0,X1,X2) | ~r2_hidden(X4,X1) | ~r2_hidden(X4,k1_relat_1(X0))) | ~r2_hidden(sK0(X0,X1,X2),X2)) & ((k1_funct_1(X0,sK1(X0,X1,X2)) = sK0(X0,X1,X2) & r2_hidden(sK1(X0,X1,X2),X1) & r2_hidden(sK1(X0,X1,X2),k1_relat_1(X0))) | r2_hidden(sK0(X0,X1,X2),X2)))) & (! [X6] : ((r2_hidden(X6,X2) | ! [X7] : (k1_funct_1(X0,X7) != X6 | ~r2_hidden(X7,X1) | ~r2_hidden(X7,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK2(X0,X1,X6)) = X6 & r2_hidden(sK2(X0,X1,X6),X1) & r2_hidden(sK2(X0,X1,X6),k1_relat_1(X0))) | ~r2_hidden(X6,X2))) | k9_relat_1(X0,X1) != X2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f29,f32,f31,f30])).
% 3.73/0.98  
% 3.73/0.98  fof(f44,plain,(
% 3.73/0.98    ( ! [X6,X2,X0,X1] : (r2_hidden(sK2(X0,X1,X6),X1) | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f33])).
% 3.73/0.98  
% 3.73/0.98  fof(f68,plain,(
% 3.73/0.98    ( ! [X6,X0,X1] : (r2_hidden(sK2(X0,X1,X6),X1) | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/0.98    inference(equality_resolution,[],[f44])).
% 3.73/0.98  
% 3.73/0.98  fof(f12,conjecture,(
% 3.73/0.98    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f13,negated_conjecture,(
% 3.73/0.98    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~(! [X4] : ~(k1_funct_1(X3,X4) = X2 & r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))))),
% 3.73/0.98    inference(negated_conjecture,[],[f12])).
% 3.73/0.98  
% 3.73/0.98  fof(f26,plain,(
% 3.73/0.98    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 3.73/0.98    inference(ennf_transformation,[],[f13])).
% 3.73/0.98  
% 3.73/0.98  fof(f27,plain,(
% 3.73/0.98    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 3.73/0.98    inference(flattening,[],[f26])).
% 3.73/0.98  
% 3.73/0.98  fof(f35,plain,(
% 3.73/0.98    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X2 | ~r2_hidden(X4,X0)) & r2_hidden(X2,k2_relset_1(X0,X1,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK6,X4) != sK5 | ~r2_hidden(X4,sK3)) & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6))),
% 3.73/0.98    introduced(choice_axiom,[])).
% 3.73/0.98  
% 3.73/0.98  fof(f36,plain,(
% 3.73/0.98    ! [X4] : (k1_funct_1(sK6,X4) != sK5 | ~r2_hidden(X4,sK3)) & r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_2(sK6,sK3,sK4) & v1_funct_1(sK6)),
% 3.73/0.98    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f27,f35])).
% 3.73/0.98  
% 3.73/0.98  fof(f62,plain,(
% 3.73/0.98    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 3.73/0.98    inference(cnf_transformation,[],[f36])).
% 3.73/0.98  
% 3.73/0.98  fof(f11,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f24,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f11])).
% 3.73/0.98  
% 3.73/0.98  fof(f25,plain,(
% 3.73/0.98    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(flattening,[],[f24])).
% 3.73/0.98  
% 3.73/0.98  fof(f34,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(nnf_transformation,[],[f25])).
% 3.73/0.98  
% 3.73/0.98  fof(f54,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f34])).
% 3.73/0.98  
% 3.73/0.98  fof(f61,plain,(
% 3.73/0.98    v1_funct_2(sK6,sK3,sK4)),
% 3.73/0.98    inference(cnf_transformation,[],[f36])).
% 3.73/0.98  
% 3.73/0.98  fof(f9,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f22,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f9])).
% 3.73/0.98  
% 3.73/0.98  fof(f52,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f22])).
% 3.73/0.98  
% 3.73/0.98  fof(f10,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f23,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f10])).
% 3.73/0.98  
% 3.73/0.98  fof(f53,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f23])).
% 3.73/0.98  
% 3.73/0.98  fof(f63,plain,(
% 3.73/0.98    r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))),
% 3.73/0.98    inference(cnf_transformation,[],[f36])).
% 3.73/0.98  
% 3.73/0.98  fof(f4,axiom,(
% 3.73/0.98    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f17,plain,(
% 3.73/0.98    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 3.73/0.98    inference(ennf_transformation,[],[f4])).
% 3.73/0.98  
% 3.73/0.98  fof(f40,plain,(
% 3.73/0.98    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f17])).
% 3.73/0.98  
% 3.73/0.98  fof(f5,axiom,(
% 3.73/0.98    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f41,plain,(
% 3.73/0.98    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f5])).
% 3.73/0.98  
% 3.73/0.98  fof(f6,axiom,(
% 3.73/0.98    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f18,plain,(
% 3.73/0.98    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 3.73/0.98    inference(ennf_transformation,[],[f6])).
% 3.73/0.98  
% 3.73/0.98  fof(f42,plain,(
% 3.73/0.98    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f18])).
% 3.73/0.98  
% 3.73/0.98  fof(f45,plain,(
% 3.73/0.98    ( ! [X6,X2,X0,X1] : (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 | ~r2_hidden(X6,X2) | k9_relat_1(X0,X1) != X2 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f33])).
% 3.73/0.98  
% 3.73/0.98  fof(f67,plain,(
% 3.73/0.98    ( ! [X6,X0,X1] : (k1_funct_1(X0,sK2(X0,X1,X6)) = X6 | ~r2_hidden(X6,k9_relat_1(X0,X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 3.73/0.98    inference(equality_resolution,[],[f45])).
% 3.73/0.98  
% 3.73/0.98  fof(f60,plain,(
% 3.73/0.98    v1_funct_1(sK6)),
% 3.73/0.98    inference(cnf_transformation,[],[f36])).
% 3.73/0.98  
% 3.73/0.98  fof(f64,plain,(
% 3.73/0.98    ( ! [X4] : (k1_funct_1(sK6,X4) != sK5 | ~r2_hidden(X4,sK3)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f36])).
% 3.73/0.98  
% 3.73/0.98  fof(f58,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f34])).
% 3.73/0.98  
% 3.73/0.98  fof(f72,plain,(
% 3.73/0.98    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 3.73/0.98    inference(equality_resolution,[],[f58])).
% 3.73/0.98  
% 3.73/0.98  fof(f55,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f34])).
% 3.73/0.98  
% 3.73/0.98  fof(f74,plain,(
% 3.73/0.98    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 3.73/0.98    inference(equality_resolution,[],[f55])).
% 3.73/0.98  
% 3.73/0.98  fof(f3,axiom,(
% 3.73/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f14,plain,(
% 3.73/0.98    ! [X0,X1] : (r1_tarski(X0,X1) => m1_subset_1(X0,k1_zfmisc_1(X1)))),
% 3.73/0.98    inference(unused_predicate_definition_removal,[],[f3])).
% 3.73/0.98  
% 3.73/0.98  fof(f16,plain,(
% 3.73/0.98    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1))),
% 3.73/0.98    inference(ennf_transformation,[],[f14])).
% 3.73/0.98  
% 3.73/0.98  fof(f39,plain,(
% 3.73/0.98    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f16])).
% 3.73/0.98  
% 3.73/0.98  fof(f1,axiom,(
% 3.73/0.98    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f37,plain,(
% 3.73/0.98    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 3.73/0.98    inference(cnf_transformation,[],[f1])).
% 3.73/0.98  
% 3.73/0.98  fof(f8,axiom,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f21,plain,(
% 3.73/0.98    ! [X0,X1,X2] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 3.73/0.98    inference(ennf_transformation,[],[f8])).
% 3.73/0.98  
% 3.73/0.98  fof(f51,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f21])).
% 3.73/0.98  
% 3.73/0.98  fof(f2,axiom,(
% 3.73/0.98    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 3.73/0.98    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 3.73/0.98  
% 3.73/0.98  fof(f15,plain,(
% 3.73/0.98    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 3.73/0.98    inference(ennf_transformation,[],[f2])).
% 3.73/0.98  
% 3.73/0.98  fof(f38,plain,(
% 3.73/0.98    ( ! [X2,X0,X1] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 3.73/0.98    inference(cnf_transformation,[],[f15])).
% 3.73/0.98  
% 3.73/0.98  cnf(c_12,plain,
% 3.73/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.73/0.98      | r2_hidden(sK2(X1,X2,X0),X2)
% 3.73/0.98      | ~ v1_funct_1(X1)
% 3.73/0.98      | ~ v1_relat_1(X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f68]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_753,plain,
% 3.73/0.98      ( r2_hidden(X0,k9_relat_1(X1,X2)) != iProver_top
% 3.73/0.98      | r2_hidden(sK2(X1,X2,X0),X2) = iProver_top
% 3.73/0.98      | v1_funct_1(X1) != iProver_top
% 3.73/0.98      | v1_relat_1(X1) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_25,negated_conjecture,
% 3.73/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 3.73/0.98      inference(cnf_transformation,[],[f62]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_740,plain,
% 3.73/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_22,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | k1_relset_1(X1,X2,X0) = X1
% 3.73/0.98      | k1_xboole_0 = X2 ),
% 3.73/0.98      inference(cnf_transformation,[],[f54]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_743,plain,
% 3.73/0.98      ( k1_relset_1(X0,X1,X2) = X0
% 3.73/0.98      | k1_xboole_0 = X1
% 3.73/0.98      | v1_funct_2(X2,X0,X1) != iProver_top
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1230,plain,
% 3.73/0.98      ( k1_relset_1(sK3,sK4,sK6) = sK3
% 3.73/0.98      | sK4 = k1_xboole_0
% 3.73/0.98      | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_740,c_743]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_26,negated_conjecture,
% 3.73/0.98      ( v1_funct_2(sK6,sK3,sK4) ),
% 3.73/0.98      inference(cnf_transformation,[],[f61]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1231,plain,
% 3.73/0.98      ( ~ v1_funct_2(sK6,sK3,sK4)
% 3.73/0.98      | k1_relset_1(sK3,sK4,sK6) = sK3
% 3.73/0.98      | sK4 = k1_xboole_0 ),
% 3.73/0.98      inference(predicate_to_equality_rev,[status(thm)],[c_1230]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1729,plain,
% 3.73/0.98      ( sK4 = k1_xboole_0 | k1_relset_1(sK3,sK4,sK6) = sK3 ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_1230,c_26,c_1231]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1730,plain,
% 3.73/0.98      ( k1_relset_1(sK3,sK4,sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_1729]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_15,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f52]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_750,plain,
% 3.73/0.98      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1393,plain,
% 3.73/0.98      ( k1_relset_1(sK3,sK4,sK6) = k1_relat_1(sK6) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_740,c_750]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1731,plain,
% 3.73/0.98      ( k1_relat_1(sK6) = sK3 | sK4 = k1_xboole_0 ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_1730,c_1393]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_16,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f53]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_749,plain,
% 3.73/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.73/0.98      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1379,plain,
% 3.73/0.98      ( k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_740,c_749]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_24,negated_conjecture,
% 3.73/0.98      ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) ),
% 3.73/0.98      inference(cnf_transformation,[],[f63]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_741,plain,
% 3.73/0.98      ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1548,plain,
% 3.73/0.98      ( r2_hidden(sK5,k2_relat_1(sK6)) = iProver_top ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_1379,c_741]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ v1_relat_1(X1) | v1_relat_1(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f40]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_762,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.73/0.98      | v1_relat_1(X1) != iProver_top
% 3.73/0.98      | v1_relat_1(X0) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1534,plain,
% 3.73/0.98      ( v1_relat_1(k2_zfmisc_1(sK3,sK4)) != iProver_top
% 3.73/0.98      | v1_relat_1(sK6) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_740,c_762]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1079,plain,
% 3.73/0.98      ( ~ v1_relat_1(k2_zfmisc_1(sK3,sK4)) | v1_relat_1(sK6) ),
% 3.73/0.98      inference(resolution,[status(thm)],[c_3,c_25]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4,plain,
% 3.73/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 3.73/0.98      inference(cnf_transformation,[],[f41]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1114,plain,
% 3.73/0.98      ( v1_relat_1(sK6) ),
% 3.73/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_1079,c_4]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1115,plain,
% 3.73/0.98      ( v1_relat_1(sK6) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1114]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1722,plain,
% 3.73/0.98      ( v1_relat_1(sK6) = iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,[status(thm)],[c_1534,c_1115]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5,plain,
% 3.73/0.98      ( ~ v1_relat_1(X0) | k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f42]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_760,plain,
% 3.73/0.98      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
% 3.73/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1727,plain,
% 3.73/0.98      ( k9_relat_1(sK6,k1_relat_1(sK6)) = k2_relat_1(sK6) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1722,c_760]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_11,plain,
% 3.73/0.98      ( ~ r2_hidden(X0,k9_relat_1(X1,X2))
% 3.73/0.98      | ~ v1_funct_1(X1)
% 3.73/0.98      | ~ v1_relat_1(X1)
% 3.73/0.98      | k1_funct_1(X1,sK2(X1,X2,X0)) = X0 ),
% 3.73/0.98      inference(cnf_transformation,[],[f67]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_754,plain,
% 3.73/0.98      ( k1_funct_1(X0,sK2(X0,X1,X2)) = X2
% 3.73/0.98      | r2_hidden(X2,k9_relat_1(X0,X1)) != iProver_top
% 3.73/0.98      | v1_funct_1(X0) != iProver_top
% 3.73/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3269,plain,
% 3.73/0.98      ( k1_funct_1(sK6,sK2(sK6,k1_relat_1(sK6),X0)) = X0
% 3.73/0.98      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top
% 3.73/0.98      | v1_funct_1(sK6) != iProver_top
% 3.73/0.98      | v1_relat_1(sK6) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1727,c_754]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_27,negated_conjecture,
% 3.73/0.98      ( v1_funct_1(sK6) ),
% 3.73/0.98      inference(cnf_transformation,[],[f60]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_28,plain,
% 3.73/0.98      ( v1_funct_1(sK6) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3518,plain,
% 3.73/0.98      ( k1_funct_1(sK6,sK2(sK6,k1_relat_1(sK6),X0)) = X0
% 3.73/0.98      | r2_hidden(X0,k2_relat_1(sK6)) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_3269,c_28,c_1115]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3527,plain,
% 3.73/0.98      ( k1_funct_1(sK6,sK2(sK6,k1_relat_1(sK6),sK5)) = sK5 ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1548,c_3518]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3727,plain,
% 3.73/0.98      ( k1_funct_1(sK6,sK2(sK6,sK3,sK5)) = sK5 | sK4 = k1_xboole_0 ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1731,c_3527]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1890,plain,
% 3.73/0.98      ( k9_relat_1(sK6,sK3) = k2_relat_1(sK6) | sK4 = k1_xboole_0 ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1731,c_1727]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_23,negated_conjecture,
% 3.73/0.98      ( ~ r2_hidden(X0,sK3) | k1_funct_1(sK6,X0) != sK5 ),
% 3.73/0.98      inference(cnf_transformation,[],[f64]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_742,plain,
% 3.73/0.98      ( k1_funct_1(sK6,X0) != sK5 | r2_hidden(X0,sK3) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3728,plain,
% 3.73/0.98      ( r2_hidden(sK2(sK6,k1_relat_1(sK6),sK5),sK3) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_3527,c_742]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3738,plain,
% 3.73/0.98      ( sK4 = k1_xboole_0 | r2_hidden(sK2(sK6,sK3,sK5),sK3) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1731,c_3728]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3861,plain,
% 3.73/0.98      ( sK4 = k1_xboole_0
% 3.73/0.98      | r2_hidden(sK5,k9_relat_1(sK6,sK3)) != iProver_top
% 3.73/0.98      | v1_funct_1(sK6) != iProver_top
% 3.73/0.98      | v1_relat_1(sK6) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_753,c_3738]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3864,plain,
% 3.73/0.98      ( sK4 = k1_xboole_0 | r2_hidden(sK5,k9_relat_1(sK6,sK3)) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_3861,c_28,c_1115]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3870,plain,
% 3.73/0.98      ( sK4 = k1_xboole_0 | r2_hidden(sK5,k2_relat_1(sK6)) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_1890,c_3864]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4008,plain,
% 3.73/0.98      ( sK4 = k1_xboole_0 ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_3727,c_1548,c_3870]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4019,plain,
% 3.73/0.98      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_4008,c_740]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_18,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 3.73/0.98      | k1_xboole_0 = X1
% 3.73/0.98      | k1_xboole_0 = X0 ),
% 3.73/0.98      inference(cnf_transformation,[],[f72]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_747,plain,
% 3.73/0.98      ( k1_xboole_0 = X0
% 3.73/0.98      | k1_xboole_0 = X1
% 3.73/0.98      | v1_funct_2(X0,X1,k1_xboole_0) != iProver_top
% 3.73/0.98      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0))) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4259,plain,
% 3.73/0.98      ( sK3 = k1_xboole_0
% 3.73/0.98      | sK6 = k1_xboole_0
% 3.73/0.98      | v1_funct_2(sK6,sK3,k1_xboole_0) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_4019,c_747]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_29,plain,
% 3.73/0.98      ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_262,plain,( X0 = X0 ),theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_289,plain,
% 3.73/0.98      ( k1_xboole_0 = k1_xboole_0 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_262]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1278,plain,
% 3.73/0.98      ( sK6 = sK6 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_262]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_275,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0,X1,X2)
% 3.73/0.98      | v1_funct_2(X3,X4,X5)
% 3.73/0.98      | X3 != X0
% 3.73/0.98      | X4 != X1
% 3.73/0.98      | X5 != X2 ),
% 3.73/0.98      theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1131,plain,
% 3.73/0.98      ( v1_funct_2(X0,X1,X2)
% 3.73/0.98      | ~ v1_funct_2(sK6,sK3,sK4)
% 3.73/0.98      | X2 != sK4
% 3.73/0.98      | X1 != sK3
% 3.73/0.98      | X0 != sK6 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_275]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1277,plain,
% 3.73/0.98      ( v1_funct_2(sK6,X0,X1)
% 3.73/0.98      | ~ v1_funct_2(sK6,sK3,sK4)
% 3.73/0.98      | X1 != sK4
% 3.73/0.98      | X0 != sK3
% 3.73/0.98      | sK6 != sK6 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1131]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1588,plain,
% 3.73/0.98      ( v1_funct_2(sK6,sK3,X0)
% 3.73/0.98      | ~ v1_funct_2(sK6,sK3,sK4)
% 3.73/0.98      | X0 != sK4
% 3.73/0.98      | sK3 != sK3
% 3.73/0.98      | sK6 != sK6 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1277]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1590,plain,
% 3.73/0.98      ( X0 != sK4
% 3.73/0.98      | sK3 != sK3
% 3.73/0.98      | sK6 != sK6
% 3.73/0.98      | v1_funct_2(sK6,sK3,X0) = iProver_top
% 3.73/0.98      | v1_funct_2(sK6,sK3,sK4) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1588]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1592,plain,
% 3.73/0.98      ( sK3 != sK3
% 3.73/0.98      | sK6 != sK6
% 3.73/0.98      | k1_xboole_0 != sK4
% 3.73/0.98      | v1_funct_2(sK6,sK3,sK4) != iProver_top
% 3.73/0.98      | v1_funct_2(sK6,sK3,k1_xboole_0) = iProver_top ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1590]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1589,plain,
% 3.73/0.98      ( sK3 = sK3 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_262]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_263,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2317,plain,
% 3.73/0.98      ( X0 != X1 | X0 = sK4 | sK4 != X1 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_263]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2318,plain,
% 3.73/0.98      ( sK4 != k1_xboole_0 | k1_xboole_0 = sK4 | k1_xboole_0 != k1_xboole_0 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_2317]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5038,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0 | sK3 = k1_xboole_0 ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_4259,c_29,c_289,c_1278,c_1548,c_1592,c_1589,c_2318,c_3870]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5039,plain,
% 3.73/0.98      ( sK3 = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_5038]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5045,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0
% 3.73/0.98      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_5039,c_4019]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_21,plain,
% 3.73/0.98      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 3.73/0.98      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 3.73/0.98      | k1_relset_1(k1_xboole_0,X1,X0) = k1_xboole_0 ),
% 3.73/0.98      inference(cnf_transformation,[],[f74]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_744,plain,
% 3.73/0.98      ( k1_relset_1(k1_xboole_0,X0,X1) = k1_xboole_0
% 3.73/0.98      | v1_funct_2(X1,k1_xboole_0,X0) != iProver_top
% 3.73/0.98      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5386,plain,
% 3.73/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 3.73/0.98      | sK6 = k1_xboole_0
% 3.73/0.98      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_5045,c_744]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_739,plain,
% 3.73/0.98      ( v1_funct_2(sK6,sK3,sK4) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4020,plain,
% 3.73/0.98      ( v1_funct_2(sK6,sK3,k1_xboole_0) = iProver_top ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_4008,c_739]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5046,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0
% 3.73/0.98      | v1_funct_2(sK6,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_5039,c_4020]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7589,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0
% 3.73/0.98      | k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0 ),
% 3.73/0.98      inference(global_propositional_subsumption,[status(thm)],[c_5386,c_5046]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7590,plain,
% 3.73/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_xboole_0
% 3.73/0.98      | sK6 = k1_xboole_0 ),
% 3.73/0.98      inference(renaming,[status(thm)],[c_7589]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_4017,plain,
% 3.73/0.98      ( k1_relset_1(sK3,k1_xboole_0,sK6) = k1_relat_1(sK6) ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_4008,c_1393]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5044,plain,
% 3.73/0.98      ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK6) = k1_relat_1(sK6)
% 3.73/0.98      | sK6 = k1_xboole_0 ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_5039,c_4017]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7596,plain,
% 3.73/0.98      ( k1_relat_1(sK6) = k1_xboole_0 | sK6 = k1_xboole_0 ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_7590,c_5044]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8569,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0
% 3.73/0.98      | r2_hidden(sK2(sK6,k1_xboole_0,sK5),sK3) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_7596,c_3728]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_31,plain,
% 3.73/0.98      ( r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1092,plain,
% 3.73/0.98      ( ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 3.73/0.98      | k2_relset_1(sK3,sK4,sK6) = k2_relat_1(sK6) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_16]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1218,plain,
% 3.73/0.98      ( sK5 = sK5 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_262]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_265,plain,
% 3.73/0.98      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 3.73/0.98      theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1095,plain,
% 3.73/0.98      ( r2_hidden(X0,X1)
% 3.73/0.98      | ~ r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
% 3.73/0.98      | X1 != k2_relset_1(sK3,sK4,sK6)
% 3.73/0.98      | X0 != sK5 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_265]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1217,plain,
% 3.73/0.98      ( r2_hidden(sK5,X0)
% 3.73/0.98      | ~ r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
% 3.73/0.98      | X0 != k2_relset_1(sK3,sK4,sK6)
% 3.73/0.98      | sK5 != sK5 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1095]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1468,plain,
% 3.73/0.98      ( ~ r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6))
% 3.73/0.98      | r2_hidden(sK5,k9_relat_1(sK6,X0))
% 3.73/0.98      | k9_relat_1(sK6,X0) != k2_relset_1(sK3,sK4,sK6)
% 3.73/0.98      | sK5 != sK5 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1217]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1472,plain,
% 3.73/0.98      ( k9_relat_1(sK6,X0) != k2_relset_1(sK3,sK4,sK6)
% 3.73/0.98      | sK5 != sK5
% 3.73/0.98      | r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) != iProver_top
% 3.73/0.98      | r2_hidden(sK5,k9_relat_1(sK6,X0)) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1468]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1474,plain,
% 3.73/0.98      ( k9_relat_1(sK6,k1_xboole_0) != k2_relset_1(sK3,sK4,sK6)
% 3.73/0.98      | sK5 != sK5
% 3.73/0.98      | r2_hidden(sK5,k2_relset_1(sK3,sK4,sK6)) != iProver_top
% 3.73/0.98      | r2_hidden(sK5,k9_relat_1(sK6,k1_xboole_0)) = iProver_top ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1472]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1865,plain,
% 3.73/0.98      ( r2_hidden(sK2(sK6,X0,sK5),X0)
% 3.73/0.98      | ~ r2_hidden(sK5,k9_relat_1(sK6,X0))
% 3.73/0.98      | ~ v1_funct_1(sK6)
% 3.73/0.98      | ~ v1_relat_1(sK6) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_12]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1866,plain,
% 3.73/0.98      ( r2_hidden(sK2(sK6,X0,sK5),X0) = iProver_top
% 3.73/0.98      | r2_hidden(sK5,k9_relat_1(sK6,X0)) != iProver_top
% 3.73/0.98      | v1_funct_1(sK6) != iProver_top
% 3.73/0.98      | v1_relat_1(sK6) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1865]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1868,plain,
% 3.73/0.98      ( r2_hidden(sK2(sK6,k1_xboole_0,sK5),k1_xboole_0) = iProver_top
% 3.73/0.98      | r2_hidden(sK5,k9_relat_1(sK6,k1_xboole_0)) != iProver_top
% 3.73/0.98      | v1_funct_1(sK6) != iProver_top
% 3.73/0.98      | v1_relat_1(sK6) != iProver_top ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1866]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1459,plain,
% 3.73/0.98      ( X0 != X1
% 3.73/0.98      | X0 = k2_relset_1(sK3,sK4,sK6)
% 3.73/0.98      | k2_relset_1(sK3,sK4,sK6) != X1 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_263]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2585,plain,
% 3.73/0.98      ( X0 = k2_relset_1(sK3,sK4,sK6)
% 3.73/0.98      | X0 != k2_relat_1(sK6)
% 3.73/0.98      | k2_relset_1(sK3,sK4,sK6) != k2_relat_1(sK6) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1459]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3471,plain,
% 3.73/0.98      ( k2_relset_1(sK3,sK4,sK6) != k2_relat_1(sK6)
% 3.73/0.98      | k9_relat_1(sK6,X0) = k2_relset_1(sK3,sK4,sK6)
% 3.73/0.98      | k9_relat_1(sK6,X0) != k2_relat_1(sK6) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_2585]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_3475,plain,
% 3.73/0.98      ( k2_relset_1(sK3,sK4,sK6) != k2_relat_1(sK6)
% 3.73/0.98      | k9_relat_1(sK6,k1_xboole_0) = k2_relset_1(sK3,sK4,sK6)
% 3.73/0.98      | k9_relat_1(sK6,k1_xboole_0) != k2_relat_1(sK6) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_3471]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_5047,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0
% 3.73/0.98      | r2_hidden(sK2(sK6,k1_relat_1(sK6),sK5),k1_xboole_0) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_5039,c_3728]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8568,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0
% 3.73/0.98      | r2_hidden(sK2(sK6,k1_xboole_0,sK5),k1_xboole_0) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_7596,c_5047]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8571,plain,
% 3.73/0.98      ( k9_relat_1(sK6,k1_xboole_0) = k2_relat_1(sK6) | sK6 = k1_xboole_0 ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_7596,c_1727]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8726,plain,
% 3.73/0.98      ( sK6 = k1_xboole_0 ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_8569,c_28,c_25,c_31,c_1092,c_1115,c_1218,c_1474,c_1868,
% 3.73/0.98                 c_3475,c_8568,c_8571]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_738,plain,
% 3.73/0.98      ( v1_funct_1(sK6) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8759,plain,
% 3.73/0.98      ( v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_8726,c_738]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8757,plain,
% 3.73/0.98      ( r2_hidden(sK5,k2_relat_1(k1_xboole_0)) = iProver_top ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_8726,c_1548]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) | ~ r1_tarski(X0,X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f39]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_763,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) = iProver_top
% 3.73/0.98      | r1_tarski(X0,X1) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_0,plain,
% 3.73/0.98      ( r1_tarski(k1_xboole_0,X0) ),
% 3.73/0.98      inference(cnf_transformation,[],[f37]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_765,plain,
% 3.73/0.98      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1378,plain,
% 3.73/0.98      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 3.73/0.98      | r1_tarski(X2,k2_zfmisc_1(X0,X1)) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_763,c_749]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2897,plain,
% 3.73/0.98      ( k2_relset_1(X0,X1,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_765,c_1378]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_14,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) ),
% 3.73/0.98      inference(cnf_transformation,[],[f51]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_751,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.73/0.98      | m1_subset_1(k2_relset_1(X1,X2,X0),k1_zfmisc_1(X2)) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_2900,plain,
% 3.73/0.98      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
% 3.73/0.98      | m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_2897,c_751]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_6873,plain,
% 3.73/0.98      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top
% 3.73/0.98      | r1_tarski(k1_xboole_0,k2_zfmisc_1(X1,X0)) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_763,c_2900]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7036,plain,
% 3.73/0.98      ( m1_subset_1(k2_relat_1(k1_xboole_0),k1_zfmisc_1(X0)) = iProver_top ),
% 3.73/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_6873,c_765]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 3.73/0.98      | ~ r2_hidden(X2,X0)
% 3.73/0.98      | r2_hidden(X2,X1) ),
% 3.73/0.98      inference(cnf_transformation,[],[f38]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_764,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(X1)) != iProver_top
% 3.73/0.98      | r2_hidden(X2,X0) != iProver_top
% 3.73/0.98      | r2_hidden(X2,X1) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_7040,plain,
% 3.73/0.98      ( r2_hidden(X0,X1) = iProver_top
% 3.73/0.98      | r2_hidden(X0,k2_relat_1(k1_xboole_0)) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_7036,c_764]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_10301,plain,
% 3.73/0.98      ( r2_hidden(sK5,X0) = iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_8757,c_7040]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_10633,plain,
% 3.73/0.98      ( k1_funct_1(X0,sK2(X0,X1,sK5)) = sK5
% 3.73/0.98      | v1_funct_1(X0) != iProver_top
% 3.73/0.98      | v1_relat_1(X0) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_10301,c_754]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_12379,plain,
% 3.73/0.98      ( k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,X0,sK5)) = sK5
% 3.73/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_8759,c_10633]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_89,plain,
% 3.73/0.98      ( v1_relat_1(k2_zfmisc_1(X0,X1)) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_91,plain,
% 3.73/0.98      ( v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_89]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1008,plain,
% 3.73/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
% 3.73/0.98      | ~ r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_2]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1009,plain,
% 3.73/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) = iProver_top
% 3.73/0.98      | r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1008]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1011,plain,
% 3.73/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top
% 3.73/0.98      | r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1009]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1013,plain,
% 3.73/0.98      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 3.73/0.98      | v1_relat_1(X0)
% 3.73/0.98      | ~ v1_relat_1(k2_zfmisc_1(X1,X2)) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_3]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1014,plain,
% 3.73/0.98      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 3.73/0.98      | v1_relat_1(X0) = iProver_top
% 3.73/0.98      | v1_relat_1(k2_zfmisc_1(X1,X2)) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1013]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1016,plain,
% 3.73/0.98      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 3.73/0.98      | v1_relat_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != iProver_top
% 3.73/0.98      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1014]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1314,plain,
% 3.73/0.98      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_0]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1315,plain,
% 3.73/0.98      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(X0,k1_xboole_0)) = iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1314]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1317,plain,
% 3.73/0.98      ( r1_tarski(k1_xboole_0,k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1315]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_12384,plain,
% 3.73/0.98      ( k1_funct_1(k1_xboole_0,sK2(k1_xboole_0,X0,sK5)) = sK5 ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_12379,c_91,c_1011,c_1016,c_1317]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_8758,plain,
% 3.73/0.98      ( k1_funct_1(k1_xboole_0,X0) != sK5 | r2_hidden(X0,sK3) != iProver_top ),
% 3.73/0.98      inference(demodulation,[status(thm)],[c_8726,c_742]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_12391,plain,
% 3.73/0.98      ( r2_hidden(sK2(k1_xboole_0,X0,sK5),sK3) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_12384,c_8758]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_12466,plain,
% 3.73/0.98      ( r2_hidden(sK5,k9_relat_1(k1_xboole_0,sK3)) != iProver_top
% 3.73/0.98      | v1_funct_1(k1_xboole_0) != iProver_top
% 3.73/0.98      | v1_relat_1(k1_xboole_0) != iProver_top ),
% 3.73/0.98      inference(superposition,[status(thm)],[c_753,c_12391]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_272,plain,
% 3.73/0.98      ( ~ v1_funct_1(X0) | v1_funct_1(X1) | X1 != X0 ),
% 3.73/0.98      theory(equality) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1046,plain,
% 3.73/0.98      ( v1_funct_1(X0) | ~ v1_funct_1(sK6) | X0 != sK6 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_272]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1047,plain,
% 3.73/0.98      ( X0 != sK6
% 3.73/0.98      | v1_funct_1(X0) = iProver_top
% 3.73/0.98      | v1_funct_1(sK6) != iProver_top ),
% 3.73/0.98      inference(predicate_to_equality,[status(thm)],[c_1046]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1049,plain,
% 3.73/0.98      ( k1_xboole_0 != sK6
% 3.73/0.98      | v1_funct_1(sK6) != iProver_top
% 3.73/0.98      | v1_funct_1(k1_xboole_0) = iProver_top ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1047]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1198,plain,
% 3.73/0.98      ( X0 != X1 | X0 = sK6 | sK6 != X1 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_263]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_1199,plain,
% 3.73/0.98      ( sK6 != k1_xboole_0 | k1_xboole_0 = sK6 | k1_xboole_0 != k1_xboole_0 ),
% 3.73/0.98      inference(instantiation,[status(thm)],[c_1198]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_12476,plain,
% 3.73/0.98      ( r2_hidden(sK5,k9_relat_1(k1_xboole_0,sK3)) != iProver_top ),
% 3.73/0.98      inference(global_propositional_subsumption,
% 3.73/0.98                [status(thm)],
% 3.73/0.98                [c_12466,c_28,c_25,c_31,c_91,c_289,c_1011,c_1016,c_1049,
% 3.73/0.98                 c_1092,c_1115,c_1199,c_1218,c_1317,c_1474,c_1868,c_3475,
% 3.73/0.98                 c_8568,c_8571]) ).
% 3.73/0.98  
% 3.73/0.98  cnf(c_12481,plain,
% 3.73/0.98      ( $false ),
% 3.73/0.98      inference(forward_subsumption_resolution,[status(thm)],[c_12476,c_10301]) ).
% 3.73/0.98  
% 3.73/0.98  
% 3.73/0.98  % SZS output end CNFRefutation for theBenchmark.p
% 3.73/0.98  
% 3.73/0.98  ------                               Statistics
% 3.73/0.98  
% 3.73/0.98  ------ Selected
% 3.73/0.98  
% 3.73/0.98  total_time:                             0.386
% 3.73/0.98  
%------------------------------------------------------------------------------
