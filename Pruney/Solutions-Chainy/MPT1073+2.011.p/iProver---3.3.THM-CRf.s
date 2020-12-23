%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:10:02 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :  141 ( 350 expanded)
%              Number of clauses        :   77 ( 116 expanded)
%              Number of leaves         :   17 (  71 expanded)
%              Depth                    :   20
%              Number of atoms          :  453 (1590 expanded)
%              Number of equality atoms :  173 ( 415 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal clause size      :   16 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
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
    inference(ennf_transformation,[],[f11])).

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
    inference(flattening,[],[f26])).

fof(f41,plain,(
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
    inference(nnf_transformation,[],[f27])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f12,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
     => ~ ( ! [X4] :
              ( m1_subset_1(X4,X1)
             => k1_funct_1(X3,X4) != X0 )
          & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X3,X1,X2)
          & v1_funct_1(X3) )
       => ~ ( ! [X4] :
                ( m1_subset_1(X4,X1)
               => k1_funct_1(X3,X4) != X0 )
            & r2_hidden(X0,k2_relset_1(X1,X2,X3)) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f28,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f29,plain,(
    ? [X0,X1,X2,X3] :
      ( ! [X4] :
          ( k1_funct_1(X3,X4) != X0
          | ~ m1_subset_1(X4,X1) )
      & r2_hidden(X0,k2_relset_1(X1,X2,X3))
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      & v1_funct_2(X3,X1,X2)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f42,plain,
    ( ? [X0,X1,X2,X3] :
        ( ! [X4] :
            ( k1_funct_1(X3,X4) != X0
            | ~ m1_subset_1(X4,X1) )
        & r2_hidden(X0,k2_relset_1(X1,X2,X3))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_2(X3,X1,X2)
        & v1_funct_1(X3) )
   => ( ! [X4] :
          ( k1_funct_1(sK7,X4) != sK4
          | ~ m1_subset_1(X4,sK5) )
      & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_2(sK7,sK5,sK6)
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ! [X4] :
        ( k1_funct_1(sK7,X4) != sK4
        | ~ m1_subset_1(X4,sK5) )
    & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_2(sK7,sK5,sK6)
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f29,f42])).

fof(f69,plain,(
    v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f70,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f43])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = X1
        <=> ! [X2] :
              ( r2_hidden(X2,X1)
            <=> ? [X3] :
                  ( k1_funct_1(X0,X3) = X2
                  & r2_hidden(X3,k1_relat_1(X0)) ) ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X2] :
                ( ( r2_hidden(X2,X1)
                  | ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) ) )
                & ( ? [X3] :
                      ( k1_funct_1(X0,X3) = X2
                      & r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ? [X2] :
                ( ( ! [X3] :
                      ( k1_funct_1(X0,X3) != X2
                      | ~ r2_hidden(X3,k1_relat_1(X0)) )
                  | ~ r2_hidden(X2,X1) )
                & ( ? [X4] :
                      ( k1_funct_1(X0,X4) = X2
                      & r2_hidden(X4,k1_relat_1(X0)) )
                  | r2_hidden(X2,X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ? [X7] :
                      ( k1_funct_1(X0,X7) = X5
                      & r2_hidden(X7,k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(rectify,[],[f35])).

fof(f39,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ( ! [X3] :
                ( k1_funct_1(X0,X3) != X2
                | ~ r2_hidden(X3,k1_relat_1(X0)) )
            | ~ r2_hidden(X2,X1) )
          & ( ? [X4] :
                ( k1_funct_1(X0,X4) = X2
                & r2_hidden(X4,k1_relat_1(X0)) )
            | r2_hidden(X2,X1) ) )
     => ( ( ! [X3] :
              ( k1_funct_1(X0,X3) != sK1(X0,X1)
              | ~ r2_hidden(X3,k1_relat_1(X0)) )
          | ~ r2_hidden(sK1(X0,X1),X1) )
        & ( ? [X4] :
              ( k1_funct_1(X0,X4) = sK1(X0,X1)
              & r2_hidden(X4,k1_relat_1(X0)) )
          | r2_hidden(sK1(X0,X1),X1) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k2_relat_1(X0) = X1
            | ( ( ! [X3] :
                    ( k1_funct_1(X0,X3) != sK1(X0,X1)
                    | ~ r2_hidden(X3,k1_relat_1(X0)) )
                | ~ r2_hidden(sK1(X0,X1),X1) )
              & ( ( k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
                  & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) )
                | r2_hidden(sK1(X0,X1),X1) ) ) )
          & ( ! [X5] :
                ( ( r2_hidden(X5,X1)
                  | ! [X6] :
                      ( k1_funct_1(X0,X6) != X5
                      | ~ r2_hidden(X6,k1_relat_1(X0)) ) )
                & ( ( k1_funct_1(X0,sK3(X0,X5)) = X5
                    & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) )
                  | ~ r2_hidden(X5,X1) ) )
            | k2_relat_1(X0) != X1 ) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f39,f38,f37])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f76,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f68,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f43])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f18,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f43])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f75,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f72,plain,(
    ! [X4] :
      ( k1_funct_1(sK7,X4) != sK4
      | ~ m1_subset_1(X4,sK5) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f30])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f19,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f19])).

fof(f50,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] : ~ r2_hidden(X1,X0) ) ),
    inference(unused_predicate_definition_removal,[],[f1])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] : ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f3,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f48,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_27,negated_conjecture,
    ( v1_funct_2(sK7,sK5,sK6) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_1082,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | sK6 != X2
    | sK5 != X1
    | sK7 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_1083,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_1082])).

cnf(c_26,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_1085,plain,
    ( k1_relset_1(sK5,sK6,sK7) = sK5
    | k1_xboole_0 = sK6 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1083,c_26])).

cnf(c_2161,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_2165,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_2937,plain,
    ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2161,c_2165])).

cnf(c_3101,plain,
    ( k1_relat_1(sK7) = sK5
    | sK6 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1085,c_2937])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f76])).

cnf(c_28,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_410,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_28])).

cnf(c_411,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7))
    | ~ v1_relat_1(sK7) ),
    inference(unflattening,[status(thm)],[c_410])).

cnf(c_2158,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_31,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_412,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_411])).

cnf(c_14,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_2214,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_2250,plain,
    ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | v1_relat_1(sK7) ),
    inference(instantiation,[status(thm)],[c_2214])).

cnf(c_2251,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_relat_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2250])).

cnf(c_2370,plain,
    ( r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2158,c_31,c_412,c_2251])).

cnf(c_2371,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2370])).

cnf(c_5,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_2167,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5])).

cnf(c_2477,plain,
    ( m1_subset_1(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2371,c_2167])).

cnf(c_3162,plain,
    ( sK6 = k1_xboole_0
    | m1_subset_1(sK3(sK7,X0),sK5) = iProver_top
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3101,c_2477])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_2164,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_2935,plain,
    ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
    inference(superposition,[status(thm)],[c_2161,c_2164])).

cnf(c_25,negated_conjecture,
    ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_2162,plain,
    ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3065,plain,
    ( r2_hidden(sK4,k2_relat_1(sK7)) = iProver_top ),
    inference(demodulation,[status(thm)],[c_2935,c_2162])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f75])).

cnf(c_425,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0
    | sK7 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_28])).

cnf(c_426,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK7))
    | ~ v1_relat_1(sK7)
    | k1_funct_1(sK7,sK3(sK7,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_425])).

cnf(c_2157,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_427,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | v1_relat_1(sK7) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_426])).

cnf(c_2310,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | k1_funct_1(sK7,sK3(sK7,X0)) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2157,c_31,c_427,c_2251])).

cnf(c_2311,plain,
    ( k1_funct_1(sK7,sK3(sK7,X0)) = X0
    | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
    inference(renaming,[status(thm)],[c_2310])).

cnf(c_3100,plain,
    ( k1_funct_1(sK7,sK3(sK7,sK4)) = sK4 ),
    inference(superposition,[status(thm)],[c_3065,c_2311])).

cnf(c_24,negated_conjecture,
    ( ~ m1_subset_1(X0,sK5)
    | k1_funct_1(sK7,X0) != sK4 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_2163,plain,
    ( k1_funct_1(sK7,X0) != sK4
    | m1_subset_1(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_3243,plain,
    ( m1_subset_1(sK3(sK7,sK4),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3100,c_2163])).

cnf(c_9968,plain,
    ( sK6 = k1_xboole_0
    | r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3162,c_3243])).

cnf(c_10563,plain,
    ( sK6 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_9968,c_3065])).

cnf(c_2,plain,
    ( r1_tarski(X0,X1)
    | r2_hidden(sK0(X0,X1),X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_2169,plain,
    ( r1_tarski(X0,X1) = iProver_top
    | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_7,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f50])).

cnf(c_341,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_7])).

cnf(c_345,plain,
    ( r1_tarski(k2_relat_1(X0),X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_341,c_14])).

cnf(c_346,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2) ),
    inference(renaming,[status(thm)],[c_345])).

cnf(c_2159,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_346])).

cnf(c_2831,plain,
    ( r1_tarski(k2_relat_1(sK7),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2161,c_2159])).

cnf(c_3,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(X2,X0)
    | r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_2168,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(X2,X0) != iProver_top
    | r2_hidden(X2,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_3060,plain,
    ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(X0,sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2831,c_2168])).

cnf(c_3594,plain,
    ( r1_tarski(k2_relat_1(sK7),X0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK7),X0),sK6) = iProver_top ),
    inference(superposition,[status(thm)],[c_2169,c_3060])).

cnf(c_10572,plain,
    ( r1_tarski(k2_relat_1(sK7),X0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK7),X0),k1_xboole_0) = iProver_top ),
    inference(demodulation,[status(thm)],[c_10563,c_3594])).

cnf(c_10592,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK7),k1_xboole_0),k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_10572])).

cnf(c_1,plain,
    ( r1_tarski(X0,X1)
    | ~ r2_hidden(sK0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_5251,plain,
    ( r1_tarski(k2_relat_1(sK7),X0)
    | ~ r2_hidden(sK0(k2_relat_1(sK7),X0),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_5257,plain,
    ( r1_tarski(k2_relat_1(sK7),X0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK7),X0),X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5251])).

cnf(c_5259,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_xboole_0) = iProver_top
    | r2_hidden(sK0(k2_relat_1(sK7),k1_xboole_0),k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5257])).

cnf(c_2569,plain,
    ( ~ r1_tarski(X0,X1)
    | ~ r2_hidden(sK4,X0)
    | r2_hidden(sK4,X1) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_3957,plain,
    ( ~ r1_tarski(k2_relat_1(sK7),X0)
    | r2_hidden(sK4,X0)
    | ~ r2_hidden(sK4,k2_relat_1(sK7)) ),
    inference(instantiation,[status(thm)],[c_2569])).

cnf(c_3958,plain,
    ( r1_tarski(k2_relat_1(sK7),X0) != iProver_top
    | r2_hidden(sK4,X0) = iProver_top
    | r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3957])).

cnf(c_3960,plain,
    ( r1_tarski(k2_relat_1(sK7),k1_xboole_0) != iProver_top
    | r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top
    | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_3958])).

cnf(c_0,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_4,plain,
    ( v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_330,plain,
    ( ~ r2_hidden(X0,X1)
    | k1_xboole_0 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_4])).

cnf(c_331,plain,
    ( ~ r2_hidden(X0,k1_xboole_0) ),
    inference(unflattening,[status(thm)],[c_330])).

cnf(c_3350,plain,
    ( ~ r2_hidden(sK4,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_331])).

cnf(c_3351,plain,
    ( r2_hidden(sK4,k1_xboole_0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3350])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_10592,c_5259,c_3960,c_3351,c_3065])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 2.71/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.00  
% 2.71/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.71/1.00  
% 2.71/1.00  ------  iProver source info
% 2.71/1.00  
% 2.71/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.71/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.71/1.00  git: non_committed_changes: false
% 2.71/1.00  git: last_make_outside_of_git: false
% 2.71/1.00  
% 2.71/1.00  ------ 
% 2.71/1.00  
% 2.71/1.00  ------ Input Options
% 2.71/1.00  
% 2.71/1.00  --out_options                           all
% 2.71/1.00  --tptp_safe_out                         true
% 2.71/1.00  --problem_path                          ""
% 2.71/1.00  --include_path                          ""
% 2.71/1.00  --clausifier                            res/vclausify_rel
% 2.71/1.00  --clausifier_options                    ""
% 2.71/1.00  --stdin                                 false
% 2.71/1.00  --stats_out                             all
% 2.71/1.00  
% 2.71/1.00  ------ General Options
% 2.71/1.00  
% 2.71/1.00  --fof                                   false
% 2.71/1.00  --time_out_real                         305.
% 2.71/1.00  --time_out_virtual                      -1.
% 2.71/1.00  --symbol_type_check                     false
% 2.71/1.00  --clausify_out                          false
% 2.71/1.00  --sig_cnt_out                           false
% 2.71/1.00  --trig_cnt_out                          false
% 2.71/1.00  --trig_cnt_out_tolerance                1.
% 2.71/1.00  --trig_cnt_out_sk_spl                   false
% 2.71/1.00  --abstr_cl_out                          false
% 2.71/1.00  
% 2.71/1.00  ------ Global Options
% 2.71/1.00  
% 2.71/1.00  --schedule                              default
% 2.71/1.00  --add_important_lit                     false
% 2.71/1.00  --prop_solver_per_cl                    1000
% 2.71/1.00  --min_unsat_core                        false
% 2.71/1.00  --soft_assumptions                      false
% 2.71/1.00  --soft_lemma_size                       3
% 2.71/1.00  --prop_impl_unit_size                   0
% 2.71/1.00  --prop_impl_unit                        []
% 2.71/1.00  --share_sel_clauses                     true
% 2.71/1.00  --reset_solvers                         false
% 2.71/1.00  --bc_imp_inh                            [conj_cone]
% 2.71/1.00  --conj_cone_tolerance                   3.
% 2.71/1.00  --extra_neg_conj                        none
% 2.71/1.00  --large_theory_mode                     true
% 2.71/1.00  --prolific_symb_bound                   200
% 2.71/1.00  --lt_threshold                          2000
% 2.71/1.00  --clause_weak_htbl                      true
% 2.71/1.00  --gc_record_bc_elim                     false
% 2.71/1.00  
% 2.71/1.01  ------ Preprocessing Options
% 2.71/1.01  
% 2.71/1.01  --preprocessing_flag                    true
% 2.71/1.01  --time_out_prep_mult                    0.1
% 2.71/1.01  --splitting_mode                        input
% 2.71/1.01  --splitting_grd                         true
% 2.71/1.01  --splitting_cvd                         false
% 2.71/1.01  --splitting_cvd_svl                     false
% 2.71/1.01  --splitting_nvd                         32
% 2.71/1.01  --sub_typing                            true
% 2.71/1.01  --prep_gs_sim                           true
% 2.71/1.01  --prep_unflatten                        true
% 2.71/1.01  --prep_res_sim                          true
% 2.71/1.01  --prep_upred                            true
% 2.71/1.01  --prep_sem_filter                       exhaustive
% 2.71/1.01  --prep_sem_filter_out                   false
% 2.71/1.01  --pred_elim                             true
% 2.71/1.01  --res_sim_input                         true
% 2.71/1.01  --eq_ax_congr_red                       true
% 2.71/1.01  --pure_diseq_elim                       true
% 2.71/1.01  --brand_transform                       false
% 2.71/1.01  --non_eq_to_eq                          false
% 2.71/1.01  --prep_def_merge                        true
% 2.71/1.01  --prep_def_merge_prop_impl              false
% 2.71/1.01  --prep_def_merge_mbd                    true
% 2.71/1.01  --prep_def_merge_tr_red                 false
% 2.71/1.01  --prep_def_merge_tr_cl                  false
% 2.71/1.01  --smt_preprocessing                     true
% 2.71/1.01  --smt_ac_axioms                         fast
% 2.71/1.01  --preprocessed_out                      false
% 2.71/1.01  --preprocessed_stats                    false
% 2.71/1.01  
% 2.71/1.01  ------ Abstraction refinement Options
% 2.71/1.01  
% 2.71/1.01  --abstr_ref                             []
% 2.71/1.01  --abstr_ref_prep                        false
% 2.71/1.01  --abstr_ref_until_sat                   false
% 2.71/1.01  --abstr_ref_sig_restrict                funpre
% 2.71/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/1.01  --abstr_ref_under                       []
% 2.71/1.01  
% 2.71/1.01  ------ SAT Options
% 2.71/1.01  
% 2.71/1.01  --sat_mode                              false
% 2.71/1.01  --sat_fm_restart_options                ""
% 2.71/1.01  --sat_gr_def                            false
% 2.71/1.01  --sat_epr_types                         true
% 2.71/1.01  --sat_non_cyclic_types                  false
% 2.71/1.01  --sat_finite_models                     false
% 2.71/1.01  --sat_fm_lemmas                         false
% 2.71/1.01  --sat_fm_prep                           false
% 2.71/1.01  --sat_fm_uc_incr                        true
% 2.71/1.01  --sat_out_model                         small
% 2.71/1.01  --sat_out_clauses                       false
% 2.71/1.01  
% 2.71/1.01  ------ QBF Options
% 2.71/1.01  
% 2.71/1.01  --qbf_mode                              false
% 2.71/1.01  --qbf_elim_univ                         false
% 2.71/1.01  --qbf_dom_inst                          none
% 2.71/1.01  --qbf_dom_pre_inst                      false
% 2.71/1.01  --qbf_sk_in                             false
% 2.71/1.01  --qbf_pred_elim                         true
% 2.71/1.01  --qbf_split                             512
% 2.71/1.01  
% 2.71/1.01  ------ BMC1 Options
% 2.71/1.01  
% 2.71/1.01  --bmc1_incremental                      false
% 2.71/1.01  --bmc1_axioms                           reachable_all
% 2.71/1.01  --bmc1_min_bound                        0
% 2.71/1.01  --bmc1_max_bound                        -1
% 2.71/1.01  --bmc1_max_bound_default                -1
% 2.71/1.01  --bmc1_symbol_reachability              true
% 2.71/1.01  --bmc1_property_lemmas                  false
% 2.71/1.01  --bmc1_k_induction                      false
% 2.71/1.01  --bmc1_non_equiv_states                 false
% 2.71/1.01  --bmc1_deadlock                         false
% 2.71/1.01  --bmc1_ucm                              false
% 2.71/1.01  --bmc1_add_unsat_core                   none
% 2.71/1.01  --bmc1_unsat_core_children              false
% 2.71/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/1.01  --bmc1_out_stat                         full
% 2.71/1.01  --bmc1_ground_init                      false
% 2.71/1.01  --bmc1_pre_inst_next_state              false
% 2.71/1.01  --bmc1_pre_inst_state                   false
% 2.71/1.01  --bmc1_pre_inst_reach_state             false
% 2.71/1.01  --bmc1_out_unsat_core                   false
% 2.71/1.01  --bmc1_aig_witness_out                  false
% 2.71/1.01  --bmc1_verbose                          false
% 2.71/1.01  --bmc1_dump_clauses_tptp                false
% 2.71/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.71/1.01  --bmc1_dump_file                        -
% 2.71/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.71/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.71/1.01  --bmc1_ucm_extend_mode                  1
% 2.71/1.01  --bmc1_ucm_init_mode                    2
% 2.71/1.01  --bmc1_ucm_cone_mode                    none
% 2.71/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.71/1.01  --bmc1_ucm_relax_model                  4
% 2.71/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.71/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/1.01  --bmc1_ucm_layered_model                none
% 2.71/1.01  --bmc1_ucm_max_lemma_size               10
% 2.71/1.01  
% 2.71/1.01  ------ AIG Options
% 2.71/1.01  
% 2.71/1.01  --aig_mode                              false
% 2.71/1.01  
% 2.71/1.01  ------ Instantiation Options
% 2.71/1.01  
% 2.71/1.01  --instantiation_flag                    true
% 2.71/1.01  --inst_sos_flag                         true
% 2.71/1.01  --inst_sos_phase                        true
% 2.71/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/1.01  --inst_lit_sel_side                     num_symb
% 2.71/1.01  --inst_solver_per_active                1400
% 2.71/1.01  --inst_solver_calls_frac                1.
% 2.71/1.01  --inst_passive_queue_type               priority_queues
% 2.71/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/1.01  --inst_passive_queues_freq              [25;2]
% 2.71/1.01  --inst_dismatching                      true
% 2.71/1.01  --inst_eager_unprocessed_to_passive     true
% 2.71/1.01  --inst_prop_sim_given                   true
% 2.71/1.01  --inst_prop_sim_new                     false
% 2.71/1.01  --inst_subs_new                         false
% 2.71/1.01  --inst_eq_res_simp                      false
% 2.71/1.01  --inst_subs_given                       false
% 2.71/1.01  --inst_orphan_elimination               true
% 2.71/1.01  --inst_learning_loop_flag               true
% 2.71/1.01  --inst_learning_start                   3000
% 2.71/1.01  --inst_learning_factor                  2
% 2.71/1.01  --inst_start_prop_sim_after_learn       3
% 2.71/1.01  --inst_sel_renew                        solver
% 2.71/1.01  --inst_lit_activity_flag                true
% 2.71/1.01  --inst_restr_to_given                   false
% 2.71/1.01  --inst_activity_threshold               500
% 2.71/1.01  --inst_out_proof                        true
% 2.71/1.01  
% 2.71/1.01  ------ Resolution Options
% 2.71/1.01  
% 2.71/1.01  --resolution_flag                       true
% 2.71/1.01  --res_lit_sel                           adaptive
% 2.71/1.01  --res_lit_sel_side                      none
% 2.71/1.01  --res_ordering                          kbo
% 2.71/1.01  --res_to_prop_solver                    active
% 2.71/1.01  --res_prop_simpl_new                    false
% 2.71/1.01  --res_prop_simpl_given                  true
% 2.71/1.01  --res_passive_queue_type                priority_queues
% 2.71/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/1.01  --res_passive_queues_freq               [15;5]
% 2.71/1.01  --res_forward_subs                      full
% 2.71/1.01  --res_backward_subs                     full
% 2.71/1.01  --res_forward_subs_resolution           true
% 2.71/1.01  --res_backward_subs_resolution          true
% 2.71/1.01  --res_orphan_elimination                true
% 2.71/1.01  --res_time_limit                        2.
% 2.71/1.01  --res_out_proof                         true
% 2.71/1.01  
% 2.71/1.01  ------ Superposition Options
% 2.71/1.01  
% 2.71/1.01  --superposition_flag                    true
% 2.71/1.01  --sup_passive_queue_type                priority_queues
% 2.71/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.71/1.01  --demod_completeness_check              fast
% 2.71/1.01  --demod_use_ground                      true
% 2.71/1.01  --sup_to_prop_solver                    passive
% 2.71/1.01  --sup_prop_simpl_new                    true
% 2.71/1.01  --sup_prop_simpl_given                  true
% 2.71/1.01  --sup_fun_splitting                     true
% 2.71/1.01  --sup_smt_interval                      50000
% 2.71/1.01  
% 2.71/1.01  ------ Superposition Simplification Setup
% 2.71/1.01  
% 2.71/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.71/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.71/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.71/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.71/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.71/1.01  --sup_immed_triv                        [TrivRules]
% 2.71/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/1.01  --sup_immed_bw_main                     []
% 2.71/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.71/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/1.01  --sup_input_bw                          []
% 2.71/1.01  
% 2.71/1.01  ------ Combination Options
% 2.71/1.01  
% 2.71/1.01  --comb_res_mult                         3
% 2.71/1.01  --comb_sup_mult                         2
% 2.71/1.01  --comb_inst_mult                        10
% 2.71/1.01  
% 2.71/1.01  ------ Debug Options
% 2.71/1.01  
% 2.71/1.01  --dbg_backtrace                         false
% 2.71/1.01  --dbg_dump_prop_clauses                 false
% 2.71/1.01  --dbg_dump_prop_clauses_file            -
% 2.71/1.01  --dbg_out_stat                          false
% 2.71/1.01  ------ Parsing...
% 2.71/1.01  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.71/1.01  
% 2.71/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 2.71/1.01  
% 2.71/1.01  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.71/1.01  
% 2.71/1.01  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.71/1.01  ------ Proving...
% 2.71/1.01  ------ Problem Properties 
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  clauses                                 21
% 2.71/1.01  conjectures                             3
% 2.71/1.01  EPR                                     3
% 2.71/1.01  Horn                                    16
% 2.71/1.01  unary                                   3
% 2.71/1.01  binary                                  9
% 2.71/1.01  lits                                    53
% 2.71/1.01  lits eq                                 16
% 2.71/1.01  fd_pure                                 0
% 2.71/1.01  fd_pseudo                               0
% 2.71/1.01  fd_cond                                 3
% 2.71/1.01  fd_pseudo_cond                          0
% 2.71/1.01  AC symbols                              0
% 2.71/1.01  
% 2.71/1.01  ------ Schedule dynamic 5 is on 
% 2.71/1.01  
% 2.71/1.01  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  ------ 
% 2.71/1.01  Current options:
% 2.71/1.01  ------ 
% 2.71/1.01  
% 2.71/1.01  ------ Input Options
% 2.71/1.01  
% 2.71/1.01  --out_options                           all
% 2.71/1.01  --tptp_safe_out                         true
% 2.71/1.01  --problem_path                          ""
% 2.71/1.01  --include_path                          ""
% 2.71/1.01  --clausifier                            res/vclausify_rel
% 2.71/1.01  --clausifier_options                    ""
% 2.71/1.01  --stdin                                 false
% 2.71/1.01  --stats_out                             all
% 2.71/1.01  
% 2.71/1.01  ------ General Options
% 2.71/1.01  
% 2.71/1.01  --fof                                   false
% 2.71/1.01  --time_out_real                         305.
% 2.71/1.01  --time_out_virtual                      -1.
% 2.71/1.01  --symbol_type_check                     false
% 2.71/1.01  --clausify_out                          false
% 2.71/1.01  --sig_cnt_out                           false
% 2.71/1.01  --trig_cnt_out                          false
% 2.71/1.01  --trig_cnt_out_tolerance                1.
% 2.71/1.01  --trig_cnt_out_sk_spl                   false
% 2.71/1.01  --abstr_cl_out                          false
% 2.71/1.01  
% 2.71/1.01  ------ Global Options
% 2.71/1.01  
% 2.71/1.01  --schedule                              default
% 2.71/1.01  --add_important_lit                     false
% 2.71/1.01  --prop_solver_per_cl                    1000
% 2.71/1.01  --min_unsat_core                        false
% 2.71/1.01  --soft_assumptions                      false
% 2.71/1.01  --soft_lemma_size                       3
% 2.71/1.01  --prop_impl_unit_size                   0
% 2.71/1.01  --prop_impl_unit                        []
% 2.71/1.01  --share_sel_clauses                     true
% 2.71/1.01  --reset_solvers                         false
% 2.71/1.01  --bc_imp_inh                            [conj_cone]
% 2.71/1.01  --conj_cone_tolerance                   3.
% 2.71/1.01  --extra_neg_conj                        none
% 2.71/1.01  --large_theory_mode                     true
% 2.71/1.01  --prolific_symb_bound                   200
% 2.71/1.01  --lt_threshold                          2000
% 2.71/1.01  --clause_weak_htbl                      true
% 2.71/1.01  --gc_record_bc_elim                     false
% 2.71/1.01  
% 2.71/1.01  ------ Preprocessing Options
% 2.71/1.01  
% 2.71/1.01  --preprocessing_flag                    true
% 2.71/1.01  --time_out_prep_mult                    0.1
% 2.71/1.01  --splitting_mode                        input
% 2.71/1.01  --splitting_grd                         true
% 2.71/1.01  --splitting_cvd                         false
% 2.71/1.01  --splitting_cvd_svl                     false
% 2.71/1.01  --splitting_nvd                         32
% 2.71/1.01  --sub_typing                            true
% 2.71/1.01  --prep_gs_sim                           true
% 2.71/1.01  --prep_unflatten                        true
% 2.71/1.01  --prep_res_sim                          true
% 2.71/1.01  --prep_upred                            true
% 2.71/1.01  --prep_sem_filter                       exhaustive
% 2.71/1.01  --prep_sem_filter_out                   false
% 2.71/1.01  --pred_elim                             true
% 2.71/1.01  --res_sim_input                         true
% 2.71/1.01  --eq_ax_congr_red                       true
% 2.71/1.01  --pure_diseq_elim                       true
% 2.71/1.01  --brand_transform                       false
% 2.71/1.01  --non_eq_to_eq                          false
% 2.71/1.01  --prep_def_merge                        true
% 2.71/1.01  --prep_def_merge_prop_impl              false
% 2.71/1.01  --prep_def_merge_mbd                    true
% 2.71/1.01  --prep_def_merge_tr_red                 false
% 2.71/1.01  --prep_def_merge_tr_cl                  false
% 2.71/1.01  --smt_preprocessing                     true
% 2.71/1.01  --smt_ac_axioms                         fast
% 2.71/1.01  --preprocessed_out                      false
% 2.71/1.01  --preprocessed_stats                    false
% 2.71/1.01  
% 2.71/1.01  ------ Abstraction refinement Options
% 2.71/1.01  
% 2.71/1.01  --abstr_ref                             []
% 2.71/1.01  --abstr_ref_prep                        false
% 2.71/1.01  --abstr_ref_until_sat                   false
% 2.71/1.01  --abstr_ref_sig_restrict                funpre
% 2.71/1.01  --abstr_ref_af_restrict_to_split_sk     false
% 2.71/1.01  --abstr_ref_under                       []
% 2.71/1.01  
% 2.71/1.01  ------ SAT Options
% 2.71/1.01  
% 2.71/1.01  --sat_mode                              false
% 2.71/1.01  --sat_fm_restart_options                ""
% 2.71/1.01  --sat_gr_def                            false
% 2.71/1.01  --sat_epr_types                         true
% 2.71/1.01  --sat_non_cyclic_types                  false
% 2.71/1.01  --sat_finite_models                     false
% 2.71/1.01  --sat_fm_lemmas                         false
% 2.71/1.01  --sat_fm_prep                           false
% 2.71/1.01  --sat_fm_uc_incr                        true
% 2.71/1.01  --sat_out_model                         small
% 2.71/1.01  --sat_out_clauses                       false
% 2.71/1.01  
% 2.71/1.01  ------ QBF Options
% 2.71/1.01  
% 2.71/1.01  --qbf_mode                              false
% 2.71/1.01  --qbf_elim_univ                         false
% 2.71/1.01  --qbf_dom_inst                          none
% 2.71/1.01  --qbf_dom_pre_inst                      false
% 2.71/1.01  --qbf_sk_in                             false
% 2.71/1.01  --qbf_pred_elim                         true
% 2.71/1.01  --qbf_split                             512
% 2.71/1.01  
% 2.71/1.01  ------ BMC1 Options
% 2.71/1.01  
% 2.71/1.01  --bmc1_incremental                      false
% 2.71/1.01  --bmc1_axioms                           reachable_all
% 2.71/1.01  --bmc1_min_bound                        0
% 2.71/1.01  --bmc1_max_bound                        -1
% 2.71/1.01  --bmc1_max_bound_default                -1
% 2.71/1.01  --bmc1_symbol_reachability              true
% 2.71/1.01  --bmc1_property_lemmas                  false
% 2.71/1.01  --bmc1_k_induction                      false
% 2.71/1.01  --bmc1_non_equiv_states                 false
% 2.71/1.01  --bmc1_deadlock                         false
% 2.71/1.01  --bmc1_ucm                              false
% 2.71/1.01  --bmc1_add_unsat_core                   none
% 2.71/1.01  --bmc1_unsat_core_children              false
% 2.71/1.01  --bmc1_unsat_core_extrapolate_axioms    false
% 2.71/1.01  --bmc1_out_stat                         full
% 2.71/1.01  --bmc1_ground_init                      false
% 2.71/1.01  --bmc1_pre_inst_next_state              false
% 2.71/1.01  --bmc1_pre_inst_state                   false
% 2.71/1.01  --bmc1_pre_inst_reach_state             false
% 2.71/1.01  --bmc1_out_unsat_core                   false
% 2.71/1.01  --bmc1_aig_witness_out                  false
% 2.71/1.01  --bmc1_verbose                          false
% 2.71/1.01  --bmc1_dump_clauses_tptp                false
% 2.71/1.01  --bmc1_dump_unsat_core_tptp             false
% 2.71/1.01  --bmc1_dump_file                        -
% 2.71/1.01  --bmc1_ucm_expand_uc_limit              128
% 2.71/1.01  --bmc1_ucm_n_expand_iterations          6
% 2.71/1.01  --bmc1_ucm_extend_mode                  1
% 2.71/1.01  --bmc1_ucm_init_mode                    2
% 2.71/1.01  --bmc1_ucm_cone_mode                    none
% 2.71/1.01  --bmc1_ucm_reduced_relation_type        0
% 2.71/1.01  --bmc1_ucm_relax_model                  4
% 2.71/1.01  --bmc1_ucm_full_tr_after_sat            true
% 2.71/1.01  --bmc1_ucm_expand_neg_assumptions       false
% 2.71/1.01  --bmc1_ucm_layered_model                none
% 2.71/1.01  --bmc1_ucm_max_lemma_size               10
% 2.71/1.01  
% 2.71/1.01  ------ AIG Options
% 2.71/1.01  
% 2.71/1.01  --aig_mode                              false
% 2.71/1.01  
% 2.71/1.01  ------ Instantiation Options
% 2.71/1.01  
% 2.71/1.01  --instantiation_flag                    true
% 2.71/1.01  --inst_sos_flag                         true
% 2.71/1.01  --inst_sos_phase                        true
% 2.71/1.01  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.71/1.01  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.71/1.01  --inst_lit_sel_side                     none
% 2.71/1.01  --inst_solver_per_active                1400
% 2.71/1.01  --inst_solver_calls_frac                1.
% 2.71/1.01  --inst_passive_queue_type               priority_queues
% 2.71/1.01  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.71/1.01  --inst_passive_queues_freq              [25;2]
% 2.71/1.01  --inst_dismatching                      true
% 2.71/1.01  --inst_eager_unprocessed_to_passive     true
% 2.71/1.01  --inst_prop_sim_given                   true
% 2.71/1.01  --inst_prop_sim_new                     false
% 2.71/1.01  --inst_subs_new                         false
% 2.71/1.01  --inst_eq_res_simp                      false
% 2.71/1.01  --inst_subs_given                       false
% 2.71/1.01  --inst_orphan_elimination               true
% 2.71/1.01  --inst_learning_loop_flag               true
% 2.71/1.01  --inst_learning_start                   3000
% 2.71/1.01  --inst_learning_factor                  2
% 2.71/1.01  --inst_start_prop_sim_after_learn       3
% 2.71/1.01  --inst_sel_renew                        solver
% 2.71/1.01  --inst_lit_activity_flag                true
% 2.71/1.01  --inst_restr_to_given                   false
% 2.71/1.01  --inst_activity_threshold               500
% 2.71/1.01  --inst_out_proof                        true
% 2.71/1.01  
% 2.71/1.01  ------ Resolution Options
% 2.71/1.01  
% 2.71/1.01  --resolution_flag                       false
% 2.71/1.01  --res_lit_sel                           adaptive
% 2.71/1.01  --res_lit_sel_side                      none
% 2.71/1.01  --res_ordering                          kbo
% 2.71/1.01  --res_to_prop_solver                    active
% 2.71/1.01  --res_prop_simpl_new                    false
% 2.71/1.01  --res_prop_simpl_given                  true
% 2.71/1.01  --res_passive_queue_type                priority_queues
% 2.71/1.01  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.71/1.01  --res_passive_queues_freq               [15;5]
% 2.71/1.01  --res_forward_subs                      full
% 2.71/1.01  --res_backward_subs                     full
% 2.71/1.01  --res_forward_subs_resolution           true
% 2.71/1.01  --res_backward_subs_resolution          true
% 2.71/1.01  --res_orphan_elimination                true
% 2.71/1.01  --res_time_limit                        2.
% 2.71/1.01  --res_out_proof                         true
% 2.71/1.01  
% 2.71/1.01  ------ Superposition Options
% 2.71/1.01  
% 2.71/1.01  --superposition_flag                    true
% 2.71/1.01  --sup_passive_queue_type                priority_queues
% 2.71/1.01  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.71/1.01  --sup_passive_queues_freq               [8;1;4]
% 2.71/1.01  --demod_completeness_check              fast
% 2.71/1.01  --demod_use_ground                      true
% 2.71/1.01  --sup_to_prop_solver                    passive
% 2.71/1.01  --sup_prop_simpl_new                    true
% 2.71/1.01  --sup_prop_simpl_given                  true
% 2.71/1.01  --sup_fun_splitting                     true
% 2.71/1.01  --sup_smt_interval                      50000
% 2.71/1.01  
% 2.71/1.01  ------ Superposition Simplification Setup
% 2.71/1.01  
% 2.71/1.01  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 2.71/1.01  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 2.71/1.01  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 2.71/1.01  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 2.71/1.01  --sup_full_triv                         [TrivRules;PropSubs]
% 2.71/1.01  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 2.71/1.01  --sup_full_bw                           [BwDemod;BwSubsumption]
% 2.71/1.01  --sup_immed_triv                        [TrivRules]
% 2.71/1.01  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/1.01  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/1.01  --sup_immed_bw_main                     []
% 2.71/1.01  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 2.71/1.01  --sup_input_triv                        [Unflattening;TrivRules]
% 2.71/1.01  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 2.71/1.01  --sup_input_bw                          []
% 2.71/1.01  
% 2.71/1.01  ------ Combination Options
% 2.71/1.01  
% 2.71/1.01  --comb_res_mult                         3
% 2.71/1.01  --comb_sup_mult                         2
% 2.71/1.01  --comb_inst_mult                        10
% 2.71/1.01  
% 2.71/1.01  ------ Debug Options
% 2.71/1.01  
% 2.71/1.01  --dbg_backtrace                         false
% 2.71/1.01  --dbg_dump_prop_clauses                 false
% 2.71/1.01  --dbg_dump_prop_clauses_file            -
% 2.71/1.01  --dbg_out_stat                          false
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  ------ Proving...
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  % SZS status Theorem for theBenchmark.p
% 2.71/1.01  
% 2.71/1.01  % SZS output start CNFRefutation for theBenchmark.p
% 2.71/1.01  
% 2.71/1.01  fof(f11,axiom,(
% 2.71/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 2.71/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f26,plain,(
% 2.71/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/1.01    inference(ennf_transformation,[],[f11])).
% 2.71/1.01  
% 2.71/1.01  fof(f27,plain,(
% 2.71/1.01    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/1.01    inference(flattening,[],[f26])).
% 2.71/1.01  
% 2.71/1.01  fof(f41,plain,(
% 2.71/1.01    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/1.01    inference(nnf_transformation,[],[f27])).
% 2.71/1.01  
% 2.71/1.01  fof(f62,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/1.01    inference(cnf_transformation,[],[f41])).
% 2.71/1.01  
% 2.71/1.01  fof(f12,conjecture,(
% 2.71/1.01    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 2.71/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f13,negated_conjecture,(
% 2.71/1.01    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => ~(! [X4] : (m1_subset_1(X4,X1) => k1_funct_1(X3,X4) != X0) & r2_hidden(X0,k2_relset_1(X1,X2,X3))))),
% 2.71/1.01    inference(negated_conjecture,[],[f12])).
% 2.71/1.01  
% 2.71/1.01  fof(f28,plain,(
% 2.71/1.01    ? [X0,X1,X2,X3] : ((! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)))),
% 2.71/1.01    inference(ennf_transformation,[],[f13])).
% 2.71/1.01  
% 2.71/1.01  fof(f29,plain,(
% 2.71/1.01    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3))),
% 2.71/1.01    inference(flattening,[],[f28])).
% 2.71/1.01  
% 2.71/1.01  fof(f42,plain,(
% 2.71/1.01    ? [X0,X1,X2,X3] : (! [X4] : (k1_funct_1(X3,X4) != X0 | ~m1_subset_1(X4,X1)) & r2_hidden(X0,k2_relset_1(X1,X2,X3)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X3,X1,X2) & v1_funct_1(X3)) => (! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7))),
% 2.71/1.01    introduced(choice_axiom,[])).
% 2.71/1.01  
% 2.71/1.01  fof(f43,plain,(
% 2.71/1.01    ! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) & r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) & v1_funct_2(sK7,sK5,sK6) & v1_funct_1(sK7)),
% 2.71/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f29,f42])).
% 2.71/1.01  
% 2.71/1.01  fof(f69,plain,(
% 2.71/1.01    v1_funct_2(sK7,sK5,sK6)),
% 2.71/1.01    inference(cnf_transformation,[],[f43])).
% 2.71/1.01  
% 2.71/1.01  fof(f70,plain,(
% 2.71/1.01    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))),
% 2.71/1.01    inference(cnf_transformation,[],[f43])).
% 2.71/1.01  
% 2.71/1.01  fof(f9,axiom,(
% 2.71/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 2.71/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f24,plain,(
% 2.71/1.01    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/1.01    inference(ennf_transformation,[],[f9])).
% 2.71/1.01  
% 2.71/1.01  fof(f60,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/1.01    inference(cnf_transformation,[],[f24])).
% 2.71/1.01  
% 2.71/1.01  fof(f6,axiom,(
% 2.71/1.01    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 2.71/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f20,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.71/1.01    inference(ennf_transformation,[],[f6])).
% 2.71/1.01  
% 2.71/1.01  fof(f21,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/1.01    inference(flattening,[],[f20])).
% 2.71/1.01  
% 2.71/1.01  fof(f35,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/1.01    inference(nnf_transformation,[],[f21])).
% 2.71/1.01  
% 2.71/1.01  fof(f36,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/1.01    inference(rectify,[],[f35])).
% 2.71/1.01  
% 2.71/1.01  fof(f39,plain,(
% 2.71/1.01    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 2.71/1.01    introduced(choice_axiom,[])).
% 2.71/1.01  
% 2.71/1.01  fof(f38,plain,(
% 2.71/1.01    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 2.71/1.01    introduced(choice_axiom,[])).
% 2.71/1.01  
% 2.71/1.01  fof(f37,plain,(
% 2.71/1.01    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 2.71/1.01    introduced(choice_axiom,[])).
% 2.71/1.01  
% 2.71/1.01  fof(f40,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.71/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f36,f39,f38,f37])).
% 2.71/1.01  
% 2.71/1.01  fof(f52,plain,(
% 2.71/1.01    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f40])).
% 2.71/1.01  
% 2.71/1.01  fof(f76,plain,(
% 2.71/1.01    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/1.01    inference(equality_resolution,[],[f52])).
% 2.71/1.01  
% 2.71/1.01  fof(f68,plain,(
% 2.71/1.01    v1_funct_1(sK7)),
% 2.71/1.01    inference(cnf_transformation,[],[f43])).
% 2.71/1.01  
% 2.71/1.01  fof(f7,axiom,(
% 2.71/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.71/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f22,plain,(
% 2.71/1.01    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/1.01    inference(ennf_transformation,[],[f7])).
% 2.71/1.01  
% 2.71/1.01  fof(f58,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/1.01    inference(cnf_transformation,[],[f22])).
% 2.71/1.01  
% 2.71/1.01  fof(f4,axiom,(
% 2.71/1.01    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.71/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f18,plain,(
% 2.71/1.01    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.71/1.01    inference(ennf_transformation,[],[f4])).
% 2.71/1.01  
% 2.71/1.01  fof(f49,plain,(
% 2.71/1.01    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f18])).
% 2.71/1.01  
% 2.71/1.01  fof(f10,axiom,(
% 2.71/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 2.71/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f25,plain,(
% 2.71/1.01    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/1.01    inference(ennf_transformation,[],[f10])).
% 2.71/1.01  
% 2.71/1.01  fof(f61,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/1.01    inference(cnf_transformation,[],[f25])).
% 2.71/1.01  
% 2.71/1.01  fof(f71,plain,(
% 2.71/1.01    r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7))),
% 2.71/1.01    inference(cnf_transformation,[],[f43])).
% 2.71/1.01  
% 2.71/1.01  fof(f53,plain,(
% 2.71/1.01    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f40])).
% 2.71/1.01  
% 2.71/1.01  fof(f75,plain,(
% 2.71/1.01    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.71/1.01    inference(equality_resolution,[],[f53])).
% 2.71/1.01  
% 2.71/1.01  fof(f72,plain,(
% 2.71/1.01    ( ! [X4] : (k1_funct_1(sK7,X4) != sK4 | ~m1_subset_1(X4,sK5)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f43])).
% 2.71/1.01  
% 2.71/1.01  fof(f2,axiom,(
% 2.71/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 2.71/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f17,plain,(
% 2.71/1.01    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 2.71/1.01    inference(ennf_transformation,[],[f2])).
% 2.71/1.01  
% 2.71/1.01  fof(f30,plain,(
% 2.71/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 2.71/1.01    inference(nnf_transformation,[],[f17])).
% 2.71/1.01  
% 2.71/1.01  fof(f31,plain,(
% 2.71/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.71/1.01    inference(rectify,[],[f30])).
% 2.71/1.01  
% 2.71/1.01  fof(f32,plain,(
% 2.71/1.01    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 2.71/1.01    introduced(choice_axiom,[])).
% 2.71/1.01  
% 2.71/1.01  fof(f33,plain,(
% 2.71/1.01    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 2.71/1.01    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f31,f32])).
% 2.71/1.01  
% 2.71/1.01  fof(f46,plain,(
% 2.71/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f33])).
% 2.71/1.01  
% 2.71/1.01  fof(f8,axiom,(
% 2.71/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.71/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f15,plain,(
% 2.71/1.01    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 2.71/1.01    inference(pure_predicate_removal,[],[f8])).
% 2.71/1.01  
% 2.71/1.01  fof(f23,plain,(
% 2.71/1.01    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.71/1.01    inference(ennf_transformation,[],[f15])).
% 2.71/1.01  
% 2.71/1.01  fof(f59,plain,(
% 2.71/1.01    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.71/1.01    inference(cnf_transformation,[],[f23])).
% 2.71/1.01  
% 2.71/1.01  fof(f5,axiom,(
% 2.71/1.01    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 2.71/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f19,plain,(
% 2.71/1.01    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 2.71/1.01    inference(ennf_transformation,[],[f5])).
% 2.71/1.01  
% 2.71/1.01  fof(f34,plain,(
% 2.71/1.01    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 2.71/1.01    inference(nnf_transformation,[],[f19])).
% 2.71/1.01  
% 2.71/1.01  fof(f50,plain,(
% 2.71/1.01    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f34])).
% 2.71/1.01  
% 2.71/1.01  fof(f45,plain,(
% 2.71/1.01    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f33])).
% 2.71/1.01  
% 2.71/1.01  fof(f47,plain,(
% 2.71/1.01    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f33])).
% 2.71/1.01  
% 2.71/1.01  fof(f1,axiom,(
% 2.71/1.01    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.71/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f14,plain,(
% 2.71/1.01    ! [X0] : (v1_xboole_0(X0) => ! [X1] : ~r2_hidden(X1,X0))),
% 2.71/1.01    inference(unused_predicate_definition_removal,[],[f1])).
% 2.71/1.01  
% 2.71/1.01  fof(f16,plain,(
% 2.71/1.01    ! [X0] : (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0))),
% 2.71/1.01    inference(ennf_transformation,[],[f14])).
% 2.71/1.01  
% 2.71/1.01  fof(f44,plain,(
% 2.71/1.01    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~v1_xboole_0(X0)) )),
% 2.71/1.01    inference(cnf_transformation,[],[f16])).
% 2.71/1.01  
% 2.71/1.01  fof(f3,axiom,(
% 2.71/1.01    v1_xboole_0(k1_xboole_0)),
% 2.71/1.01    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.71/1.01  
% 2.71/1.01  fof(f48,plain,(
% 2.71/1.01    v1_xboole_0(k1_xboole_0)),
% 2.71/1.01    inference(cnf_transformation,[],[f3])).
% 2.71/1.01  
% 2.71/1.01  cnf(c_23,plain,
% 2.71/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.71/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.71/1.01      | k1_xboole_0 = X2 ),
% 2.71/1.01      inference(cnf_transformation,[],[f62]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_27,negated_conjecture,
% 2.71/1.01      ( v1_funct_2(sK7,sK5,sK6) ),
% 2.71/1.01      inference(cnf_transformation,[],[f69]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_1082,plain,
% 2.71/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/1.01      | k1_relset_1(X1,X2,X0) = X1
% 2.71/1.01      | sK6 != X2
% 2.71/1.01      | sK5 != X1
% 2.71/1.01      | sK7 != X0
% 2.71/1.01      | k1_xboole_0 = X2 ),
% 2.71/1.01      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_1083,plain,
% 2.71/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.71/1.01      | k1_relset_1(sK5,sK6,sK7) = sK5
% 2.71/1.01      | k1_xboole_0 = sK6 ),
% 2.71/1.01      inference(unflattening,[status(thm)],[c_1082]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_26,negated_conjecture,
% 2.71/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
% 2.71/1.01      inference(cnf_transformation,[],[f70]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_1085,plain,
% 2.71/1.01      ( k1_relset_1(sK5,sK6,sK7) = sK5 | k1_xboole_0 = sK6 ),
% 2.71/1.01      inference(global_propositional_subsumption,
% 2.71/1.01                [status(thm)],
% 2.71/1.01                [c_1083,c_26]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2161,plain,
% 2.71/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_16,plain,
% 2.71/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/1.01      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 2.71/1.01      inference(cnf_transformation,[],[f60]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2165,plain,
% 2.71/1.01      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 2.71/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2937,plain,
% 2.71/1.01      ( k1_relset_1(sK5,sK6,sK7) = k1_relat_1(sK7) ),
% 2.71/1.01      inference(superposition,[status(thm)],[c_2161,c_2165]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3101,plain,
% 2.71/1.01      ( k1_relat_1(sK7) = sK5 | sK6 = k1_xboole_0 ),
% 2.71/1.01      inference(superposition,[status(thm)],[c_1085,c_2937]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_13,plain,
% 2.71/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.71/1.01      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 2.71/1.01      | ~ v1_funct_1(X1)
% 2.71/1.01      | ~ v1_relat_1(X1) ),
% 2.71/1.01      inference(cnf_transformation,[],[f76]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_28,negated_conjecture,
% 2.71/1.01      ( v1_funct_1(sK7) ),
% 2.71/1.01      inference(cnf_transformation,[],[f68]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_410,plain,
% 2.71/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.71/1.01      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 2.71/1.01      | ~ v1_relat_1(X1)
% 2.71/1.01      | sK7 != X1 ),
% 2.71/1.01      inference(resolution_lifted,[status(thm)],[c_13,c_28]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_411,plain,
% 2.71/1.01      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 2.71/1.01      | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7))
% 2.71/1.01      | ~ v1_relat_1(sK7) ),
% 2.71/1.01      inference(unflattening,[status(thm)],[c_410]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2158,plain,
% 2.71/1.01      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 2.71/1.01      | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 2.71/1.01      | v1_relat_1(sK7) != iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_31,plain,
% 2.71/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_412,plain,
% 2.71/1.01      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 2.71/1.01      | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 2.71/1.01      | v1_relat_1(sK7) != iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_411]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_14,plain,
% 2.71/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/1.01      | v1_relat_1(X0) ),
% 2.71/1.01      inference(cnf_transformation,[],[f58]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2214,plain,
% 2.71/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.71/1.01      | v1_relat_1(sK7) ),
% 2.71/1.01      inference(instantiation,[status(thm)],[c_14]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2250,plain,
% 2.71/1.01      ( ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
% 2.71/1.01      | v1_relat_1(sK7) ),
% 2.71/1.01      inference(instantiation,[status(thm)],[c_2214]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2251,plain,
% 2.71/1.01      ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
% 2.71/1.01      | v1_relat_1(sK7) = iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_2250]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2370,plain,
% 2.71/1.01      ( r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 2.71/1.01      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 2.71/1.01      inference(global_propositional_subsumption,
% 2.71/1.01                [status(thm)],
% 2.71/1.01                [c_2158,c_31,c_412,c_2251]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2371,plain,
% 2.71/1.01      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 2.71/1.01      | r2_hidden(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top ),
% 2.71/1.01      inference(renaming,[status(thm)],[c_2370]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_5,plain,
% 2.71/1.01      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 2.71/1.01      inference(cnf_transformation,[],[f49]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2167,plain,
% 2.71/1.01      ( m1_subset_1(X0,X1) = iProver_top
% 2.71/1.01      | r2_hidden(X0,X1) != iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_5]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2477,plain,
% 2.71/1.01      ( m1_subset_1(sK3(sK7,X0),k1_relat_1(sK7)) = iProver_top
% 2.71/1.01      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 2.71/1.01      inference(superposition,[status(thm)],[c_2371,c_2167]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3162,plain,
% 2.71/1.01      ( sK6 = k1_xboole_0
% 2.71/1.01      | m1_subset_1(sK3(sK7,X0),sK5) = iProver_top
% 2.71/1.01      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 2.71/1.01      inference(superposition,[status(thm)],[c_3101,c_2477]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_17,plain,
% 2.71/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/1.01      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 2.71/1.01      inference(cnf_transformation,[],[f61]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2164,plain,
% 2.71/1.01      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 2.71/1.01      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2935,plain,
% 2.71/1.01      ( k2_relset_1(sK5,sK6,sK7) = k2_relat_1(sK7) ),
% 2.71/1.01      inference(superposition,[status(thm)],[c_2161,c_2164]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_25,negated_conjecture,
% 2.71/1.01      ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) ),
% 2.71/1.01      inference(cnf_transformation,[],[f71]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2162,plain,
% 2.71/1.01      ( r2_hidden(sK4,k2_relset_1(sK5,sK6,sK7)) = iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3065,plain,
% 2.71/1.01      ( r2_hidden(sK4,k2_relat_1(sK7)) = iProver_top ),
% 2.71/1.01      inference(demodulation,[status(thm)],[c_2935,c_2162]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_12,plain,
% 2.71/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.71/1.01      | ~ v1_funct_1(X1)
% 2.71/1.01      | ~ v1_relat_1(X1)
% 2.71/1.01      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 2.71/1.01      inference(cnf_transformation,[],[f75]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_425,plain,
% 2.71/1.01      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 2.71/1.01      | ~ v1_relat_1(X1)
% 2.71/1.01      | k1_funct_1(X1,sK3(X1,X0)) = X0
% 2.71/1.01      | sK7 != X1 ),
% 2.71/1.01      inference(resolution_lifted,[status(thm)],[c_12,c_28]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_426,plain,
% 2.71/1.01      ( ~ r2_hidden(X0,k2_relat_1(sK7))
% 2.71/1.01      | ~ v1_relat_1(sK7)
% 2.71/1.01      | k1_funct_1(sK7,sK3(sK7,X0)) = X0 ),
% 2.71/1.01      inference(unflattening,[status(thm)],[c_425]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2157,plain,
% 2.71/1.01      ( k1_funct_1(sK7,sK3(sK7,X0)) = X0
% 2.71/1.01      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 2.71/1.01      | v1_relat_1(sK7) != iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_427,plain,
% 2.71/1.01      ( k1_funct_1(sK7,sK3(sK7,X0)) = X0
% 2.71/1.01      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 2.71/1.01      | v1_relat_1(sK7) != iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_426]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2310,plain,
% 2.71/1.01      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 2.71/1.01      | k1_funct_1(sK7,sK3(sK7,X0)) = X0 ),
% 2.71/1.01      inference(global_propositional_subsumption,
% 2.71/1.01                [status(thm)],
% 2.71/1.01                [c_2157,c_31,c_427,c_2251]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2311,plain,
% 2.71/1.01      ( k1_funct_1(sK7,sK3(sK7,X0)) = X0
% 2.71/1.01      | r2_hidden(X0,k2_relat_1(sK7)) != iProver_top ),
% 2.71/1.01      inference(renaming,[status(thm)],[c_2310]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3100,plain,
% 2.71/1.01      ( k1_funct_1(sK7,sK3(sK7,sK4)) = sK4 ),
% 2.71/1.01      inference(superposition,[status(thm)],[c_3065,c_2311]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_24,negated_conjecture,
% 2.71/1.01      ( ~ m1_subset_1(X0,sK5) | k1_funct_1(sK7,X0) != sK4 ),
% 2.71/1.01      inference(cnf_transformation,[],[f72]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2163,plain,
% 2.71/1.01      ( k1_funct_1(sK7,X0) != sK4 | m1_subset_1(X0,sK5) != iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3243,plain,
% 2.71/1.01      ( m1_subset_1(sK3(sK7,sK4),sK5) != iProver_top ),
% 2.71/1.01      inference(superposition,[status(thm)],[c_3100,c_2163]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_9968,plain,
% 2.71/1.01      ( sK6 = k1_xboole_0
% 2.71/1.01      | r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top ),
% 2.71/1.01      inference(superposition,[status(thm)],[c_3162,c_3243]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_10563,plain,
% 2.71/1.01      ( sK6 = k1_xboole_0 ),
% 2.71/1.01      inference(global_propositional_subsumption,
% 2.71/1.01                [status(thm)],
% 2.71/1.01                [c_9968,c_3065]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2,plain,
% 2.71/1.01      ( r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0) ),
% 2.71/1.01      inference(cnf_transformation,[],[f46]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2169,plain,
% 2.71/1.01      ( r1_tarski(X0,X1) = iProver_top
% 2.71/1.01      | r2_hidden(sK0(X0,X1),X0) = iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_15,plain,
% 2.71/1.01      ( v5_relat_1(X0,X1)
% 2.71/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 2.71/1.01      inference(cnf_transformation,[],[f59]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_7,plain,
% 2.71/1.01      ( ~ v5_relat_1(X0,X1)
% 2.71/1.01      | r1_tarski(k2_relat_1(X0),X1)
% 2.71/1.01      | ~ v1_relat_1(X0) ),
% 2.71/1.01      inference(cnf_transformation,[],[f50]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_341,plain,
% 2.71/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/1.01      | r1_tarski(k2_relat_1(X0),X2)
% 2.71/1.01      | ~ v1_relat_1(X0) ),
% 2.71/1.01      inference(resolution,[status(thm)],[c_15,c_7]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_345,plain,
% 2.71/1.01      ( r1_tarski(k2_relat_1(X0),X2)
% 2.71/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
% 2.71/1.01      inference(global_propositional_subsumption,
% 2.71/1.01                [status(thm)],
% 2.71/1.01                [c_341,c_14]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_346,plain,
% 2.71/1.01      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.71/1.01      | r1_tarski(k2_relat_1(X0),X2) ),
% 2.71/1.01      inference(renaming,[status(thm)],[c_345]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2159,plain,
% 2.71/1.01      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.71/1.01      | r1_tarski(k2_relat_1(X0),X2) = iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_346]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2831,plain,
% 2.71/1.01      ( r1_tarski(k2_relat_1(sK7),sK6) = iProver_top ),
% 2.71/1.01      inference(superposition,[status(thm)],[c_2161,c_2159]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3,plain,
% 2.71/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(X2,X0) | r2_hidden(X2,X1) ),
% 2.71/1.01      inference(cnf_transformation,[],[f45]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2168,plain,
% 2.71/1.01      ( r1_tarski(X0,X1) != iProver_top
% 2.71/1.01      | r2_hidden(X2,X0) != iProver_top
% 2.71/1.01      | r2_hidden(X2,X1) = iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3060,plain,
% 2.71/1.01      ( r2_hidden(X0,k2_relat_1(sK7)) != iProver_top
% 2.71/1.01      | r2_hidden(X0,sK6) = iProver_top ),
% 2.71/1.01      inference(superposition,[status(thm)],[c_2831,c_2168]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3594,plain,
% 2.71/1.01      ( r1_tarski(k2_relat_1(sK7),X0) = iProver_top
% 2.71/1.01      | r2_hidden(sK0(k2_relat_1(sK7),X0),sK6) = iProver_top ),
% 2.71/1.01      inference(superposition,[status(thm)],[c_2169,c_3060]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_10572,plain,
% 2.71/1.01      ( r1_tarski(k2_relat_1(sK7),X0) = iProver_top
% 2.71/1.01      | r2_hidden(sK0(k2_relat_1(sK7),X0),k1_xboole_0) = iProver_top ),
% 2.71/1.01      inference(demodulation,[status(thm)],[c_10563,c_3594]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_10592,plain,
% 2.71/1.01      ( r1_tarski(k2_relat_1(sK7),k1_xboole_0) = iProver_top
% 2.71/1.01      | r2_hidden(sK0(k2_relat_1(sK7),k1_xboole_0),k1_xboole_0) = iProver_top ),
% 2.71/1.01      inference(instantiation,[status(thm)],[c_10572]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_1,plain,
% 2.71/1.01      ( r1_tarski(X0,X1) | ~ r2_hidden(sK0(X0,X1),X1) ),
% 2.71/1.01      inference(cnf_transformation,[],[f47]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_5251,plain,
% 2.71/1.01      ( r1_tarski(k2_relat_1(sK7),X0)
% 2.71/1.01      | ~ r2_hidden(sK0(k2_relat_1(sK7),X0),X0) ),
% 2.71/1.01      inference(instantiation,[status(thm)],[c_1]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_5257,plain,
% 2.71/1.01      ( r1_tarski(k2_relat_1(sK7),X0) = iProver_top
% 2.71/1.01      | r2_hidden(sK0(k2_relat_1(sK7),X0),X0) != iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_5251]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_5259,plain,
% 2.71/1.01      ( r1_tarski(k2_relat_1(sK7),k1_xboole_0) = iProver_top
% 2.71/1.01      | r2_hidden(sK0(k2_relat_1(sK7),k1_xboole_0),k1_xboole_0) != iProver_top ),
% 2.71/1.01      inference(instantiation,[status(thm)],[c_5257]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_2569,plain,
% 2.71/1.01      ( ~ r1_tarski(X0,X1) | ~ r2_hidden(sK4,X0) | r2_hidden(sK4,X1) ),
% 2.71/1.01      inference(instantiation,[status(thm)],[c_3]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3957,plain,
% 2.71/1.01      ( ~ r1_tarski(k2_relat_1(sK7),X0)
% 2.71/1.01      | r2_hidden(sK4,X0)
% 2.71/1.01      | ~ r2_hidden(sK4,k2_relat_1(sK7)) ),
% 2.71/1.01      inference(instantiation,[status(thm)],[c_2569]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3958,plain,
% 2.71/1.01      ( r1_tarski(k2_relat_1(sK7),X0) != iProver_top
% 2.71/1.01      | r2_hidden(sK4,X0) = iProver_top
% 2.71/1.01      | r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_3957]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3960,plain,
% 2.71/1.01      ( r1_tarski(k2_relat_1(sK7),k1_xboole_0) != iProver_top
% 2.71/1.01      | r2_hidden(sK4,k2_relat_1(sK7)) != iProver_top
% 2.71/1.01      | r2_hidden(sK4,k1_xboole_0) = iProver_top ),
% 2.71/1.01      inference(instantiation,[status(thm)],[c_3958]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_0,plain,
% 2.71/1.01      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 2.71/1.01      inference(cnf_transformation,[],[f44]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_4,plain,
% 2.71/1.01      ( v1_xboole_0(k1_xboole_0) ),
% 2.71/1.01      inference(cnf_transformation,[],[f48]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_330,plain,
% 2.71/1.01      ( ~ r2_hidden(X0,X1) | k1_xboole_0 != X1 ),
% 2.71/1.01      inference(resolution_lifted,[status(thm)],[c_0,c_4]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_331,plain,
% 2.71/1.01      ( ~ r2_hidden(X0,k1_xboole_0) ),
% 2.71/1.01      inference(unflattening,[status(thm)],[c_330]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3350,plain,
% 2.71/1.01      ( ~ r2_hidden(sK4,k1_xboole_0) ),
% 2.71/1.01      inference(instantiation,[status(thm)],[c_331]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(c_3351,plain,
% 2.71/1.01      ( r2_hidden(sK4,k1_xboole_0) != iProver_top ),
% 2.71/1.01      inference(predicate_to_equality,[status(thm)],[c_3350]) ).
% 2.71/1.01  
% 2.71/1.01  cnf(contradiction,plain,
% 2.71/1.01      ( $false ),
% 2.71/1.01      inference(minisat,
% 2.71/1.01                [status(thm)],
% 2.71/1.01                [c_10592,c_5259,c_3960,c_3351,c_3065]) ).
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.71/1.01  
% 2.71/1.01  ------                               Statistics
% 2.71/1.01  
% 2.71/1.01  ------ General
% 2.71/1.01  
% 2.71/1.01  abstr_ref_over_cycles:                  0
% 2.71/1.01  abstr_ref_under_cycles:                 0
% 2.71/1.01  gc_basic_clause_elim:                   0
% 2.71/1.01  forced_gc_time:                         0
% 2.71/1.01  parsing_time:                           0.007
% 2.71/1.01  unif_index_cands_time:                  0.
% 2.71/1.01  unif_index_add_time:                    0.
% 2.71/1.01  orderings_time:                         0.
% 2.71/1.01  out_proof_time:                         0.012
% 2.71/1.01  total_time:                             0.473
% 2.71/1.01  num_of_symbols:                         55
% 2.71/1.01  num_of_terms:                           8803
% 2.71/1.01  
% 2.71/1.01  ------ Preprocessing
% 2.71/1.01  
% 2.71/1.01  num_of_splits:                          0
% 2.71/1.01  num_of_split_atoms:                     0
% 2.71/1.01  num_of_reused_defs:                     0
% 2.71/1.01  num_eq_ax_congr_red:                    28
% 2.71/1.01  num_of_sem_filtered_clauses:            1
% 2.71/1.01  num_of_subtypes:                        0
% 2.71/1.01  monotx_restored_types:                  0
% 2.71/1.01  sat_num_of_epr_types:                   0
% 2.71/1.01  sat_num_of_non_cyclic_types:            0
% 2.71/1.01  sat_guarded_non_collapsed_types:        0
% 2.71/1.01  num_pure_diseq_elim:                    0
% 2.71/1.01  simp_replaced_by:                       0
% 2.71/1.01  res_preprocessed:                       125
% 2.71/1.01  prep_upred:                             0
% 2.71/1.01  prep_unflattend:                        120
% 2.71/1.01  smt_new_axioms:                         0
% 2.71/1.01  pred_elim_cands:                        4
% 2.71/1.01  pred_elim:                              4
% 2.71/1.01  pred_elim_cl:                           8
% 2.71/1.01  pred_elim_cycles:                       11
% 2.71/1.01  merged_defs:                            0
% 2.71/1.01  merged_defs_ncl:                        0
% 2.71/1.01  bin_hyper_res:                          0
% 2.71/1.01  prep_cycles:                            4
% 2.71/1.01  pred_elim_time:                         0.017
% 2.71/1.01  splitting_time:                         0.
% 2.71/1.01  sem_filter_time:                        0.
% 2.71/1.01  monotx_time:                            0.
% 2.71/1.01  subtype_inf_time:                       0.
% 2.71/1.01  
% 2.71/1.01  ------ Problem properties
% 2.71/1.01  
% 2.71/1.01  clauses:                                21
% 2.71/1.01  conjectures:                            3
% 2.71/1.01  epr:                                    3
% 2.71/1.01  horn:                                   16
% 2.71/1.01  ground:                                 5
% 2.71/1.01  unary:                                  3
% 2.71/1.01  binary:                                 9
% 2.71/1.01  lits:                                   53
% 2.71/1.01  lits_eq:                                16
% 2.71/1.01  fd_pure:                                0
% 2.71/1.01  fd_pseudo:                              0
% 2.71/1.01  fd_cond:                                3
% 2.71/1.01  fd_pseudo_cond:                         0
% 2.71/1.01  ac_symbols:                             0
% 2.71/1.01  
% 2.71/1.01  ------ Propositional Solver
% 2.71/1.01  
% 2.71/1.01  prop_solver_calls:                      32
% 2.71/1.01  prop_fast_solver_calls:                 1234
% 2.71/1.01  smt_solver_calls:                       0
% 2.71/1.01  smt_fast_solver_calls:                  0
% 2.71/1.01  prop_num_of_clauses:                    5302
% 2.71/1.01  prop_preprocess_simplified:             7635
% 2.71/1.01  prop_fo_subsumed:                       10
% 2.71/1.01  prop_solver_time:                       0.
% 2.71/1.01  smt_solver_time:                        0.
% 2.71/1.01  smt_fast_solver_time:                   0.
% 2.71/1.01  prop_fast_solver_time:                  0.
% 2.71/1.01  prop_unsat_core_time:                   0.
% 2.71/1.01  
% 2.71/1.01  ------ QBF
% 2.71/1.01  
% 2.71/1.01  qbf_q_res:                              0
% 2.71/1.01  qbf_num_tautologies:                    0
% 2.71/1.01  qbf_prep_cycles:                        0
% 2.71/1.01  
% 2.71/1.01  ------ BMC1
% 2.71/1.01  
% 2.71/1.01  bmc1_current_bound:                     -1
% 2.71/1.01  bmc1_last_solved_bound:                 -1
% 2.71/1.01  bmc1_unsat_core_size:                   -1
% 2.71/1.01  bmc1_unsat_core_parents_size:           -1
% 2.71/1.01  bmc1_merge_next_fun:                    0
% 2.71/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.71/1.01  
% 2.71/1.01  ------ Instantiation
% 2.71/1.01  
% 2.71/1.01  inst_num_of_clauses:                    932
% 2.71/1.01  inst_num_in_passive:                    228
% 2.71/1.01  inst_num_in_active:                     551
% 2.71/1.01  inst_num_in_unprocessed:                153
% 2.71/1.01  inst_num_of_loops:                      720
% 2.71/1.01  inst_num_of_learning_restarts:          0
% 2.71/1.01  inst_num_moves_active_passive:          163
% 2.71/1.01  inst_lit_activity:                      0
% 2.71/1.01  inst_lit_activity_moves:                0
% 2.71/1.01  inst_num_tautologies:                   0
% 2.71/1.01  inst_num_prop_implied:                  0
% 2.71/1.01  inst_num_existing_simplified:           0
% 2.71/1.01  inst_num_eq_res_simplified:             0
% 2.71/1.01  inst_num_child_elim:                    0
% 2.71/1.01  inst_num_of_dismatching_blockings:      412
% 2.71/1.01  inst_num_of_non_proper_insts:           1289
% 2.71/1.01  inst_num_of_duplicates:                 0
% 2.71/1.01  inst_inst_num_from_inst_to_res:         0
% 2.71/1.01  inst_dismatching_checking_time:         0.
% 2.71/1.01  
% 2.71/1.01  ------ Resolution
% 2.71/1.01  
% 2.71/1.01  res_num_of_clauses:                     0
% 2.71/1.01  res_num_in_passive:                     0
% 2.71/1.01  res_num_in_active:                      0
% 2.71/1.01  res_num_of_loops:                       129
% 2.71/1.01  res_forward_subset_subsumed:            45
% 2.71/1.01  res_backward_subset_subsumed:           0
% 2.71/1.01  res_forward_subsumed:                   0
% 2.71/1.01  res_backward_subsumed:                  0
% 2.71/1.01  res_forward_subsumption_resolution:     0
% 2.71/1.01  res_backward_subsumption_resolution:    0
% 2.71/1.01  res_clause_to_clause_subsumption:       3662
% 2.71/1.01  res_orphan_elimination:                 0
% 2.71/1.01  res_tautology_del:                      220
% 2.71/1.01  res_num_eq_res_simplified:              0
% 2.71/1.01  res_num_sel_changes:                    0
% 2.71/1.01  res_moves_from_active_to_pass:          0
% 2.71/1.01  
% 2.71/1.01  ------ Superposition
% 2.71/1.01  
% 2.71/1.01  sup_time_total:                         0.
% 2.71/1.01  sup_time_generating:                    0.
% 2.71/1.01  sup_time_sim_full:                      0.
% 2.71/1.01  sup_time_sim_immed:                     0.
% 2.71/1.01  
% 2.71/1.01  sup_num_of_clauses:                     776
% 2.71/1.01  sup_num_in_active:                      119
% 2.71/1.01  sup_num_in_passive:                     657
% 2.71/1.01  sup_num_of_loops:                       142
% 2.71/1.01  sup_fw_superposition:                   591
% 2.71/1.01  sup_bw_superposition:                   403
% 2.71/1.01  sup_immediate_simplified:               70
% 2.71/1.01  sup_given_eliminated:                   0
% 2.71/1.01  comparisons_done:                       0
% 2.71/1.01  comparisons_avoided:                    42
% 2.71/1.01  
% 2.71/1.01  ------ Simplifications
% 2.71/1.01  
% 2.71/1.01  
% 2.71/1.01  sim_fw_subset_subsumed:                 6
% 2.71/1.01  sim_bw_subset_subsumed:                 2
% 2.71/1.01  sim_fw_subsumed:                        10
% 2.71/1.01  sim_bw_subsumed:                        25
% 2.71/1.01  sim_fw_subsumption_res:                 0
% 2.71/1.01  sim_bw_subsumption_res:                 0
% 2.71/1.01  sim_tautology_del:                      1
% 2.71/1.01  sim_eq_tautology_del:                   172
% 2.71/1.01  sim_eq_res_simp:                        1
% 2.71/1.01  sim_fw_demodulated:                     0
% 2.71/1.01  sim_bw_demodulated:                     21
% 2.71/1.01  sim_light_normalised:                   30
% 2.71/1.01  sim_joinable_taut:                      0
% 2.71/1.01  sim_joinable_simp:                      0
% 2.71/1.01  sim_ac_normalised:                      0
% 2.71/1.01  sim_smt_subsumption:                    0
% 2.71/1.01  
%------------------------------------------------------------------------------
