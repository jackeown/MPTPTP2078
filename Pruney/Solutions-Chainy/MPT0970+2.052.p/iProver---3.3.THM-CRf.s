%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:00:56 EST 2020

% Result     : Theorem 39.95s
% Output     : CNFRefutation 39.95s
% Verified   : 
% Statistics : Number of formulae       :  318 (19544 expanded)
%              Number of clauses        :  249 (6983 expanded)
%              Number of leaves         :   24 (4944 expanded)
%              Depth                    :   33
%              Number of atoms          : 1064 (100879 expanded)
%              Number of equality atoms :  653 (34263 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal clause size      :   16 (   3 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f17,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f12,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ! [X3] :
            ~ ( ! [X4] :
                  ~ ( k1_funct_1(X2,X4) = X3
                    & r2_hidden(X4,X0) )
              & r2_hidden(X3,X1) )
       => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ! [X3] :
              ~ ( ! [X4] :
                    ~ ( k1_funct_1(X2,X4) = X3
                      & r2_hidden(X4,X0) )
                & r2_hidden(X3,X1) )
         => k2_relset_1(X0,X1,X2) = X1 ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f27,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f28,plain,(
    ? [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) != X1
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(X2,X4) = X3
              & r2_hidden(X4,X0) )
          | ~ r2_hidden(X3,X1) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f42,plain,(
    ! [X2,X0,X3] :
      ( ? [X4] :
          ( k1_funct_1(X2,X4) = X3
          & r2_hidden(X4,X0) )
     => ( k1_funct_1(X2,sK7(X3)) = X3
        & r2_hidden(sK7(X3),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X0,X1,X2] :
        ( k2_relset_1(X0,X1,X2) != X1
        & ! [X3] :
            ( ? [X4] :
                ( k1_funct_1(X2,X4) = X3
                & r2_hidden(X4,X0) )
            | ~ r2_hidden(X3,X1) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( k2_relset_1(sK4,sK5,sK6) != sK5
      & ! [X3] :
          ( ? [X4] :
              ( k1_funct_1(sK6,X4) = X3
              & r2_hidden(X4,sK4) )
          | ~ r2_hidden(X3,sK5) )
      & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
      & v1_funct_2(sK6,sK4,sK5)
      & v1_funct_1(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( k2_relset_1(sK4,sK5,sK6) != sK5
    & ! [X3] :
        ( ( k1_funct_1(sK6,sK7(X3)) = X3
          & r2_hidden(sK7(X3),sK4) )
        | ~ r2_hidden(X3,sK5) )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))
    & v1_funct_2(sK6,sK4,sK5)
    & v1_funct_1(sK6) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f28,f42,f41])).

fof(f70,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f43])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f5,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f51,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f5])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f15,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X2] :
            ( r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f15])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ? [X2] :
            ( ~ r2_hidden(X2,X1)
            & r2_hidden(X2,X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X1,X0] :
      ( ? [X2] :
          ( ~ r2_hidden(X2,X1)
          & r2_hidden(X2,X0) )
     => ( ~ r2_hidden(sK0(X0,X1),X1)
        & r2_hidden(sK0(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( r1_tarski(X0,X1)
        | ( ~ r2_hidden(sK0(X0,X1),X1)
          & r2_hidden(sK0(X0,X1),X0) ) )
      & ( ! [X3] :
            ( r2_hidden(X3,X1)
            | ~ r2_hidden(X3,X0) )
        | ~ r1_tarski(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | r2_hidden(sK0(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( r2_hidden(X3,X1)
      | ~ r2_hidden(X3,X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ r2_hidden(sK0(X0,X1),X1) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f72,plain,(
    ! [X3] :
      ( k1_funct_1(sK6,sK7(X3)) = X3
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f43])).

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

fof(f18,plain,(
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f35,plain,(
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
    inference(rectify,[],[f34])).

fof(f38,plain,(
    ! [X5,X0] :
      ( ? [X7] :
          ( k1_funct_1(X0,X7) = X5
          & r2_hidden(X7,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK3(X0,X5)) = X5
        & r2_hidden(sK3(X0,X5),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,(
    ! [X2,X1,X0] :
      ( ? [X4] :
          ( k1_funct_1(X0,X4) = X2
          & r2_hidden(X4,k1_relat_1(X0)) )
     => ( k1_funct_1(X0,sK2(X0,X1)) = X2
        & r2_hidden(sK2(X0,X1),k1_relat_1(X0)) ) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,(
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

fof(f39,plain,(
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).

fof(f55,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | r2_hidden(sK2(X0,X1),k1_relat_1(X0))
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f68,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f43])).

fof(f69,plain,(
    v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f43])).

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
    inference(ennf_transformation,[],[f11])).

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

fof(f40,plain,(
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

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f71,plain,(
    ! [X3] :
      ( r2_hidden(sK7(X3),sK4)
      | ~ r2_hidden(X3,sK5) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
      | r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f73,plain,(
    k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f43])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f57,plain,(
    ! [X0,X3,X1] :
      ( k2_relat_1(X0) = X1
      | k1_funct_1(X0,X3) != sK1(X0,X1)
      | ~ r2_hidden(X3,k1_relat_1(X0))
      | ~ r2_hidden(sK1(X0,X1),X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f80,plain,(
    ! [X2,X0] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) ) ),
    inference(equality_resolution,[],[f66])).

fof(f2,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f47,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f2])).

fof(f52,plain,(
    ! [X0,X5,X1] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f77,plain,(
    ! [X0,X5] :
      ( r2_hidden(sK3(X0,X5),k1_relat_1(X0))
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f52])).

fof(f53,plain,(
    ! [X0,X5,X1] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,X1)
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f76,plain,(
    ! [X0,X5] :
      ( k1_funct_1(X0,sK3(X0,X5)) = X5
      | ~ r2_hidden(X5,k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f54,plain,(
    ! [X6,X0,X5,X1] :
      ( r2_hidden(X5,X1)
      | k1_funct_1(X0,X6) != X5
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f74,plain,(
    ! [X6,X0,X1] :
      ( r2_hidden(k1_funct_1(X0,X6),X1)
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | k2_relat_1(X0) != X1
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f54])).

fof(f75,plain,(
    ! [X6,X0] :
      ( r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0))
      | ~ r2_hidden(X6,k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(equality_resolution,[],[f74])).

cnf(c_15,plain,
    ( v5_relat_1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
    inference(cnf_transformation,[],[f59])).

cnf(c_6,plain,
    ( ~ v5_relat_1(X0,X1)
    | r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_321,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r1_tarski(k2_relat_1(X0),X2)
    | ~ v1_relat_1(X0) ),
    inference(resolution,[status(thm)],[c_15,c_6])).

cnf(c_27,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
    inference(cnf_transformation,[],[f70])).

cnf(c_421,plain,
    ( r1_tarski(k2_relat_1(X0),X1)
    | ~ v1_relat_1(X0)
    | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_321,c_27])).

cnf(c_422,plain,
    ( r1_tarski(k2_relat_1(sK6),X0)
    | ~ v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_421])).

cnf(c_1340,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_relat_1(sK6),X1) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_422])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
    | ~ v1_relat_1(X1)
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_406,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(X1)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_4,c_27])).

cnf(c_407,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0) ),
    inference(unflattening,[status(thm)],[c_406])).

cnf(c_1029,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_1426,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_1421,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
    inference(instantiation,[status(thm)],[c_407])).

cnf(c_1538,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_1421])).

cnf(c_7,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_1590,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(instantiation,[status(thm)],[c_7])).

cnf(c_1688,plain,
    ( v1_relat_1(sK6) ),
    inference(global_propositional_subsumption,[status(thm)],[c_407,c_1426,c_1538,c_1590])).

cnf(c_1699,plain,
    ( r1_tarski(k2_relat_1(sK6),X0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1688,c_422])).

cnf(c_1724,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_relat_1(sK6),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1699])).

cnf(c_3615,plain,
    ( r1_tarski(k2_relat_1(sK6),X1) = iProver_top
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1340,c_1724])).

cnf(c_3616,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | r1_tarski(k2_relat_1(sK6),X1) = iProver_top ),
    inference(renaming,[status(thm)],[c_3615])).

cnf(c_3619,plain,
    ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
    inference(equality_resolution,[status(thm)],[c_3616])).

cnf(c_1,plain,
    ( r2_hidden(sK0(X0,X1),X0)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_1347,plain,
    ( r2_hidden(sK0(X0,X1),X0) = iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_2,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X0,X2)
    | ~ r1_tarski(X1,X2) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1346,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | r2_hidden(X0,X2) = iProver_top
    | r1_tarski(X1,X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_1568,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1347,c_1346])).

cnf(c_1678,plain,
    ( r2_hidden(sK0(X0,X1),X2) = iProver_top
    | r1_tarski(X0,X3) != iProver_top
    | r1_tarski(X3,X2) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(superposition,[status(thm)],[c_1568,c_1346])).

cnf(c_47781,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) = iProver_top
    | r1_tarski(sK5,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3619,c_1678])).

cnf(c_0,plain,
    ( ~ r2_hidden(sK0(X0,X1),X1)
    | r1_tarski(X0,X1) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_1348,plain,
    ( r2_hidden(sK0(X0,X1),X1) != iProver_top
    | r1_tarski(X0,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_0])).

cnf(c_48464,plain,
    ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_47781,c_1348])).

cnf(c_25,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | k1_funct_1(sK6,sK7(X0)) = X0 ),
    inference(cnf_transformation,[],[f72])).

cnf(c_1343,plain,
    ( k1_funct_1(sK6,sK7(X0)) = X0
    | r2_hidden(X0,sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_1496,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r1_tarski(sK5,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1347,c_1343])).

cnf(c_10,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f55])).

cnf(c_29,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f68])).

cnf(c_661,plain,
    ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
    | r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k2_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_10,c_29])).

cnf(c_662,plain,
    ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | k2_relat_1(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_661])).

cnf(c_1339,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_1703,plain,
    ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
    | r2_hidden(sK1(sK6,X0),X0)
    | k2_relat_1(sK6) = X0 ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1688,c_662])).

cnf(c_1712,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1703])).

cnf(c_3183,plain,
    ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | k2_relat_1(sK6) = X0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_1339,c_1712])).

cnf(c_3184,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_3183])).

cnf(c_3194,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),X1) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3184,c_1346])).

cnf(c_3584,plain,
    ( k1_funct_1(sK6,sK7(sK2(sK6,X0))) = sK2(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | r1_tarski(k1_relat_1(sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3194,c_1343])).

cnf(c_4207,plain,
    ( k1_funct_1(sK6,sK7(sK2(sK6,X0))) = sK2(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_3584,c_1346])).

cnf(c_5702,plain,
    ( k1_funct_1(sK6,sK7(sK2(sK6,X0))) = sK2(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(X0,X2) != iProver_top
    | r1_tarski(k1_relat_1(sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_4207,c_1346])).

cnf(c_6543,plain,
    ( k1_funct_1(sK6,sK7(sK2(sK6,sK5))) = sK2(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(k1_relat_1(sK6),sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_5702])).

cnf(c_1030,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1462,plain,
    ( sK5 != X0
    | sK5 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1526,plain,
    ( sK5 != sK5
    | sK5 = k1_xboole_0
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1462])).

cnf(c_1527,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_3248,plain,
    ( X0 != X1
    | X1 = X0 ),
    inference(resolution,[status(thm)],[c_1030,c_1029])).

cnf(c_28,negated_conjecture,
    ( v1_funct_2(sK6,sK4,sK5) ),
    inference(cnf_transformation,[],[f69])).

cnf(c_23,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = X1
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f62])).

cnf(c_436,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | k1_relset_1(X1,X2,X0) = X1
    | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0
    | k1_xboole_0 = X2 ),
    inference(resolution_lifted,[status(thm)],[c_23,c_27])).

cnf(c_437,plain,
    ( ~ v1_funct_2(sK6,X0,X1)
    | k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = X1 ),
    inference(unflattening,[status(thm)],[c_436])).

cnf(c_799,plain,
    ( k1_relset_1(X0,X1,sK6) = X0
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != sK6
    | sK5 != X1
    | sK4 != X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_437])).

cnf(c_800,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = sK5 ),
    inference(unflattening,[status(thm)],[c_799])).

cnf(c_868,plain,
    ( k1_relset_1(sK4,sK5,sK6) = sK4
    | k1_xboole_0 = sK5 ),
    inference(equality_resolution_simp,[status(thm)],[c_800])).

cnf(c_4850,plain,
    ( sK4 = k1_relset_1(sK4,sK5,sK6)
    | k1_xboole_0 = sK5 ),
    inference(resolution,[status(thm)],[c_3248,c_868])).

cnf(c_16,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
    inference(cnf_transformation,[],[f60])).

cnf(c_481,plain,
    ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_16,c_27])).

cnf(c_482,plain,
    ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_481])).

cnf(c_1805,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(resolution,[status(thm)],[c_482,c_1029])).

cnf(c_4859,plain,
    ( k1_relat_1(sK6) = k1_relset_1(sK4,sK5,sK6) ),
    inference(resolution,[status(thm)],[c_3248,c_1805])).

cnf(c_1531,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1910,plain,
    ( X0 != k1_relset_1(sK4,sK5,sK6)
    | sK4 = X0
    | sK4 != k1_relset_1(sK4,sK5,sK6) ),
    inference(instantiation,[status(thm)],[c_1531])).

cnf(c_15451,plain,
    ( k1_relat_1(sK6) != k1_relset_1(sK4,sK5,sK6)
    | sK4 != k1_relset_1(sK4,sK5,sK6)
    | sK4 = k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1910])).

cnf(c_3187,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3184,c_1346])).

cnf(c_26,negated_conjecture,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK7(X0),sK4) ),
    inference(cnf_transformation,[],[f71])).

cnf(c_1342,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_26])).

cnf(c_1569,plain,
    ( r2_hidden(X0,sK5) != iProver_top
    | r2_hidden(sK7(X0),X1) = iProver_top
    | r1_tarski(sK4,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_1342,c_1346])).

cnf(c_9,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1 ),
    inference(cnf_transformation,[],[f56])).

cnf(c_679,plain,
    ( r2_hidden(sK1(X0,X1),X1)
    | ~ v1_relat_1(X0)
    | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
    | k2_relat_1(X0) = X1
    | sK6 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_9,c_29])).

cnf(c_680,plain,
    ( r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0 ),
    inference(unflattening,[status(thm)],[c_679])).

cnf(c_1338,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_681,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_680])).

cnf(c_1539,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
    | v1_relat_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1538])).

cnf(c_1591,plain,
    ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1590])).

cnf(c_2905,plain,
    ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | k2_relat_1(sK6) = X0
    | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1338,c_681,c_1426,c_1539,c_1591])).

cnf(c_2906,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_2905])).

cnf(c_2912,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(superposition,[status(thm)],[c_2906,c_1343])).

cnf(c_24,negated_conjecture,
    ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
    inference(cnf_transformation,[],[f73])).

cnf(c_17,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
    inference(cnf_transformation,[],[f61])).

cnf(c_472,plain,
    ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_17,c_27])).

cnf(c_473,plain,
    ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
    inference(unflattening,[status(thm)],[c_472])).

cnf(c_1396,plain,
    ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_473])).

cnf(c_1491,plain,
    ( X0 != X1
    | sK5 != X1
    | sK5 = X0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1584,plain,
    ( X0 != sK5
    | sK5 = X0
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1491])).

cnf(c_1746,plain,
    ( k2_relat_1(sK6) != sK5
    | sK5 = k2_relat_1(sK6)
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1584])).

cnf(c_1458,plain,
    ( k2_relset_1(sK4,sK5,sK6) != X0
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1845,plain,
    ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
    | k2_relset_1(sK4,sK5,sK6) = sK5
    | sK5 != k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1458])).

cnf(c_2967,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_2912,c_24,c_1396,c_1527,c_1746,c_1845])).

cnf(c_2968,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(renaming,[status(thm)],[c_2967])).

cnf(c_8,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK1(X1,X2),X2)
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | sK1(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2 ),
    inference(cnf_transformation,[],[f57])).

cnf(c_742,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | ~ r2_hidden(sK1(X1,X2),X2)
    | ~ v1_relat_1(X1)
    | sK1(X1,X2) != k1_funct_1(X1,X0)
    | k2_relat_1(X1) = X2
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_8,c_29])).

cnf(c_743,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,X1),X1)
    | ~ v1_relat_1(sK6)
    | sK1(sK6,X1) != k1_funct_1(sK6,X0)
    | k2_relat_1(sK6) = X1 ),
    inference(unflattening,[status(thm)],[c_742])).

cnf(c_1334,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
    | k2_relat_1(sK6) = X0
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_744,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
    | k2_relat_1(sK6) = X0
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_743])).

cnf(c_2236,plain,
    ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | k2_relat_1(sK6) = X0
    | sK1(sK6,X0) != k1_funct_1(sK6,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1334,c_744,c_1426,c_1539,c_1591])).

cnf(c_2237,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
    | k2_relat_1(sK6) = X0
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_2236])).

cnf(c_2971,plain,
    ( sK1(sK6,X0) != sK1(sK6,sK5)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_2968,c_2237])).

cnf(c_1973,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_680])).

cnf(c_1975,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1973])).

cnf(c_4934,plain,
    ( sK1(sK6,X0) = sK1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_8018,plain,
    ( sK1(sK6,sK5) = sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_4934])).

cnf(c_3553,plain,
    ( sK1(sK6,X0) != X1
    | sK1(sK6,X0) = k1_funct_1(sK6,X2)
    | k1_funct_1(sK6,X2) != X1 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_4933,plain,
    ( sK1(sK6,X0) != sK1(sK6,X0)
    | sK1(sK6,X0) = k1_funct_1(sK6,X1)
    | k1_funct_1(sK6,X1) != sK1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_3553])).

cnf(c_13213,plain,
    ( sK1(sK6,sK5) != sK1(sK6,sK5)
    | sK1(sK6,sK5) = k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_4933])).

cnf(c_2219,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ v1_relat_1(sK6)
    | sK1(sK6,sK5) != k1_funct_1(sK6,X0)
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_20247,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k2_relat_1(sK6) = sK5 ),
    inference(instantiation,[status(thm)],[c_2219])).

cnf(c_20248,plain,
    ( sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
    | k2_relat_1(sK6) = sK5
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20247])).

cnf(c_20691,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_2971,c_24,c_1396,c_1426,c_1527,c_1539,c_1591,c_1746,c_1845,c_1975,c_2912,c_8018,c_13213,c_20248])).

cnf(c_20697,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_20691])).

cnf(c_2214,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) ),
    inference(instantiation,[status(thm)],[c_26])).

cnf(c_2215,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2214])).

cnf(c_2213,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),sK5)
    | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
    inference(instantiation,[status(thm)],[c_25])).

cnf(c_2217,plain,
    ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
    | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2213])).

cnf(c_2875,plain,
    ( r2_hidden(sK7(sK1(sK6,sK5)),X0)
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | ~ r1_tarski(sK4,X0) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_20273,plain,
    ( r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
    | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
    | ~ r1_tarski(sK4,k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_2875])).

cnf(c_20275,plain,
    ( r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20273])).

cnf(c_22787,plain,
    ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_20697,c_24,c_1396,c_1426,c_1527,c_1539,c_1591,c_1746,c_1845,c_2215,c_2217,c_8018,c_13213,c_20248,c_20275])).

cnf(c_22799,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3187,c_22787])).

cnf(c_22793,plain,
    ( k2_relat_1(sK6) = sK5
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_3184,c_22787])).

cnf(c_23953,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_22799,c_24,c_1396,c_1527,c_1746,c_1845,c_22793])).

cnf(c_4876,plain,
    ( ~ r2_hidden(sK1(sK6,X0),X1)
    | r2_hidden(sK1(sK6,X0),X2)
    | ~ r1_tarski(X1,X2) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_28225,plain,
    ( ~ r2_hidden(sK1(sK6,sK5),X0)
    | r2_hidden(sK1(sK6,sK5),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_4876])).

cnf(c_28226,plain,
    ( r2_hidden(sK1(sK6,sK5),X0) != iProver_top
    | r2_hidden(sK1(sK6,sK5),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28225])).

cnf(c_3489,plain,
    ( r2_hidden(sK0(k1_relat_1(sK6),X0),k1_relat_1(sK6))
    | r1_tarski(k1_relat_1(sK6),X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_44051,plain,
    ( r2_hidden(sK0(k1_relat_1(sK6),k1_relat_1(sK6)),k1_relat_1(sK6))
    | r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_3489])).

cnf(c_44053,plain,
    ( r2_hidden(sK0(k1_relat_1(sK6),k1_relat_1(sK6)),k1_relat_1(sK6)) = iProver_top
    | r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44051])).

cnf(c_44052,plain,
    ( ~ r2_hidden(sK0(k1_relat_1(sK6),k1_relat_1(sK6)),k1_relat_1(sK6))
    | r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_44055,plain,
    ( r2_hidden(sK0(k1_relat_1(sK6),k1_relat_1(sK6)),k1_relat_1(sK6)) != iProver_top
    | r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44052])).

cnf(c_1032,plain,
    ( ~ r2_hidden(X0,X1)
    | r2_hidden(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1035,plain,
    ( X0 != X1
    | k2_relat_1(X0) = k2_relat_1(X1) ),
    theory(equality)).

cnf(c_3439,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(X2,k2_relat_1(X3))
    | X2 != X0
    | X3 != X1 ),
    inference(resolution,[status(thm)],[c_1032,c_1035])).

cnf(c_10604,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(X2,k2_relat_1(k1_funct_1(sK6,sK7(X1))))
    | ~ r2_hidden(X1,sK5)
    | X2 != X0 ),
    inference(resolution,[status(thm)],[c_3439,c_25])).

cnf(c_1034,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_19,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
    | k1_xboole_0 = X1
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f80])).

cnf(c_507,plain,
    ( ~ v1_funct_2(X0,X1,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != X0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1 ),
    inference(resolution_lifted,[status(thm)],[c_19,c_27])).

cnf(c_508,plain,
    ( ~ v1_funct_2(sK6,X0,k1_xboole_0)
    | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK6 ),
    inference(unflattening,[status(thm)],[c_507])).

cnf(c_810,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 != sK6
    | sK6 = k1_xboole_0
    | sK5 != k1_xboole_0
    | sK4 != X0
    | k1_xboole_0 = X0 ),
    inference(resolution_lifted,[status(thm)],[c_28,c_508])).

cnf(c_811,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
    | sK6 = k1_xboole_0
    | sK5 != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_810])).

cnf(c_2051,plain,
    ( k2_zfmisc_1(sK4,k1_xboole_0) != k2_zfmisc_1(sK4,sK5)
    | sK6 = k1_xboole_0
    | sK5 != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(resolution,[status(thm)],[c_1034,c_811])).

cnf(c_1058,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_1530,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1029])).

cnf(c_1562,plain,
    ( sK5 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK5 ),
    inference(instantiation,[status(thm)],[c_1030])).

cnf(c_1563,plain,
    ( sK5 != k1_xboole_0
    | k1_xboole_0 = sK5
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1562])).

cnf(c_1036,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_1544,plain,
    ( X0 != sK5
    | X1 != sK4
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK4,sK5) ),
    inference(instantiation,[status(thm)],[c_1036])).

cnf(c_2105,plain,
    ( X0 != sK5
    | k2_zfmisc_1(sK4,X0) = k2_zfmisc_1(sK4,sK5)
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_1544])).

cnf(c_2106,plain,
    ( k2_zfmisc_1(sK4,k1_xboole_0) = k2_zfmisc_1(sK4,sK5)
    | sK4 != sK4
    | k1_xboole_0 != sK5 ),
    inference(instantiation,[status(thm)],[c_2105])).

cnf(c_2379,plain,
    ( sK6 = k1_xboole_0
    | sK5 != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(global_propositional_subsumption,[status(thm)],[c_2051,c_1058,c_1530,c_1563,c_2106])).

cnf(c_10838,plain,
    ( ~ r2_hidden(X0,sK5)
    | r2_hidden(sK6,k2_relat_1(k1_funct_1(sK6,sK7(X0))))
    | ~ r2_hidden(k1_xboole_0,k2_relat_1(X0))
    | sK5 != k1_xboole_0
    | k1_xboole_0 = sK4 ),
    inference(resolution,[status(thm)],[c_10604,c_2379])).

cnf(c_3,plain,
    ( r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_95,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_97,plain,
    ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(instantiation,[status(thm)],[c_95])).

cnf(c_3063,plain,
    ( k2_relat_1(sK6) != X0
    | sK5 != X0
    | sK5 = k2_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1491])).

cnf(c_3064,plain,
    ( k2_relat_1(sK6) != k1_xboole_0
    | sK5 = k2_relat_1(sK6)
    | sK5 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_3063])).

cnf(c_1031,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(X2,X1)
    | X2 != X0 ),
    theory(equality)).

cnf(c_5270,plain,
    ( ~ r1_tarski(X0,X1)
    | r1_tarski(sK5,X1)
    | sK5 != X0 ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_5271,plain,
    ( sK5 != X0
    | r1_tarski(X0,X1) != iProver_top
    | r1_tarski(sK5,X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5270])).

cnf(c_5273,plain,
    ( sK5 != k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) = iProver_top
    | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_5271])).

cnf(c_1345,plain,
    ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2909,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK1(sK6,X0),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2906,c_1346])).

cnf(c_3098,plain,
    ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
    | k1_funct_1(sK6,sK7(sK1(sK6,X0))) = sK1(sK6,X0)
    | k2_relat_1(sK6) = X0
    | r1_tarski(X0,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2909,c_1343])).

cnf(c_4220,plain,
    ( k1_funct_1(sK6,sK2(sK6,k1_xboole_0)) = sK1(sK6,k1_xboole_0)
    | k1_funct_1(sK6,sK7(sK1(sK6,k1_xboole_0))) = sK1(sK6,k1_xboole_0)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1345,c_3098])).

cnf(c_4489,plain,
    ( sK1(sK6,X0) != sK1(sK6,k1_xboole_0)
    | k1_funct_1(sK6,sK2(sK6,k1_xboole_0)) = sK1(sK6,k1_xboole_0)
    | k2_relat_1(sK6) = X0
    | k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK7(sK1(sK6,k1_xboole_0)),k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4220,c_2237])).

cnf(c_683,plain,
    ( k1_funct_1(sK6,sK2(sK6,k1_xboole_0)) = sK1(sK6,k1_xboole_0)
    | k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_681])).

cnf(c_3508,plain,
    ( ~ r2_hidden(sK1(sK6,X0),X0)
    | r2_hidden(sK1(sK6,X0),X1)
    | ~ r1_tarski(X0,X1) ),
    inference(instantiation,[status(thm)],[c_2])).

cnf(c_4896,plain,
    ( ~ r2_hidden(sK1(sK6,X0),X0)
    | r2_hidden(sK1(sK6,X0),k2_relat_1(sK6))
    | ~ r1_tarski(X0,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_3508])).

cnf(c_4899,plain,
    ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | r2_hidden(sK1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | r1_tarski(X0,k2_relat_1(sK6)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4896])).

cnf(c_4901,plain,
    ( r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) != iProver_top
    | r1_tarski(k1_xboole_0,k2_relat_1(sK6)) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4899])).

cnf(c_13,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_697,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_13,c_29])).

cnf(c_698,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_697])).

cnf(c_4898,plain,
    ( r2_hidden(sK3(sK6,sK1(sK6,X0)),k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_698])).

cnf(c_4903,plain,
    ( r2_hidden(sK3(sK6,sK1(sK6,X0)),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4898])).

cnf(c_4905,plain,
    ( r2_hidden(sK3(sK6,sK1(sK6,k1_xboole_0)),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4903])).

cnf(c_12,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
    inference(cnf_transformation,[],[f76])).

cnf(c_712,plain,
    ( ~ r2_hidden(X0,k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | k1_funct_1(X1,sK3(X1,X0)) = X0
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_12,c_29])).

cnf(c_713,plain,
    ( ~ r2_hidden(X0,k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_712])).

cnf(c_4897,plain,
    ( ~ r2_hidden(sK1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6)
    | k1_funct_1(sK6,sK3(sK6,sK1(sK6,X0))) = sK1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_713])).

cnf(c_4907,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK1(sK6,X0))) = sK1(sK6,X0)
    | r2_hidden(sK1(sK6,X0),k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4897])).

cnf(c_4909,plain,
    ( k1_funct_1(sK6,sK3(sK6,sK1(sK6,k1_xboole_0))) = sK1(sK6,k1_xboole_0)
    | r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_4907])).

cnf(c_4936,plain,
    ( sK1(sK6,k1_xboole_0) = sK1(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_4934])).

cnf(c_8126,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK6)) ),
    inference(instantiation,[status(thm)],[c_3])).

cnf(c_8129,plain,
    ( r1_tarski(k1_xboole_0,k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8126])).

cnf(c_20620,plain,
    ( sK1(sK6,X0) != sK1(sK6,X0)
    | sK1(sK6,X0) = k1_funct_1(sK6,sK3(sK6,sK1(sK6,X0)))
    | k1_funct_1(sK6,sK3(sK6,sK1(sK6,X0))) != sK1(sK6,X0) ),
    inference(instantiation,[status(thm)],[c_4933])).

cnf(c_20621,plain,
    ( sK1(sK6,k1_xboole_0) != sK1(sK6,k1_xboole_0)
    | sK1(sK6,k1_xboole_0) = k1_funct_1(sK6,sK3(sK6,sK1(sK6,k1_xboole_0)))
    | k1_funct_1(sK6,sK3(sK6,sK1(sK6,k1_xboole_0))) != sK1(sK6,k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_20620])).

cnf(c_51969,plain,
    ( ~ r2_hidden(sK3(sK6,sK1(sK6,X0)),k1_relat_1(sK6))
    | ~ r2_hidden(sK1(sK6,X0),X0)
    | ~ v1_relat_1(sK6)
    | sK1(sK6,X0) != k1_funct_1(sK6,sK3(sK6,sK1(sK6,X0)))
    | k2_relat_1(sK6) = X0 ),
    inference(instantiation,[status(thm)],[c_743])).

cnf(c_51970,plain,
    ( sK1(sK6,X0) != k1_funct_1(sK6,sK3(sK6,sK1(sK6,X0)))
    | k2_relat_1(sK6) = X0
    | r2_hidden(sK3(sK6,sK1(sK6,X0)),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,X0),X0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_51969])).

cnf(c_51972,plain,
    ( sK1(sK6,k1_xboole_0) != k1_funct_1(sK6,sK3(sK6,sK1(sK6,k1_xboole_0)))
    | k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK3(sK6,sK1(sK6,k1_xboole_0)),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) != iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_51970])).

cnf(c_56043,plain,
    ( k1_funct_1(sK6,sK2(sK6,k1_xboole_0)) = sK1(sK6,k1_xboole_0)
    | k2_relat_1(sK6) = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4489,c_683,c_1426,c_1539,c_1591,c_4901,c_4905,c_4909,c_4936,c_8129,c_20621,c_51972])).

cnf(c_11,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_funct_1(X1)
    | ~ v1_relat_1(X1) ),
    inference(cnf_transformation,[],[f75])).

cnf(c_727,plain,
    ( ~ r2_hidden(X0,k1_relat_1(X1))
    | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
    | ~ v1_relat_1(X1)
    | sK6 != X1 ),
    inference(resolution_lifted,[status(thm)],[c_11,c_29])).

cnf(c_728,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
    | ~ v1_relat_1(sK6) ),
    inference(unflattening,[status(thm)],[c_727])).

cnf(c_1335,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_728])).

cnf(c_1700,plain,
    ( ~ r2_hidden(X0,k1_relat_1(sK6))
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) ),
    inference(backward_subsumption_resolution,[status(thm)],[c_1688,c_728])).

cnf(c_1721,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1700])).

cnf(c_2359,plain,
    ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
    | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_1335,c_1721])).

cnf(c_2360,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
    inference(renaming,[status(thm)],[c_2359])).

cnf(c_2363,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_2360,c_1346])).

cnf(c_2428,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK6),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_2363,c_1346])).

cnf(c_48704,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(sK5,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_48464,c_2428])).

cnf(c_51307,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1345,c_48704])).

cnf(c_56047,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),X0) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(superposition,[status(thm)],[c_56043,c_51307])).

cnf(c_663,plain,
    ( k2_relat_1(sK6) = X0
    | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,X0),X0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_662])).

cnf(c_665,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) = iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
    | v1_relat_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_663])).

cnf(c_56055,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56047])).

cnf(c_56498,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK1(sK6,k1_xboole_0),X0) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56047,c_665,c_1426,c_1539,c_1591,c_4901,c_4905,c_4909,c_4936,c_8129,c_20621,c_51972,c_56055])).

cnf(c_56501,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(instantiation,[status(thm)],[c_56498])).

cnf(c_56504,plain,
    ( k2_relat_1(sK6) = k1_xboole_0
    | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_56498,c_1426,c_1539,c_1591,c_4901,c_4905,c_4909,c_4936,c_8129,c_20621,c_51972,c_56501])).

cnf(c_56976,plain,
    ( sK5 != k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_10838,c_24,c_97,c_1396,c_1845,c_3064,c_5273,c_56504])).

cnf(c_8275,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK6))
    | r1_tarski(X1,k1_relat_1(sK6))
    | X1 != X0 ),
    inference(instantiation,[status(thm)],[c_1031])).

cnf(c_20765,plain,
    ( ~ r1_tarski(X0,k1_relat_1(sK6))
    | r1_tarski(sK4,k1_relat_1(sK6))
    | sK4 != X0 ),
    inference(instantiation,[status(thm)],[c_8275])).

cnf(c_60337,plain,
    ( ~ r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6))
    | r1_tarski(sK4,k1_relat_1(sK6))
    | sK4 != k1_relat_1(sK6) ),
    inference(instantiation,[status(thm)],[c_20765])).

cnf(c_60358,plain,
    ( sK4 != k1_relat_1(sK6)
    | r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60337])).

cnf(c_1789,plain,
    ( k1_funct_1(sK6,sK7(sK7(X0))) = sK7(X0)
    | r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1343])).

cnf(c_1856,plain,
    ( k1_funct_1(sK6,sK7(sK7(sK7(X0)))) = sK7(sK7(X0))
    | r2_hidden(X0,sK5) != iProver_top
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1569,c_1789])).

cnf(c_4668,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | k1_funct_1(sK6,sK7(sK7(sK7(sK1(sK6,sK5))))) = sK7(sK7(sK1(sK6,sK5)))
    | k2_relat_1(sK6) = sK5
    | r1_tarski(sK4,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_2906,c_1856])).

cnf(c_1465,plain,
    ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
    inference(equality_resolution,[status(thm)],[c_482])).

cnf(c_2356,plain,
    ( k1_relat_1(sK6) = sK4
    | sK5 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_868,c_1465])).

cnf(c_20699,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
    | sK5 = k1_xboole_0
    | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_2356,c_20691])).

cnf(c_59077,plain,
    ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4668,c_24,c_97,c_1396,c_1426,c_1527,c_1539,c_1591,c_1746,c_1845,c_1975,c_2215,c_3064,c_5273,c_20699,c_56504])).

cnf(c_1565,plain,
    ( r1_tarski(X0,X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1347,c_1348])).

cnf(c_48465,plain,
    ( r2_hidden(sK0(k2_relat_1(sK6),X0),X1) = iProver_top
    | r1_tarski(X2,X1) != iProver_top
    | r1_tarski(k2_relat_1(sK6),X0) = iProver_top
    | r1_tarski(sK5,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_47781,c_1346])).

cnf(c_49129,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r2_hidden(sK0(k2_relat_1(sK6),X1),X0) = iProver_top
    | r1_tarski(k2_relat_1(sK6),X1) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1496,c_48465])).

cnf(c_62332,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r1_tarski(k2_relat_1(sK6),X0) = iProver_top
    | r1_tarski(sK5,sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_49129,c_1348])).

cnf(c_62537,plain,
    ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
    | k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_62332,c_1496,c_48464])).

cnf(c_62538,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r1_tarski(k2_relat_1(sK6),X0) = iProver_top ),
    inference(renaming,[status(thm)],[c_62537])).

cnf(c_62576,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X1),X2) = iProver_top
    | r1_tarski(X0,X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_62538,c_2428])).

cnf(c_108532,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X1),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_1565,c_62576])).

cnf(c_108655,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,sK5),X0) = iProver_top ),
    inference(superposition,[status(thm)],[c_59077,c_108532])).

cnf(c_134759,plain,
    ( r1_tarski(X0,X1) != iProver_top
    | r2_hidden(sK1(sK6,sK5),X1) = iProver_top
    | k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0) ),
    inference(global_propositional_subsumption,[status(thm)],[c_6543,c_24,c_97,c_1396,c_1526,c_1527,c_1845,c_3064,c_4850,c_4859,c_5273,c_15451,c_23953,c_28226,c_44053,c_44055,c_56504,c_60358,c_108655])).

cnf(c_134760,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
    | r2_hidden(sK1(sK6,sK5),X1) = iProver_top
    | r1_tarski(X0,X1) != iProver_top ),
    inference(renaming,[status(thm)],[c_134759])).

cnf(c_134771,plain,
    ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6))
    | r2_hidden(sK1(sK6,sK5),X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_48464,c_134760])).

cnf(c_47787,plain,
    ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
    | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
    | r1_tarski(sK5,X1) != iProver_top ),
    inference(superposition,[status(thm)],[c_3619,c_2428])).

cnf(c_59080,plain,
    ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
    | r2_hidden(sK1(sK6,sK5),X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_59077,c_47787])).

cnf(c_135803,plain,
    ( r2_hidden(sK1(sK6,sK5),X0) = iProver_top
    | r1_tarski(sK5,X0) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_134771,c_24,c_97,c_1396,c_1526,c_1527,c_1845,c_3064,c_4850,c_4859,c_5273,c_15451,c_23953,c_44053,c_44055,c_56504,c_59080,c_60358])).

cnf(c_135916,plain,
    ( r1_tarski(sK5,sK5) != iProver_top
    | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_135803,c_22787])).

cnf(c_135779,plain,
    ( ~ r2_hidden(sK0(sK5,sK5),sK5)
    | r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_135782,plain,
    ( r2_hidden(sK0(sK5,sK5),sK5) != iProver_top
    | r1_tarski(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_135779])).

cnf(c_129003,plain,
    ( r2_hidden(sK0(sK5,X0),sK5)
    | r1_tarski(sK5,X0) ),
    inference(instantiation,[status(thm)],[c_1])).

cnf(c_135778,plain,
    ( r2_hidden(sK0(sK5,sK5),sK5)
    | r1_tarski(sK5,sK5) ),
    inference(instantiation,[status(thm)],[c_129003])).

cnf(c_135780,plain,
    ( r2_hidden(sK0(sK5,sK5),sK5) = iProver_top
    | r1_tarski(sK5,sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_135778])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_135916,c_135782,c_135780,c_60358,c_56976,c_44055,c_44053,c_15451,c_4859,c_4850,c_1527,c_1526])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : iproveropt_run.sh %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:43:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  % Running in FOF mode
% 39.95/5.48  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.95/5.48  
% 39.95/5.48  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 39.95/5.48  
% 39.95/5.48  ------  iProver source info
% 39.95/5.48  
% 39.95/5.48  git: date: 2020-06-30 10:37:57 +0100
% 39.95/5.48  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 39.95/5.48  git: non_committed_changes: false
% 39.95/5.48  git: last_make_outside_of_git: false
% 39.95/5.48  
% 39.95/5.48  ------ 
% 39.95/5.48  ------ Parsing...
% 39.95/5.48  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 39.95/5.48  
% 39.95/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe:4:0s pe_e  sf_s  rm: 4 0s  sf_e  pe_s  pe_e 
% 39.95/5.48  
% 39.95/5.48  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 39.95/5.48  
% 39.95/5.48  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 39.95/5.48  ------ Proving...
% 39.95/5.48  ------ Problem Properties 
% 39.95/5.48  
% 39.95/5.48  
% 39.95/5.48  clauses                                 21
% 39.95/5.48  conjectures                             3
% 39.95/5.48  EPR                                     2
% 39.95/5.48  Horn                                    16
% 39.95/5.48  unary                                   3
% 39.95/5.48  binary                                  7
% 39.95/5.48  lits                                    55
% 39.95/5.48  lits eq                                 23
% 39.95/5.48  fd_pure                                 0
% 39.95/5.48  fd_pseudo                               0
% 39.95/5.48  fd_cond                                 3
% 39.95/5.48  fd_pseudo_cond                          0
% 39.95/5.48  AC symbols                              0
% 39.95/5.48  
% 39.95/5.48  ------ Input Options Time Limit: Unbounded
% 39.95/5.48  
% 39.95/5.48  
% 39.95/5.48  ------ 
% 39.95/5.48  Current options:
% 39.95/5.48  ------ 
% 39.95/5.48  
% 39.95/5.48  
% 39.95/5.48  
% 39.95/5.48  
% 39.95/5.48  ------ Proving...
% 39.95/5.48  
% 39.95/5.48  
% 39.95/5.48  % SZS status Theorem for theBenchmark.p
% 39.95/5.48  
% 39.95/5.48  % SZS output start CNFRefutation for theBenchmark.p
% 39.95/5.48  
% 39.95/5.48  fof(f8,axiom,(
% 39.95/5.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 39.95/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.95/5.48  
% 39.95/5.48  fof(f14,plain,(
% 39.95/5.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v5_relat_1(X2,X1))),
% 39.95/5.48    inference(pure_predicate_removal,[],[f8])).
% 39.95/5.48  
% 39.95/5.48  fof(f22,plain,(
% 39.95/5.48    ! [X0,X1,X2] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.95/5.48    inference(ennf_transformation,[],[f14])).
% 39.95/5.48  
% 39.95/5.48  fof(f59,plain,(
% 39.95/5.48    ( ! [X2,X0,X1] : (v5_relat_1(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.95/5.48    inference(cnf_transformation,[],[f22])).
% 39.95/5.48  
% 39.95/5.48  fof(f4,axiom,(
% 39.95/5.48    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 39.95/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.95/5.48  
% 39.95/5.48  fof(f17,plain,(
% 39.95/5.48    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 39.95/5.48    inference(ennf_transformation,[],[f4])).
% 39.95/5.48  
% 39.95/5.48  fof(f33,plain,(
% 39.95/5.48    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 39.95/5.48    inference(nnf_transformation,[],[f17])).
% 39.95/5.48  
% 39.95/5.48  fof(f49,plain,(
% 39.95/5.48    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f33])).
% 39.95/5.48  
% 39.95/5.48  fof(f12,conjecture,(
% 39.95/5.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 39.95/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.95/5.48  
% 39.95/5.48  fof(f13,negated_conjecture,(
% 39.95/5.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (! [X3] : ~(! [X4] : ~(k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) & r2_hidden(X3,X1)) => k2_relset_1(X0,X1,X2) = X1))),
% 39.95/5.48    inference(negated_conjecture,[],[f12])).
% 39.95/5.48  
% 39.95/5.48  fof(f27,plain,(
% 39.95/5.48    ? [X0,X1,X2] : ((k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 39.95/5.48    inference(ennf_transformation,[],[f13])).
% 39.95/5.48  
% 39.95/5.48  fof(f28,plain,(
% 39.95/5.48    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 39.95/5.48    inference(flattening,[],[f27])).
% 39.95/5.48  
% 39.95/5.48  fof(f42,plain,(
% 39.95/5.48    ( ! [X2,X0] : (! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) => (k1_funct_1(X2,sK7(X3)) = X3 & r2_hidden(sK7(X3),X0)))) )),
% 39.95/5.48    introduced(choice_axiom,[])).
% 39.95/5.48  
% 39.95/5.48  fof(f41,plain,(
% 39.95/5.48    ? [X0,X1,X2] : (k2_relset_1(X0,X1,X2) != X1 & ! [X3] : (? [X4] : (k1_funct_1(X2,X4) = X3 & r2_hidden(X4,X0)) | ~r2_hidden(X3,X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : (? [X4] : (k1_funct_1(sK6,X4) = X3 & r2_hidden(X4,sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6))),
% 39.95/5.48    introduced(choice_axiom,[])).
% 39.95/5.48  
% 39.95/5.48  fof(f43,plain,(
% 39.95/5.48    k2_relset_1(sK4,sK5,sK6) != sK5 & ! [X3] : ((k1_funct_1(sK6,sK7(X3)) = X3 & r2_hidden(sK7(X3),sK4)) | ~r2_hidden(X3,sK5)) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) & v1_funct_2(sK6,sK4,sK5) & v1_funct_1(sK6)),
% 39.95/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f28,f42,f41])).
% 39.95/5.48  
% 39.95/5.48  fof(f70,plain,(
% 39.95/5.48    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)))),
% 39.95/5.48    inference(cnf_transformation,[],[f43])).
% 39.95/5.48  
% 39.95/5.48  fof(f3,axiom,(
% 39.95/5.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 39.95/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.95/5.48  
% 39.95/5.48  fof(f16,plain,(
% 39.95/5.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 39.95/5.48    inference(ennf_transformation,[],[f3])).
% 39.95/5.48  
% 39.95/5.48  fof(f48,plain,(
% 39.95/5.48    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f16])).
% 39.95/5.48  
% 39.95/5.48  fof(f5,axiom,(
% 39.95/5.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 39.95/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.95/5.48  
% 39.95/5.48  fof(f51,plain,(
% 39.95/5.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 39.95/5.48    inference(cnf_transformation,[],[f5])).
% 39.95/5.48  
% 39.95/5.48  fof(f1,axiom,(
% 39.95/5.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 39.95/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.95/5.48  
% 39.95/5.48  fof(f15,plain,(
% 39.95/5.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 39.95/5.48    inference(ennf_transformation,[],[f1])).
% 39.95/5.48  
% 39.95/5.48  fof(f29,plain,(
% 39.95/5.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) | ~r1_tarski(X0,X1)))),
% 39.95/5.48    inference(nnf_transformation,[],[f15])).
% 39.95/5.48  
% 39.95/5.48  fof(f30,plain,(
% 39.95/5.48    ! [X0,X1] : ((r1_tarski(X0,X1) | ? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 39.95/5.48    inference(rectify,[],[f29])).
% 39.95/5.48  
% 39.95/5.48  fof(f31,plain,(
% 39.95/5.48    ! [X1,X0] : (? [X2] : (~r2_hidden(X2,X1) & r2_hidden(X2,X0)) => (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0)))),
% 39.95/5.48    introduced(choice_axiom,[])).
% 39.95/5.48  
% 39.95/5.48  fof(f32,plain,(
% 39.95/5.48    ! [X0,X1] : ((r1_tarski(X0,X1) | (~r2_hidden(sK0(X0,X1),X1) & r2_hidden(sK0(X0,X1),X0))) & (! [X3] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0)) | ~r1_tarski(X0,X1)))),
% 39.95/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 39.95/5.48  
% 39.95/5.48  fof(f45,plain,(
% 39.95/5.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | r2_hidden(sK0(X0,X1),X0)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f32])).
% 39.95/5.48  
% 39.95/5.48  fof(f44,plain,(
% 39.95/5.48    ( ! [X0,X3,X1] : (r2_hidden(X3,X1) | ~r2_hidden(X3,X0) | ~r1_tarski(X0,X1)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f32])).
% 39.95/5.48  
% 39.95/5.48  fof(f46,plain,(
% 39.95/5.48    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~r2_hidden(sK0(X0,X1),X1)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f32])).
% 39.95/5.48  
% 39.95/5.48  fof(f72,plain,(
% 39.95/5.48    ( ! [X3] : (k1_funct_1(sK6,sK7(X3)) = X3 | ~r2_hidden(X3,sK5)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f43])).
% 39.95/5.48  
% 39.95/5.48  fof(f6,axiom,(
% 39.95/5.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))))),
% 39.95/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.95/5.48  
% 39.95/5.48  fof(f18,plain,(
% 39.95/5.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 39.95/5.48    inference(ennf_transformation,[],[f6])).
% 39.95/5.48  
% 39.95/5.48  fof(f19,plain,(
% 39.95/5.48    ! [X0] : (! [X1] : (k2_relat_1(X0) = X1 <=> ! [X2] : (r2_hidden(X2,X1) <=> ? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.95/5.48    inference(flattening,[],[f18])).
% 39.95/5.48  
% 39.95/5.48  fof(f34,plain,(
% 39.95/5.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X2] : ((r2_hidden(X2,X1) | ! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0)))) & (? [X3] : (k1_funct_1(X0,X3) = X2 & r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.95/5.48    inference(nnf_transformation,[],[f19])).
% 39.95/5.48  
% 39.95/5.48  fof(f35,plain,(
% 39.95/5.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.95/5.48    inference(rectify,[],[f34])).
% 39.95/5.48  
% 39.95/5.48  fof(f38,plain,(
% 39.95/5.48    ! [X5,X0] : (? [X7] : (k1_funct_1(X0,X7) = X5 & r2_hidden(X7,k1_relat_1(X0))) => (k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))))),
% 39.95/5.48    introduced(choice_axiom,[])).
% 39.95/5.48  
% 39.95/5.48  fof(f37,plain,(
% 39.95/5.48    ( ! [X2] : (! [X1,X0] : (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) => (k1_funct_1(X0,sK2(X0,X1)) = X2 & r2_hidden(sK2(X0,X1),k1_relat_1(X0))))) )),
% 39.95/5.48    introduced(choice_axiom,[])).
% 39.95/5.48  
% 39.95/5.48  fof(f36,plain,(
% 39.95/5.48    ! [X1,X0] : (? [X2] : ((! [X3] : (k1_funct_1(X0,X3) != X2 | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(X2,X1)) & (? [X4] : (k1_funct_1(X0,X4) = X2 & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(X2,X1))) => ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & (? [X4] : (k1_funct_1(X0,X4) = sK1(X0,X1) & r2_hidden(X4,k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1))))),
% 39.95/5.48    introduced(choice_axiom,[])).
% 39.95/5.48  
% 39.95/5.48  fof(f39,plain,(
% 39.95/5.48    ! [X0] : (! [X1] : ((k2_relat_1(X0) = X1 | ((! [X3] : (k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0))) | ~r2_hidden(sK1(X0,X1),X1)) & ((k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) & r2_hidden(sK2(X0,X1),k1_relat_1(X0))) | r2_hidden(sK1(X0,X1),X1)))) & (! [X5] : ((r2_hidden(X5,X1) | ! [X6] : (k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)))) & ((k1_funct_1(X0,sK3(X0,X5)) = X5 & r2_hidden(sK3(X0,X5),k1_relat_1(X0))) | ~r2_hidden(X5,X1))) | k2_relat_1(X0) != X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 39.95/5.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3])],[f35,f38,f37,f36])).
% 39.95/5.48  
% 39.95/5.48  fof(f55,plain,(
% 39.95/5.48    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | r2_hidden(sK2(X0,X1),k1_relat_1(X0)) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f39])).
% 39.95/5.48  
% 39.95/5.48  fof(f68,plain,(
% 39.95/5.48    v1_funct_1(sK6)),
% 39.95/5.48    inference(cnf_transformation,[],[f43])).
% 39.95/5.48  
% 39.95/5.48  fof(f69,plain,(
% 39.95/5.48    v1_funct_2(sK6,sK4,sK5)),
% 39.95/5.48    inference(cnf_transformation,[],[f43])).
% 39.95/5.48  
% 39.95/5.48  fof(f11,axiom,(
% 39.95/5.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 39.95/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.95/5.48  
% 39.95/5.48  fof(f25,plain,(
% 39.95/5.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.95/5.48    inference(ennf_transformation,[],[f11])).
% 39.95/5.48  
% 39.95/5.48  fof(f26,plain,(
% 39.95/5.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.95/5.48    inference(flattening,[],[f25])).
% 39.95/5.48  
% 39.95/5.48  fof(f40,plain,(
% 39.95/5.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.95/5.48    inference(nnf_transformation,[],[f26])).
% 39.95/5.48  
% 39.95/5.48  fof(f62,plain,(
% 39.95/5.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.95/5.48    inference(cnf_transformation,[],[f40])).
% 39.95/5.48  
% 39.95/5.48  fof(f9,axiom,(
% 39.95/5.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relat_1(X2) = k1_relset_1(X0,X1,X2))),
% 39.95/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.95/5.48  
% 39.95/5.48  fof(f23,plain,(
% 39.95/5.48    ! [X0,X1,X2] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.95/5.48    inference(ennf_transformation,[],[f9])).
% 39.95/5.48  
% 39.95/5.48  fof(f60,plain,(
% 39.95/5.48    ( ! [X2,X0,X1] : (k1_relat_1(X2) = k1_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.95/5.48    inference(cnf_transformation,[],[f23])).
% 39.95/5.48  
% 39.95/5.48  fof(f71,plain,(
% 39.95/5.48    ( ! [X3] : (r2_hidden(sK7(X3),sK4) | ~r2_hidden(X3,sK5)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f43])).
% 39.95/5.48  
% 39.95/5.48  fof(f56,plain,(
% 39.95/5.48    ( ! [X0,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1) | r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f39])).
% 39.95/5.48  
% 39.95/5.48  fof(f73,plain,(
% 39.95/5.48    k2_relset_1(sK4,sK5,sK6) != sK5),
% 39.95/5.48    inference(cnf_transformation,[],[f43])).
% 39.95/5.48  
% 39.95/5.48  fof(f10,axiom,(
% 39.95/5.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relat_1(X2) = k2_relset_1(X0,X1,X2))),
% 39.95/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.95/5.48  
% 39.95/5.48  fof(f24,plain,(
% 39.95/5.48    ! [X0,X1,X2] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 39.95/5.48    inference(ennf_transformation,[],[f10])).
% 39.95/5.48  
% 39.95/5.48  fof(f61,plain,(
% 39.95/5.48    ( ! [X2,X0,X1] : (k2_relat_1(X2) = k2_relset_1(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.95/5.48    inference(cnf_transformation,[],[f24])).
% 39.95/5.48  
% 39.95/5.48  fof(f57,plain,(
% 39.95/5.48    ( ! [X0,X3,X1] : (k2_relat_1(X0) = X1 | k1_funct_1(X0,X3) != sK1(X0,X1) | ~r2_hidden(X3,k1_relat_1(X0)) | ~r2_hidden(sK1(X0,X1),X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f39])).
% 39.95/5.48  
% 39.95/5.48  fof(f66,plain,(
% 39.95/5.48    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 39.95/5.48    inference(cnf_transformation,[],[f40])).
% 39.95/5.48  
% 39.95/5.48  fof(f80,plain,(
% 39.95/5.48    ( ! [X2,X0] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) )),
% 39.95/5.48    inference(equality_resolution,[],[f66])).
% 39.95/5.48  
% 39.95/5.48  fof(f2,axiom,(
% 39.95/5.48    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 39.95/5.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 39.95/5.48  
% 39.95/5.48  fof(f47,plain,(
% 39.95/5.48    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f2])).
% 39.95/5.48  
% 39.95/5.48  fof(f52,plain,(
% 39.95/5.48    ( ! [X0,X5,X1] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f39])).
% 39.95/5.48  
% 39.95/5.48  fof(f77,plain,(
% 39.95/5.48    ( ! [X0,X5] : (r2_hidden(sK3(X0,X5),k1_relat_1(X0)) | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.95/5.48    inference(equality_resolution,[],[f52])).
% 39.95/5.48  
% 39.95/5.48  fof(f53,plain,(
% 39.95/5.48    ( ! [X0,X5,X1] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,X1) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f39])).
% 39.95/5.48  
% 39.95/5.48  fof(f76,plain,(
% 39.95/5.48    ( ! [X0,X5] : (k1_funct_1(X0,sK3(X0,X5)) = X5 | ~r2_hidden(X5,k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.95/5.48    inference(equality_resolution,[],[f53])).
% 39.95/5.48  
% 39.95/5.48  fof(f54,plain,(
% 39.95/5.48    ( ! [X6,X0,X5,X1] : (r2_hidden(X5,X1) | k1_funct_1(X0,X6) != X5 | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.95/5.48    inference(cnf_transformation,[],[f39])).
% 39.95/5.48  
% 39.95/5.48  fof(f74,plain,(
% 39.95/5.48    ( ! [X6,X0,X1] : (r2_hidden(k1_funct_1(X0,X6),X1) | ~r2_hidden(X6,k1_relat_1(X0)) | k2_relat_1(X0) != X1 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.95/5.48    inference(equality_resolution,[],[f54])).
% 39.95/5.48  
% 39.95/5.48  fof(f75,plain,(
% 39.95/5.48    ( ! [X6,X0] : (r2_hidden(k1_funct_1(X0,X6),k2_relat_1(X0)) | ~r2_hidden(X6,k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 39.95/5.48    inference(equality_resolution,[],[f74])).
% 39.95/5.48  
% 39.95/5.48  cnf(c_15,plain,
% 39.95/5.48      ( v5_relat_1(X0,X1)
% 39.95/5.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) ),
% 39.95/5.48      inference(cnf_transformation,[],[f59]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_6,plain,
% 39.95/5.48      ( ~ v5_relat_1(X0,X1)
% 39.95/5.48      | r1_tarski(k2_relat_1(X0),X1)
% 39.95/5.48      | ~ v1_relat_1(X0) ),
% 39.95/5.48      inference(cnf_transformation,[],[f49]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_321,plain,
% 39.95/5.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.95/5.48      | r1_tarski(k2_relat_1(X0),X2)
% 39.95/5.48      | ~ v1_relat_1(X0) ),
% 39.95/5.48      inference(resolution,[status(thm)],[c_15,c_6]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_27,negated_conjecture,
% 39.95/5.48      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))) ),
% 39.95/5.48      inference(cnf_transformation,[],[f70]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_421,plain,
% 39.95/5.48      ( r1_tarski(k2_relat_1(X0),X1)
% 39.95/5.48      | ~ v1_relat_1(X0)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X2,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | sK6 != X0 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_321,c_27]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_422,plain,
% 39.95/5.48      ( r1_tarski(k2_relat_1(sK6),X0)
% 39.95/5.48      | ~ v1_relat_1(sK6)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_421]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1340,plain,
% 39.95/5.48      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | r1_tarski(k2_relat_1(sK6),X1) = iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_422]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4,plain,
% 39.95/5.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
% 39.95/5.48      | ~ v1_relat_1(X1)
% 39.95/5.48      | v1_relat_1(X0) ),
% 39.95/5.48      inference(cnf_transformation,[],[f48]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_406,plain,
% 39.95/5.48      ( ~ v1_relat_1(X0)
% 39.95/5.48      | v1_relat_1(X1)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0)
% 39.95/5.48      | sK6 != X1 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_4,c_27]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_407,plain,
% 39.95/5.48      ( ~ v1_relat_1(X0)
% 39.95/5.48      | v1_relat_1(sK6)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(X0) ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_406]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1029,plain,( X0 = X0 ),theory(equality) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1426,plain,
% 39.95/5.48      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) = k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1029]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1421,plain,
% 39.95/5.48      ( ~ v1_relat_1(k2_zfmisc_1(X0,X1))
% 39.95/5.48      | v1_relat_1(sK6)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(X0,X1)) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_407]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1538,plain,
% 39.95/5.48      ( ~ v1_relat_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | v1_relat_1(sK6)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1421]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_7,plain,
% 39.95/5.48      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 39.95/5.48      inference(cnf_transformation,[],[f51]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1590,plain,
% 39.95/5.48      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_7]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1688,plain,
% 39.95/5.48      ( v1_relat_1(sK6) ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_407,c_1426,c_1538,c_1590]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1699,plain,
% 39.95/5.48      ( r1_tarski(k2_relat_1(sK6),X0)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X1,X0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 39.95/5.48      inference(backward_subsumption_resolution,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_1688,c_422]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1724,plain,
% 39.95/5.48      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | r1_tarski(k2_relat_1(sK6),X1) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_1699]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3615,plain,
% 39.95/5.48      ( r1_tarski(k2_relat_1(sK6),X1) = iProver_top
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_1340,c_1724]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3616,plain,
% 39.95/5.48      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | r1_tarski(k2_relat_1(sK6),X1) = iProver_top ),
% 39.95/5.48      inference(renaming,[status(thm)],[c_3615]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3619,plain,
% 39.95/5.48      ( r1_tarski(k2_relat_1(sK6),sK5) = iProver_top ),
% 39.95/5.48      inference(equality_resolution,[status(thm)],[c_3616]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1,plain,
% 39.95/5.48      ( r2_hidden(sK0(X0,X1),X0) | r1_tarski(X0,X1) ),
% 39.95/5.48      inference(cnf_transformation,[],[f45]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1347,plain,
% 39.95/5.48      ( r2_hidden(sK0(X0,X1),X0) = iProver_top
% 39.95/5.48      | r1_tarski(X0,X1) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X0,X2) | ~ r1_tarski(X1,X2) ),
% 39.95/5.48      inference(cnf_transformation,[],[f44]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1346,plain,
% 39.95/5.48      ( r2_hidden(X0,X1) != iProver_top
% 39.95/5.48      | r2_hidden(X0,X2) = iProver_top
% 39.95/5.48      | r1_tarski(X1,X2) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1568,plain,
% 39.95/5.48      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 39.95/5.48      | r1_tarski(X0,X2) != iProver_top
% 39.95/5.48      | r1_tarski(X0,X1) = iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1347,c_1346]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1678,plain,
% 39.95/5.48      ( r2_hidden(sK0(X0,X1),X2) = iProver_top
% 39.95/5.48      | r1_tarski(X0,X3) != iProver_top
% 39.95/5.48      | r1_tarski(X3,X2) != iProver_top
% 39.95/5.48      | r1_tarski(X0,X1) = iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1568,c_1346]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_47781,plain,
% 39.95/5.48      ( r2_hidden(sK0(k2_relat_1(sK6),X0),X1) = iProver_top
% 39.95/5.48      | r1_tarski(k2_relat_1(sK6),X0) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,X1) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_3619,c_1678]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_0,plain,
% 39.95/5.48      ( ~ r2_hidden(sK0(X0,X1),X1) | r1_tarski(X0,X1) ),
% 39.95/5.48      inference(cnf_transformation,[],[f46]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1348,plain,
% 39.95/5.48      ( r2_hidden(sK0(X0,X1),X1) != iProver_top
% 39.95/5.48      | r1_tarski(X0,X1) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_0]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_48464,plain,
% 39.95/5.48      ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,X0) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_47781,c_1348]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_25,negated_conjecture,
% 39.95/5.48      ( ~ r2_hidden(X0,sK5) | k1_funct_1(sK6,sK7(X0)) = X0 ),
% 39.95/5.48      inference(cnf_transformation,[],[f72]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1343,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(X0)) = X0 | r2_hidden(X0,sK5) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1496,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 39.95/5.48      | r1_tarski(sK5,X0) = iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1347,c_1343]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_10,plain,
% 39.95/5.48      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 39.95/5.48      | r2_hidden(sK1(X0,X1),X1)
% 39.95/5.48      | ~ v1_funct_1(X0)
% 39.95/5.48      | ~ v1_relat_1(X0)
% 39.95/5.48      | k2_relat_1(X0) = X1 ),
% 39.95/5.48      inference(cnf_transformation,[],[f55]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_29,negated_conjecture,
% 39.95/5.48      ( v1_funct_1(sK6) ),
% 39.95/5.48      inference(cnf_transformation,[],[f68]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_661,plain,
% 39.95/5.48      ( r2_hidden(sK2(X0,X1),k1_relat_1(X0))
% 39.95/5.48      | r2_hidden(sK1(X0,X1),X1)
% 39.95/5.48      | ~ v1_relat_1(X0)
% 39.95/5.48      | k2_relat_1(X0) = X1
% 39.95/5.48      | sK6 != X0 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_10,c_29]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_662,plain,
% 39.95/5.48      ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0)
% 39.95/5.48      | ~ v1_relat_1(sK6)
% 39.95/5.48      | k2_relat_1(sK6) = X0 ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_661]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1339,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1703,plain,
% 39.95/5.48      ( r2_hidden(sK2(sK6,X0),k1_relat_1(sK6))
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0)
% 39.95/5.48      | k2_relat_1(sK6) = X0 ),
% 39.95/5.48      inference(backward_subsumption_resolution,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_1688,c_662]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1712,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_1703]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3183,plain,
% 39.95/5.48      ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 39.95/5.48      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | k2_relat_1(sK6) = X0 ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_1339,c_1712]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3184,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 39.95/5.48      inference(renaming,[status(thm)],[c_3183]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3194,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK2(sK6,X0),X1) = iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 39.95/5.48      | r1_tarski(k1_relat_1(sK6),X1) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_3184,c_1346]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3584,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK2(sK6,X0))) = sK2(sK6,X0)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 39.95/5.48      | r1_tarski(k1_relat_1(sK6),sK5) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_3194,c_1343]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4207,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK2(sK6,X0))) = sK2(sK6,X0)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X1) = iProver_top
% 39.95/5.48      | r1_tarski(X0,X1) != iProver_top
% 39.95/5.48      | r1_tarski(k1_relat_1(sK6),sK5) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_3584,c_1346]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_5702,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK2(sK6,X0))) = sK2(sK6,X0)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X1) = iProver_top
% 39.95/5.48      | r1_tarski(X2,X1) != iProver_top
% 39.95/5.48      | r1_tarski(X0,X2) != iProver_top
% 39.95/5.48      | r1_tarski(k1_relat_1(sK6),sK5) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_4207,c_1346]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_6543,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK2(sK6,sK5))) = sK2(sK6,sK5)
% 39.95/5.48      | k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 39.95/5.48      | k2_relat_1(sK6) = sK5
% 39.95/5.48      | r2_hidden(sK1(sK6,sK5),X1) = iProver_top
% 39.95/5.48      | r1_tarski(X0,X1) != iProver_top
% 39.95/5.48      | r1_tarski(k1_relat_1(sK6),sK5) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1496,c_5702]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1030,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1462,plain,
% 39.95/5.48      ( sK5 != X0 | sK5 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1030]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1526,plain,
% 39.95/5.48      ( sK5 != sK5 | sK5 = k1_xboole_0 | k1_xboole_0 != sK5 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1462]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1527,plain,
% 39.95/5.48      ( sK5 = sK5 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1029]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3248,plain,
% 39.95/5.48      ( X0 != X1 | X1 = X0 ),
% 39.95/5.48      inference(resolution,[status(thm)],[c_1030,c_1029]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_28,negated_conjecture,
% 39.95/5.48      ( v1_funct_2(sK6,sK4,sK5) ),
% 39.95/5.48      inference(cnf_transformation,[],[f69]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_23,plain,
% 39.95/5.48      ( ~ v1_funct_2(X0,X1,X2)
% 39.95/5.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.95/5.48      | k1_relset_1(X1,X2,X0) = X1
% 39.95/5.48      | k1_xboole_0 = X2 ),
% 39.95/5.48      inference(cnf_transformation,[],[f62]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_436,plain,
% 39.95/5.48      ( ~ v1_funct_2(X0,X1,X2)
% 39.95/5.48      | k1_relset_1(X1,X2,X0) = X1
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X1,X2)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | sK6 != X0
% 39.95/5.48      | k1_xboole_0 = X2 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_23,c_27]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_437,plain,
% 39.95/5.48      ( ~ v1_funct_2(sK6,X0,X1)
% 39.95/5.48      | k1_relset_1(X0,X1,sK6) = X0
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | k1_xboole_0 = X1 ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_436]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_799,plain,
% 39.95/5.48      ( k1_relset_1(X0,X1,sK6) = X0
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | sK6 != sK6
% 39.95/5.48      | sK5 != X1
% 39.95/5.48      | sK4 != X0
% 39.95/5.48      | k1_xboole_0 = X1 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_28,c_437]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_800,plain,
% 39.95/5.48      ( k1_relset_1(sK4,sK5,sK6) = sK4
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | k1_xboole_0 = sK5 ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_799]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_868,plain,
% 39.95/5.48      ( k1_relset_1(sK4,sK5,sK6) = sK4 | k1_xboole_0 = sK5 ),
% 39.95/5.48      inference(equality_resolution_simp,[status(thm)],[c_800]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4850,plain,
% 39.95/5.48      ( sK4 = k1_relset_1(sK4,sK5,sK6) | k1_xboole_0 = sK5 ),
% 39.95/5.48      inference(resolution,[status(thm)],[c_3248,c_868]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_16,plain,
% 39.95/5.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.95/5.48      | k1_relset_1(X1,X2,X0) = k1_relat_1(X0) ),
% 39.95/5.48      inference(cnf_transformation,[],[f60]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_481,plain,
% 39.95/5.48      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | sK6 != X2 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_16,c_27]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_482,plain,
% 39.95/5.48      ( k1_relset_1(X0,X1,sK6) = k1_relat_1(sK6)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_481]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1805,plain,
% 39.95/5.48      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 39.95/5.48      inference(resolution,[status(thm)],[c_482,c_1029]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4859,plain,
% 39.95/5.48      ( k1_relat_1(sK6) = k1_relset_1(sK4,sK5,sK6) ),
% 39.95/5.48      inference(resolution,[status(thm)],[c_3248,c_1805]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1531,plain,
% 39.95/5.48      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1030]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1910,plain,
% 39.95/5.48      ( X0 != k1_relset_1(sK4,sK5,sK6)
% 39.95/5.48      | sK4 = X0
% 39.95/5.48      | sK4 != k1_relset_1(sK4,sK5,sK6) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1531]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_15451,plain,
% 39.95/5.48      ( k1_relat_1(sK6) != k1_relset_1(sK4,sK5,sK6)
% 39.95/5.48      | sK4 != k1_relset_1(sK4,sK5,sK6)
% 39.95/5.48      | sK4 = k1_relat_1(sK6) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1910]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3187,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X1) = iProver_top
% 39.95/5.48      | r1_tarski(X0,X1) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_3184,c_1346]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_26,negated_conjecture,
% 39.95/5.48      ( ~ r2_hidden(X0,sK5) | r2_hidden(sK7(X0),sK4) ),
% 39.95/5.48      inference(cnf_transformation,[],[f71]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1342,plain,
% 39.95/5.48      ( r2_hidden(X0,sK5) != iProver_top
% 39.95/5.48      | r2_hidden(sK7(X0),sK4) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_26]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1569,plain,
% 39.95/5.48      ( r2_hidden(X0,sK5) != iProver_top
% 39.95/5.48      | r2_hidden(sK7(X0),X1) = iProver_top
% 39.95/5.48      | r1_tarski(sK4,X1) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1342,c_1346]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_9,plain,
% 39.95/5.48      ( r2_hidden(sK1(X0,X1),X1)
% 39.95/5.48      | ~ v1_funct_1(X0)
% 39.95/5.48      | ~ v1_relat_1(X0)
% 39.95/5.48      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 39.95/5.48      | k2_relat_1(X0) = X1 ),
% 39.95/5.48      inference(cnf_transformation,[],[f56]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_679,plain,
% 39.95/5.48      ( r2_hidden(sK1(X0,X1),X1)
% 39.95/5.48      | ~ v1_relat_1(X0)
% 39.95/5.48      | k1_funct_1(X0,sK2(X0,X1)) = sK1(X0,X1)
% 39.95/5.48      | k2_relat_1(X0) = X1
% 39.95/5.48      | sK6 != X0 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_9,c_29]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_680,plain,
% 39.95/5.48      ( r2_hidden(sK1(sK6,X0),X0)
% 39.95/5.48      | ~ v1_relat_1(sK6)
% 39.95/5.48      | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 39.95/5.48      | k2_relat_1(sK6) = X0 ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_679]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1338,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_681,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_680]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1539,plain,
% 39.95/5.48      ( k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | v1_relat_1(k2_zfmisc_1(sK4,sK5)) != iProver_top
% 39.95/5.48      | v1_relat_1(sK6) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_1538]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1591,plain,
% 39.95/5.48      ( v1_relat_1(k2_zfmisc_1(sK4,sK5)) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_1590]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2905,plain,
% 39.95/5.48      ( r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0) ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_1338,c_681,c_1426,c_1539,c_1591]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2906,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) = iProver_top ),
% 39.95/5.48      inference(renaming,[status(thm)],[c_2905]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2912,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 39.95/5.48      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 39.95/5.48      | k2_relat_1(sK6) = sK5 ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_2906,c_1343]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_24,negated_conjecture,
% 39.95/5.48      ( k2_relset_1(sK4,sK5,sK6) != sK5 ),
% 39.95/5.48      inference(cnf_transformation,[],[f73]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_17,plain,
% 39.95/5.48      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 39.95/5.48      | k2_relset_1(X1,X2,X0) = k2_relat_1(X0) ),
% 39.95/5.48      inference(cnf_transformation,[],[f61]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_472,plain,
% 39.95/5.48      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | sK6 != X2 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_17,c_27]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_473,plain,
% 39.95/5.48      ( k2_relset_1(X0,X1,sK6) = k2_relat_1(sK6)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5)) ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_472]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1396,plain,
% 39.95/5.48      ( k2_relset_1(sK4,sK5,sK6) = k2_relat_1(sK6) ),
% 39.95/5.48      inference(equality_resolution,[status(thm)],[c_473]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1491,plain,
% 39.95/5.48      ( X0 != X1 | sK5 != X1 | sK5 = X0 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1030]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1584,plain,
% 39.95/5.48      ( X0 != sK5 | sK5 = X0 | sK5 != sK5 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1491]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1746,plain,
% 39.95/5.48      ( k2_relat_1(sK6) != sK5 | sK5 = k2_relat_1(sK6) | sK5 != sK5 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1584]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1458,plain,
% 39.95/5.48      ( k2_relset_1(sK4,sK5,sK6) != X0
% 39.95/5.48      | k2_relset_1(sK4,sK5,sK6) = sK5
% 39.95/5.48      | sK5 != X0 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1030]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1845,plain,
% 39.95/5.48      ( k2_relset_1(sK4,sK5,sK6) != k2_relat_1(sK6)
% 39.95/5.48      | k2_relset_1(sK4,sK5,sK6) = sK5
% 39.95/5.48      | sK5 != k2_relat_1(sK6) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1458]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2967,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 39.95/5.48      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_2912,c_24,c_1396,c_1527,c_1746,c_1845]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2968,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 39.95/5.48      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 39.95/5.48      inference(renaming,[status(thm)],[c_2967]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_8,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 39.95/5.48      | ~ r2_hidden(sK1(X1,X2),X2)
% 39.95/5.48      | ~ v1_funct_1(X1)
% 39.95/5.48      | ~ v1_relat_1(X1)
% 39.95/5.48      | sK1(X1,X2) != k1_funct_1(X1,X0)
% 39.95/5.48      | k2_relat_1(X1) = X2 ),
% 39.95/5.48      inference(cnf_transformation,[],[f57]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_742,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 39.95/5.48      | ~ r2_hidden(sK1(X1,X2),X2)
% 39.95/5.48      | ~ v1_relat_1(X1)
% 39.95/5.48      | sK1(X1,X2) != k1_funct_1(X1,X0)
% 39.95/5.48      | k2_relat_1(X1) = X2
% 39.95/5.48      | sK6 != X1 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_8,c_29]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_743,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 39.95/5.48      | ~ r2_hidden(sK1(sK6,X1),X1)
% 39.95/5.48      | ~ v1_relat_1(sK6)
% 39.95/5.48      | sK1(sK6,X1) != k1_funct_1(sK6,X0)
% 39.95/5.48      | k2_relat_1(sK6) = X1 ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_742]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1334,plain,
% 39.95/5.48      ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_744,plain,
% 39.95/5.48      ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_743]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2236,plain,
% 39.95/5.48      ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 39.95/5.48      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | sK1(sK6,X0) != k1_funct_1(sK6,X1) ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_1334,c_744,c_1426,c_1539,c_1591]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2237,plain,
% 39.95/5.48      ( sK1(sK6,X0) != k1_funct_1(sK6,X1)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) != iProver_top ),
% 39.95/5.48      inference(renaming,[status(thm)],[c_2236]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2971,plain,
% 39.95/5.48      ( sK1(sK6,X0) != sK1(sK6,sK5)
% 39.95/5.48      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 39.95/5.48      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_2968,c_2237]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1973,plain,
% 39.95/5.48      ( r2_hidden(sK1(sK6,sK5),sK5)
% 39.95/5.48      | ~ v1_relat_1(sK6)
% 39.95/5.48      | k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 39.95/5.48      | k2_relat_1(sK6) = sK5 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_680]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1975,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 39.95/5.48      | k2_relat_1(sK6) = sK5
% 39.95/5.48      | r2_hidden(sK1(sK6,sK5),sK5) = iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_1973]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4934,plain,
% 39.95/5.48      ( sK1(sK6,X0) = sK1(sK6,X0) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1029]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_8018,plain,
% 39.95/5.48      ( sK1(sK6,sK5) = sK1(sK6,sK5) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_4934]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3553,plain,
% 39.95/5.48      ( sK1(sK6,X0) != X1
% 39.95/5.48      | sK1(sK6,X0) = k1_funct_1(sK6,X2)
% 39.95/5.48      | k1_funct_1(sK6,X2) != X1 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1030]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4933,plain,
% 39.95/5.48      ( sK1(sK6,X0) != sK1(sK6,X0)
% 39.95/5.48      | sK1(sK6,X0) = k1_funct_1(sK6,X1)
% 39.95/5.48      | k1_funct_1(sK6,X1) != sK1(sK6,X0) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_3553]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_13213,plain,
% 39.95/5.48      ( sK1(sK6,sK5) != sK1(sK6,sK5)
% 39.95/5.48      | sK1(sK6,sK5) = k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 39.95/5.48      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) != sK1(sK6,sK5) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_4933]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2219,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 39.95/5.48      | ~ r2_hidden(sK1(sK6,sK5),sK5)
% 39.95/5.48      | ~ v1_relat_1(sK6)
% 39.95/5.48      | sK1(sK6,sK5) != k1_funct_1(sK6,X0)
% 39.95/5.48      | k2_relat_1(sK6) = sK5 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_743]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_20247,plain,
% 39.95/5.48      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 39.95/5.48      | ~ r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
% 39.95/5.48      | ~ v1_relat_1(sK6)
% 39.95/5.48      | sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 39.95/5.48      | k2_relat_1(sK6) = sK5 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_2219]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_20248,plain,
% 39.95/5.48      ( sK1(sK6,sK5) != k1_funct_1(sK6,sK7(sK1(sK6,sK5)))
% 39.95/5.48      | k2_relat_1(sK6) = sK5
% 39.95/5.48      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 39.95/5.48      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_20247]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_20691,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 39.95/5.48      | r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_2971,c_24,c_1396,c_1426,c_1527,c_1539,c_1591,c_1746,
% 39.95/5.48                 c_1845,c_1975,c_2912,c_8018,c_13213,c_20248]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_20697,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 39.95/5.48      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 39.95/5.48      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1569,c_20691]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2214,plain,
% 39.95/5.48      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 39.95/5.48      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_26]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2215,plain,
% 39.95/5.48      ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 39.95/5.48      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_2214]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2213,plain,
% 39.95/5.48      ( ~ r2_hidden(sK1(sK6,sK5),sK5)
% 39.95/5.48      | k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_25]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2217,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK1(sK6,sK5))) = sK1(sK6,sK5)
% 39.95/5.48      | r2_hidden(sK1(sK6,sK5),sK5) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_2213]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2875,plain,
% 39.95/5.48      ( r2_hidden(sK7(sK1(sK6,sK5)),X0)
% 39.95/5.48      | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 39.95/5.48      | ~ r1_tarski(sK4,X0) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_2]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_20273,plain,
% 39.95/5.48      ( r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6))
% 39.95/5.48      | ~ r2_hidden(sK7(sK1(sK6,sK5)),sK4)
% 39.95/5.48      | ~ r1_tarski(sK4,k1_relat_1(sK6)) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_2875]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_20275,plain,
% 39.95/5.48      ( r2_hidden(sK7(sK1(sK6,sK5)),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top
% 39.95/5.48      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_20273]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_22787,plain,
% 39.95/5.48      ( r2_hidden(sK1(sK6,sK5),sK5) != iProver_top
% 39.95/5.48      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_20697,c_24,c_1396,c_1426,c_1527,c_1539,c_1591,c_1746,
% 39.95/5.48                 c_1845,c_2215,c_2217,c_8018,c_13213,c_20248,c_20275]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_22799,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = sK5
% 39.95/5.48      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,sK5) != iProver_top
% 39.95/5.48      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_3187,c_22787]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_22793,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = sK5
% 39.95/5.48      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_3184,c_22787]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_23953,plain,
% 39.95/5.48      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_22799,c_24,c_1396,c_1527,c_1746,c_1845,c_22793]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4876,plain,
% 39.95/5.48      ( ~ r2_hidden(sK1(sK6,X0),X1)
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X2)
% 39.95/5.48      | ~ r1_tarski(X1,X2) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_2]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_28225,plain,
% 39.95/5.48      ( ~ r2_hidden(sK1(sK6,sK5),X0)
% 39.95/5.48      | r2_hidden(sK1(sK6,sK5),X1)
% 39.95/5.48      | ~ r1_tarski(X0,X1) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_4876]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_28226,plain,
% 39.95/5.48      ( r2_hidden(sK1(sK6,sK5),X0) != iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,sK5),X1) = iProver_top
% 39.95/5.48      | r1_tarski(X0,X1) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_28225]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3489,plain,
% 39.95/5.48      ( r2_hidden(sK0(k1_relat_1(sK6),X0),k1_relat_1(sK6))
% 39.95/5.48      | r1_tarski(k1_relat_1(sK6),X0) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_44051,plain,
% 39.95/5.48      ( r2_hidden(sK0(k1_relat_1(sK6),k1_relat_1(sK6)),k1_relat_1(sK6))
% 39.95/5.48      | r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_3489]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_44053,plain,
% 39.95/5.48      ( r2_hidden(sK0(k1_relat_1(sK6),k1_relat_1(sK6)),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_44051]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_44052,plain,
% 39.95/5.48      ( ~ r2_hidden(sK0(k1_relat_1(sK6),k1_relat_1(sK6)),k1_relat_1(sK6))
% 39.95/5.48      | r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_0]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_44055,plain,
% 39.95/5.48      ( r2_hidden(sK0(k1_relat_1(sK6),k1_relat_1(sK6)),k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_44052]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1032,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,X1) | r2_hidden(X2,X3) | X2 != X0 | X3 != X1 ),
% 39.95/5.48      theory(equality) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1035,plain,
% 39.95/5.48      ( X0 != X1 | k2_relat_1(X0) = k2_relat_1(X1) ),
% 39.95/5.48      theory(equality) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3439,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 39.95/5.48      | r2_hidden(X2,k2_relat_1(X3))
% 39.95/5.48      | X2 != X0
% 39.95/5.48      | X3 != X1 ),
% 39.95/5.48      inference(resolution,[status(thm)],[c_1032,c_1035]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_10604,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 39.95/5.48      | r2_hidden(X2,k2_relat_1(k1_funct_1(sK6,sK7(X1))))
% 39.95/5.48      | ~ r2_hidden(X1,sK5)
% 39.95/5.48      | X2 != X0 ),
% 39.95/5.48      inference(resolution,[status(thm)],[c_3439,c_25]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1034,plain,
% 39.95/5.48      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 39.95/5.48      theory(equality) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_19,plain,
% 39.95/5.48      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 39.95/5.48      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)))
% 39.95/5.48      | k1_xboole_0 = X1
% 39.95/5.48      | k1_xboole_0 = X0 ),
% 39.95/5.48      inference(cnf_transformation,[],[f80]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_507,plain,
% 39.95/5.48      ( ~ v1_funct_2(X0,X1,k1_xboole_0)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X1,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | sK6 != X0
% 39.95/5.48      | k1_xboole_0 = X0
% 39.95/5.48      | k1_xboole_0 = X1 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_19,c_27]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_508,plain,
% 39.95/5.48      ( ~ v1_funct_2(sK6,X0,k1_xboole_0)
% 39.95/5.48      | k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | k1_xboole_0 = X0
% 39.95/5.48      | k1_xboole_0 = sK6 ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_507]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_810,plain,
% 39.95/5.48      ( k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | sK6 != sK6
% 39.95/5.48      | sK6 = k1_xboole_0
% 39.95/5.48      | sK5 != k1_xboole_0
% 39.95/5.48      | sK4 != X0
% 39.95/5.48      | k1_xboole_0 = X0 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_28,c_508]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_811,plain,
% 39.95/5.48      ( k1_zfmisc_1(k2_zfmisc_1(sK4,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK4,sK5))
% 39.95/5.48      | sK6 = k1_xboole_0
% 39.95/5.48      | sK5 != k1_xboole_0
% 39.95/5.48      | k1_xboole_0 = sK4 ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_810]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2051,plain,
% 39.95/5.48      ( k2_zfmisc_1(sK4,k1_xboole_0) != k2_zfmisc_1(sK4,sK5)
% 39.95/5.48      | sK6 = k1_xboole_0
% 39.95/5.48      | sK5 != k1_xboole_0
% 39.95/5.48      | k1_xboole_0 = sK4 ),
% 39.95/5.48      inference(resolution,[status(thm)],[c_1034,c_811]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1058,plain,
% 39.95/5.48      ( k1_xboole_0 = k1_xboole_0 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1029]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1530,plain,
% 39.95/5.48      ( sK4 = sK4 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1029]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1562,plain,
% 39.95/5.48      ( sK5 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK5 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1030]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1563,plain,
% 39.95/5.48      ( sK5 != k1_xboole_0
% 39.95/5.48      | k1_xboole_0 = sK5
% 39.95/5.48      | k1_xboole_0 != k1_xboole_0 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1562]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1036,plain,
% 39.95/5.48      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 39.95/5.48      theory(equality) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1544,plain,
% 39.95/5.48      ( X0 != sK5
% 39.95/5.48      | X1 != sK4
% 39.95/5.48      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK4,sK5) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1036]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2105,plain,
% 39.95/5.48      ( X0 != sK5
% 39.95/5.48      | k2_zfmisc_1(sK4,X0) = k2_zfmisc_1(sK4,sK5)
% 39.95/5.48      | sK4 != sK4 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1544]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2106,plain,
% 39.95/5.48      ( k2_zfmisc_1(sK4,k1_xboole_0) = k2_zfmisc_1(sK4,sK5)
% 39.95/5.48      | sK4 != sK4
% 39.95/5.48      | k1_xboole_0 != sK5 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_2105]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2379,plain,
% 39.95/5.48      ( sK6 = k1_xboole_0 | sK5 != k1_xboole_0 | k1_xboole_0 = sK4 ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_2051,c_1058,c_1530,c_1563,c_2106]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_10838,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,sK5)
% 39.95/5.48      | r2_hidden(sK6,k2_relat_1(k1_funct_1(sK6,sK7(X0))))
% 39.95/5.48      | ~ r2_hidden(k1_xboole_0,k2_relat_1(X0))
% 39.95/5.48      | sK5 != k1_xboole_0
% 39.95/5.48      | k1_xboole_0 = sK4 ),
% 39.95/5.48      inference(resolution,[status(thm)],[c_10604,c_2379]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3,plain,
% 39.95/5.48      ( r1_tarski(k1_xboole_0,X0) ),
% 39.95/5.48      inference(cnf_transformation,[],[f47]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_95,plain,
% 39.95/5.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_97,plain,
% 39.95/5.48      ( r1_tarski(k1_xboole_0,k1_xboole_0) = iProver_top ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_95]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3063,plain,
% 39.95/5.48      ( k2_relat_1(sK6) != X0 | sK5 != X0 | sK5 = k2_relat_1(sK6) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1491]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3064,plain,
% 39.95/5.48      ( k2_relat_1(sK6) != k1_xboole_0
% 39.95/5.48      | sK5 = k2_relat_1(sK6)
% 39.95/5.48      | sK5 != k1_xboole_0 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_3063]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1031,plain,
% 39.95/5.48      ( ~ r1_tarski(X0,X1) | r1_tarski(X2,X1) | X2 != X0 ),
% 39.95/5.48      theory(equality) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_5270,plain,
% 39.95/5.48      ( ~ r1_tarski(X0,X1) | r1_tarski(sK5,X1) | sK5 != X0 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1031]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_5271,plain,
% 39.95/5.48      ( sK5 != X0
% 39.95/5.48      | r1_tarski(X0,X1) != iProver_top
% 39.95/5.48      | r1_tarski(sK5,X1) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_5270]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_5273,plain,
% 39.95/5.48      ( sK5 != k1_xboole_0
% 39.95/5.48      | r1_tarski(sK5,k1_xboole_0) = iProver_top
% 39.95/5.48      | r1_tarski(k1_xboole_0,k1_xboole_0) != iProver_top ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_5271]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1345,plain,
% 39.95/5.48      ( r1_tarski(k1_xboole_0,X0) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2909,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X1) = iProver_top
% 39.95/5.48      | r1_tarski(X0,X1) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_2906,c_1346]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3098,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,X0)) = sK1(sK6,X0)
% 39.95/5.48      | k1_funct_1(sK6,sK7(sK1(sK6,X0))) = sK1(sK6,X0)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r1_tarski(X0,sK5) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_2909,c_1343]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4220,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,k1_xboole_0)) = sK1(sK6,k1_xboole_0)
% 39.95/5.48      | k1_funct_1(sK6,sK7(sK1(sK6,k1_xboole_0))) = sK1(sK6,k1_xboole_0)
% 39.95/5.48      | k2_relat_1(sK6) = k1_xboole_0 ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1345,c_3098]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4489,plain,
% 39.95/5.48      ( sK1(sK6,X0) != sK1(sK6,k1_xboole_0)
% 39.95/5.48      | k1_funct_1(sK6,sK2(sK6,k1_xboole_0)) = sK1(sK6,k1_xboole_0)
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | k2_relat_1(sK6) = k1_xboole_0
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 39.95/5.48      | r2_hidden(sK7(sK1(sK6,k1_xboole_0)),k1_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_4220,c_2237]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_683,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,k1_xboole_0)) = sK1(sK6,k1_xboole_0)
% 39.95/5.48      | k2_relat_1(sK6) = k1_xboole_0
% 39.95/5.48      | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_681]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_3508,plain,
% 39.95/5.48      ( ~ r2_hidden(sK1(sK6,X0),X0)
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X1)
% 39.95/5.48      | ~ r1_tarski(X0,X1) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_2]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4896,plain,
% 39.95/5.48      ( ~ r2_hidden(sK1(sK6,X0),X0)
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),k2_relat_1(sK6))
% 39.95/5.48      | ~ r1_tarski(X0,k2_relat_1(sK6)) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_3508]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4899,plain,
% 39.95/5.48      ( r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r1_tarski(X0,k2_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_4896]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4901,plain,
% 39.95/5.48      ( r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) != iProver_top
% 39.95/5.48      | r1_tarski(k1_xboole_0,k2_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_4899]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_13,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 39.95/5.48      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 39.95/5.48      | ~ v1_funct_1(X1)
% 39.95/5.48      | ~ v1_relat_1(X1) ),
% 39.95/5.48      inference(cnf_transformation,[],[f77]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_697,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 39.95/5.48      | r2_hidden(sK3(X1,X0),k1_relat_1(X1))
% 39.95/5.48      | ~ v1_relat_1(X1)
% 39.95/5.48      | sK6 != X1 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_13,c_29]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_698,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 39.95/5.48      | r2_hidden(sK3(sK6,X0),k1_relat_1(sK6))
% 39.95/5.48      | ~ v1_relat_1(sK6) ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_697]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4898,plain,
% 39.95/5.48      ( r2_hidden(sK3(sK6,sK1(sK6,X0)),k1_relat_1(sK6))
% 39.95/5.48      | ~ r2_hidden(sK1(sK6,X0),k2_relat_1(sK6))
% 39.95/5.48      | ~ v1_relat_1(sK6) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_698]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4903,plain,
% 39.95/5.48      ( r2_hidden(sK3(sK6,sK1(sK6,X0)),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),k2_relat_1(sK6)) != iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_4898]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4905,plain,
% 39.95/5.48      ( r2_hidden(sK3(sK6,sK1(sK6,k1_xboole_0)),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) != iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_4903]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_12,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 39.95/5.48      | ~ v1_funct_1(X1)
% 39.95/5.48      | ~ v1_relat_1(X1)
% 39.95/5.48      | k1_funct_1(X1,sK3(X1,X0)) = X0 ),
% 39.95/5.48      inference(cnf_transformation,[],[f76]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_712,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k2_relat_1(X1))
% 39.95/5.48      | ~ v1_relat_1(X1)
% 39.95/5.48      | k1_funct_1(X1,sK3(X1,X0)) = X0
% 39.95/5.48      | sK6 != X1 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_12,c_29]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_713,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k2_relat_1(sK6))
% 39.95/5.48      | ~ v1_relat_1(sK6)
% 39.95/5.48      | k1_funct_1(sK6,sK3(sK6,X0)) = X0 ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_712]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4897,plain,
% 39.95/5.48      ( ~ r2_hidden(sK1(sK6,X0),k2_relat_1(sK6))
% 39.95/5.48      | ~ v1_relat_1(sK6)
% 39.95/5.48      | k1_funct_1(sK6,sK3(sK6,sK1(sK6,X0))) = sK1(sK6,X0) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_713]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4907,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK3(sK6,sK1(sK6,X0))) = sK1(sK6,X0)
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),k2_relat_1(sK6)) != iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_4897]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4909,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK3(sK6,sK1(sK6,k1_xboole_0))) = sK1(sK6,k1_xboole_0)
% 39.95/5.48      | r2_hidden(sK1(sK6,k1_xboole_0),k2_relat_1(sK6)) != iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_4907]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4936,plain,
% 39.95/5.48      ( sK1(sK6,k1_xboole_0) = sK1(sK6,k1_xboole_0) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_4934]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_8126,plain,
% 39.95/5.48      ( r1_tarski(k1_xboole_0,k2_relat_1(sK6)) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_3]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_8129,plain,
% 39.95/5.48      ( r1_tarski(k1_xboole_0,k2_relat_1(sK6)) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_8126]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_20620,plain,
% 39.95/5.48      ( sK1(sK6,X0) != sK1(sK6,X0)
% 39.95/5.48      | sK1(sK6,X0) = k1_funct_1(sK6,sK3(sK6,sK1(sK6,X0)))
% 39.95/5.48      | k1_funct_1(sK6,sK3(sK6,sK1(sK6,X0))) != sK1(sK6,X0) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_4933]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_20621,plain,
% 39.95/5.48      ( sK1(sK6,k1_xboole_0) != sK1(sK6,k1_xboole_0)
% 39.95/5.48      | sK1(sK6,k1_xboole_0) = k1_funct_1(sK6,sK3(sK6,sK1(sK6,k1_xboole_0)))
% 39.95/5.48      | k1_funct_1(sK6,sK3(sK6,sK1(sK6,k1_xboole_0))) != sK1(sK6,k1_xboole_0) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_20620]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_51969,plain,
% 39.95/5.48      ( ~ r2_hidden(sK3(sK6,sK1(sK6,X0)),k1_relat_1(sK6))
% 39.95/5.48      | ~ r2_hidden(sK1(sK6,X0),X0)
% 39.95/5.48      | ~ v1_relat_1(sK6)
% 39.95/5.48      | sK1(sK6,X0) != k1_funct_1(sK6,sK3(sK6,sK1(sK6,X0)))
% 39.95/5.48      | k2_relat_1(sK6) = X0 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_743]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_51970,plain,
% 39.95/5.48      ( sK1(sK6,X0) != k1_funct_1(sK6,sK3(sK6,sK1(sK6,X0)))
% 39.95/5.48      | k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK3(sK6,sK1(sK6,X0)),k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) != iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_51969]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_51972,plain,
% 39.95/5.48      ( sK1(sK6,k1_xboole_0) != k1_funct_1(sK6,sK3(sK6,sK1(sK6,k1_xboole_0)))
% 39.95/5.48      | k2_relat_1(sK6) = k1_xboole_0
% 39.95/5.48      | r2_hidden(sK3(sK6,sK1(sK6,k1_xboole_0)),k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) != iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_51970]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_56043,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,k1_xboole_0)) = sK1(sK6,k1_xboole_0)
% 39.95/5.48      | k2_relat_1(sK6) = k1_xboole_0 ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_4489,c_683,c_1426,c_1539,c_1591,c_4901,c_4905,c_4909,
% 39.95/5.48                 c_4936,c_8129,c_20621,c_51972]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_11,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 39.95/5.48      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 39.95/5.48      | ~ v1_funct_1(X1)
% 39.95/5.48      | ~ v1_relat_1(X1) ),
% 39.95/5.48      inference(cnf_transformation,[],[f75]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_727,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k1_relat_1(X1))
% 39.95/5.48      | r2_hidden(k1_funct_1(X1,X0),k2_relat_1(X1))
% 39.95/5.48      | ~ v1_relat_1(X1)
% 39.95/5.48      | sK6 != X1 ),
% 39.95/5.48      inference(resolution_lifted,[status(thm)],[c_11,c_29]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_728,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 39.95/5.48      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6))
% 39.95/5.48      | ~ v1_relat_1(sK6) ),
% 39.95/5.48      inference(unflattening,[status(thm)],[c_727]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1335,plain,
% 39.95/5.48      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_728]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1700,plain,
% 39.95/5.48      ( ~ r2_hidden(X0,k1_relat_1(sK6))
% 39.95/5.48      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) ),
% 39.95/5.48      inference(backward_subsumption_resolution,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_1688,c_728]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1721,plain,
% 39.95/5.48      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_1700]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2359,plain,
% 39.95/5.48      ( r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r2_hidden(X0,k1_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_1335,c_1721]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2360,plain,
% 39.95/5.48      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(k1_funct_1(sK6,X0),k2_relat_1(sK6)) = iProver_top ),
% 39.95/5.48      inference(renaming,[status(thm)],[c_2359]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2363,plain,
% 39.95/5.48      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
% 39.95/5.48      | r1_tarski(k2_relat_1(sK6),X1) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_2360,c_1346]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2428,plain,
% 39.95/5.48      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
% 39.95/5.48      | r1_tarski(X2,X1) != iProver_top
% 39.95/5.48      | r1_tarski(k2_relat_1(sK6),X2) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_2363,c_1346]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_48704,plain,
% 39.95/5.48      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
% 39.95/5.48      | r1_tarski(X2,X1) != iProver_top
% 39.95/5.48      | r1_tarski(sK5,X2) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_48464,c_2428]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_51307,plain,
% 39.95/5.48      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1345,c_48704]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_56047,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = k1_xboole_0
% 39.95/5.48      | r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,k1_xboole_0),X0) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_56043,c_51307]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_663,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = X0
% 39.95/5.48      | r2_hidden(sK2(sK6,X0),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,X0),X0) = iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_662]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_665,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = k1_xboole_0
% 39.95/5.48      | r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) = iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
% 39.95/5.48      | v1_relat_1(sK6) != iProver_top ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_663]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_56055,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = k1_xboole_0
% 39.95/5.48      | r2_hidden(sK2(sK6,k1_xboole_0),k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_56047]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_56498,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = k1_xboole_0
% 39.95/5.48      | r2_hidden(sK1(sK6,k1_xboole_0),X0) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_56047,c_665,c_1426,c_1539,c_1591,c_4901,c_4905,c_4909,
% 39.95/5.48                 c_4936,c_8129,c_20621,c_51972,c_56055]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_56501,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = k1_xboole_0
% 39.95/5.48      | r2_hidden(sK1(sK6,k1_xboole_0),k1_xboole_0) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_56498]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_56504,plain,
% 39.95/5.48      ( k2_relat_1(sK6) = k1_xboole_0
% 39.95/5.48      | r1_tarski(sK5,k1_xboole_0) != iProver_top ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_56498,c_1426,c_1539,c_1591,c_4901,c_4905,c_4909,
% 39.95/5.48                 c_4936,c_8129,c_20621,c_51972,c_56501]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_56976,plain,
% 39.95/5.48      ( sK5 != k1_xboole_0 ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_10838,c_24,c_97,c_1396,c_1845,c_3064,c_5273,c_56504]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_8275,plain,
% 39.95/5.48      ( ~ r1_tarski(X0,k1_relat_1(sK6))
% 39.95/5.48      | r1_tarski(X1,k1_relat_1(sK6))
% 39.95/5.48      | X1 != X0 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1031]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_20765,plain,
% 39.95/5.48      ( ~ r1_tarski(X0,k1_relat_1(sK6))
% 39.95/5.48      | r1_tarski(sK4,k1_relat_1(sK6))
% 39.95/5.48      | sK4 != X0 ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_8275]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_60337,plain,
% 39.95/5.48      ( ~ r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6))
% 39.95/5.48      | r1_tarski(sK4,k1_relat_1(sK6))
% 39.95/5.48      | sK4 != k1_relat_1(sK6) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_20765]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_60358,plain,
% 39.95/5.48      ( sK4 != k1_relat_1(sK6)
% 39.95/5.48      | r1_tarski(k1_relat_1(sK6),k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r1_tarski(sK4,k1_relat_1(sK6)) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_60337]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1789,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK7(X0))) = sK7(X0)
% 39.95/5.48      | r2_hidden(X0,sK5) != iProver_top
% 39.95/5.48      | r1_tarski(sK4,sK5) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1569,c_1343]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1856,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK7(sK7(X0)))) = sK7(sK7(X0))
% 39.95/5.48      | r2_hidden(X0,sK5) != iProver_top
% 39.95/5.48      | r1_tarski(sK4,sK5) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1569,c_1789]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_4668,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 39.95/5.48      | k1_funct_1(sK6,sK7(sK7(sK7(sK1(sK6,sK5))))) = sK7(sK7(sK1(sK6,sK5)))
% 39.95/5.48      | k2_relat_1(sK6) = sK5
% 39.95/5.48      | r1_tarski(sK4,sK5) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_2906,c_1856]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1465,plain,
% 39.95/5.48      ( k1_relset_1(sK4,sK5,sK6) = k1_relat_1(sK6) ),
% 39.95/5.48      inference(equality_resolution,[status(thm)],[c_482]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_2356,plain,
% 39.95/5.48      ( k1_relat_1(sK6) = sK4 | sK5 = k1_xboole_0 ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_868,c_1465]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_20699,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5)
% 39.95/5.48      | sK5 = k1_xboole_0
% 39.95/5.48      | r2_hidden(sK7(sK1(sK6,sK5)),sK4) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_2356,c_20691]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_59077,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK2(sK6,sK5)) = sK1(sK6,sK5) ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_4668,c_24,c_97,c_1396,c_1426,c_1527,c_1539,c_1591,
% 39.95/5.48                 c_1746,c_1845,c_1975,c_2215,c_3064,c_5273,c_20699,
% 39.95/5.48                 c_56504]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_1565,plain,
% 39.95/5.48      ( r1_tarski(X0,X0) = iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1347,c_1348]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_48465,plain,
% 39.95/5.48      ( r2_hidden(sK0(k2_relat_1(sK6),X0),X1) = iProver_top
% 39.95/5.48      | r1_tarski(X2,X1) != iProver_top
% 39.95/5.48      | r1_tarski(k2_relat_1(sK6),X0) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,X2) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_47781,c_1346]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_49129,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 39.95/5.48      | r2_hidden(sK0(k2_relat_1(sK6),X1),X0) = iProver_top
% 39.95/5.48      | r1_tarski(k2_relat_1(sK6),X1) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,sK5) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1496,c_48465]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_62332,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 39.95/5.48      | r1_tarski(k2_relat_1(sK6),X0) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,sK5) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_49129,c_1348]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_62537,plain,
% 39.95/5.48      ( r1_tarski(k2_relat_1(sK6),X0) = iProver_top
% 39.95/5.48      | k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0) ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_62332,c_1496,c_48464]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_62538,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 39.95/5.48      | r1_tarski(k2_relat_1(sK6),X0) = iProver_top ),
% 39.95/5.48      inference(renaming,[status(thm)],[c_62537]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_62576,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 39.95/5.48      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(k1_funct_1(sK6,X1),X2) = iProver_top
% 39.95/5.48      | r1_tarski(X0,X2) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_62538,c_2428]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_108532,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 39.95/5.48      | r2_hidden(X1,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(k1_funct_1(sK6,X1),X0) = iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_1565,c_62576]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_108655,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 39.95/5.48      | r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,sK5),X0) = iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_59077,c_108532]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_134759,plain,
% 39.95/5.48      ( r1_tarski(X0,X1) != iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,sK5),X1) = iProver_top
% 39.95/5.48      | k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0) ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_6543,c_24,c_97,c_1396,c_1526,c_1527,c_1845,c_3064,
% 39.95/5.48                 c_4850,c_4859,c_5273,c_15451,c_23953,c_28226,c_44053,
% 39.95/5.48                 c_44055,c_56504,c_60358,c_108655]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_134760,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK0(sK5,X0))) = sK0(sK5,X0)
% 39.95/5.48      | r2_hidden(sK1(sK6,sK5),X1) = iProver_top
% 39.95/5.48      | r1_tarski(X0,X1) != iProver_top ),
% 39.95/5.48      inference(renaming,[status(thm)],[c_134759]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_134771,plain,
% 39.95/5.48      ( k1_funct_1(sK6,sK7(sK0(sK5,k2_relat_1(sK6)))) = sK0(sK5,k2_relat_1(sK6))
% 39.95/5.48      | r2_hidden(sK1(sK6,sK5),X0) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,X0) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_48464,c_134760]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_47787,plain,
% 39.95/5.48      ( r2_hidden(X0,k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(k1_funct_1(sK6,X0),X1) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,X1) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_3619,c_2428]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_59080,plain,
% 39.95/5.48      ( r2_hidden(sK2(sK6,sK5),k1_relat_1(sK6)) != iProver_top
% 39.95/5.48      | r2_hidden(sK1(sK6,sK5),X0) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,X0) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_59077,c_47787]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_135803,plain,
% 39.95/5.48      ( r2_hidden(sK1(sK6,sK5),X0) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,X0) != iProver_top ),
% 39.95/5.48      inference(global_propositional_subsumption,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_134771,c_24,c_97,c_1396,c_1526,c_1527,c_1845,c_3064,
% 39.95/5.48                 c_4850,c_4859,c_5273,c_15451,c_23953,c_44053,c_44055,
% 39.95/5.48                 c_56504,c_59080,c_60358]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_135916,plain,
% 39.95/5.48      ( r1_tarski(sK5,sK5) != iProver_top
% 39.95/5.48      | r1_tarski(sK4,k1_relat_1(sK6)) != iProver_top ),
% 39.95/5.48      inference(superposition,[status(thm)],[c_135803,c_22787]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_135779,plain,
% 39.95/5.48      ( ~ r2_hidden(sK0(sK5,sK5),sK5) | r1_tarski(sK5,sK5) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_0]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_135782,plain,
% 39.95/5.48      ( r2_hidden(sK0(sK5,sK5),sK5) != iProver_top
% 39.95/5.48      | r1_tarski(sK5,sK5) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_135779]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_129003,plain,
% 39.95/5.48      ( r2_hidden(sK0(sK5,X0),sK5) | r1_tarski(sK5,X0) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_1]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_135778,plain,
% 39.95/5.48      ( r2_hidden(sK0(sK5,sK5),sK5) | r1_tarski(sK5,sK5) ),
% 39.95/5.48      inference(instantiation,[status(thm)],[c_129003]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(c_135780,plain,
% 39.95/5.48      ( r2_hidden(sK0(sK5,sK5),sK5) = iProver_top
% 39.95/5.48      | r1_tarski(sK5,sK5) = iProver_top ),
% 39.95/5.48      inference(predicate_to_equality,[status(thm)],[c_135778]) ).
% 39.95/5.48  
% 39.95/5.48  cnf(contradiction,plain,
% 39.95/5.48      ( $false ),
% 39.95/5.48      inference(minisat,
% 39.95/5.48                [status(thm)],
% 39.95/5.48                [c_135916,c_135782,c_135780,c_60358,c_56976,c_44055,
% 39.95/5.48                 c_44053,c_15451,c_4859,c_4850,c_1527,c_1526]) ).
% 39.95/5.48  
% 39.95/5.48  
% 39.95/5.48  % SZS output end CNFRefutation for theBenchmark.p
% 39.95/5.48  
% 39.95/5.48  ------                               Statistics
% 39.95/5.48  
% 39.95/5.48  ------ Selected
% 39.95/5.48  
% 39.95/5.48  total_time:                             4.932
% 39.95/5.48  
%------------------------------------------------------------------------------
