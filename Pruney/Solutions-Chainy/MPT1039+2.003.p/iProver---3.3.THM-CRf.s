%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:43 EST 2020

% Result     : Theorem 11.48s
% Output     : CNFRefutation 11.48s
% Verified   : 
% Statistics : Number of formulae       :  275 (254706 expanded)
%              Number of clauses        :  217 (78824 expanded)
%              Number of leaves         :   15 (61844 expanded)
%              Depth                    :   42
%              Number of atoms          : 1108 (1964098 expanded)
%              Number of equality atoms :  595 (403103 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal clause size      :   24 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_2(X4,X0,X1)
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f6,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X3) )
           => ~ ( ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                      & v1_funct_2(X4,X0,X1)
                      & v1_funct_1(X4) )
                   => ~ ( r1_partfun1(X3,X4)
                        & r1_partfun1(X2,X4) ) )
                & r1_partfun1(X2,X3)
                & ( k1_xboole_0 = X1
                 => k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f5])).

fof(f15,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f16,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f15])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(X2,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X4,X0,X1)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(X2,X3)
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X3) )
     => ( ! [X4] :
            ( ~ r1_partfun1(sK6,X4)
            | ~ r1_partfun1(X2,X4)
            | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X4,X0,X1)
            | ~ v1_funct_1(X4) )
        & r1_partfun1(X2,sK6)
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(sK6) ) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ! [X4] :
                ( ~ r1_partfun1(X3,X4)
                | ~ r1_partfun1(X2,X4)
                | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                | ~ v1_funct_2(X4,X0,X1)
                | ~ v1_funct_1(X4) )
            & r1_partfun1(X2,X3)
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ! [X4] :
              ( ~ r1_partfun1(X3,X4)
              | ~ r1_partfun1(sK5,X4)
              | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
              | ~ v1_funct_2(X4,sK3,sK4)
              | ~ v1_funct_1(X4) )
          & r1_partfun1(sK5,X3)
          & ( k1_xboole_0 = sK3
            | k1_xboole_0 != sK4 )
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
          & v1_funct_1(X3) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ! [X4] :
        ( ~ r1_partfun1(sK6,X4)
        | ~ r1_partfun1(sK5,X4)
        | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
        | ~ v1_funct_2(X4,sK3,sK4)
        | ~ v1_funct_1(X4) )
    & r1_partfun1(sK5,sK6)
    & ( k1_xboole_0 = sK3
      | k1_xboole_0 != sK4 )
    & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK6)
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    & v1_funct_1(sK5) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f26,f25])).

fof(f49,plain,(
    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f27])).

fof(f47,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f27])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ~ ( ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                    & v1_funct_1(X4) )
                 => ~ ( r1_partfun1(X3,X4)
                      & r1_partfun1(X2,X4)
                      & v1_partfun1(X4,X0) ) )
              & r1_partfun1(X2,X3)
              & ( k1_xboole_0 = X1
               => k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ? [X4] :
              ( r1_partfun1(X3,X4)
              & r1_partfun1(X2,X4)
              & v1_partfun1(X4,X0)
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X4) )
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f13])).

fof(f17,plain,(
    ! [X3,X2,X0,X1] :
      ( ? [X4] :
          ( r1_partfun1(X3,X4)
          & r1_partfun1(X2,X4)
          & v1_partfun1(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X4) )
      | ~ sP0(X3,X2,X0,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( sP0(X3,X2,X0,X1)
          | ~ r1_partfun1(X2,X3)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 )
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f14,f17])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X0,X1)
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f46,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f27])).

fof(f48,plain,(
    v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    r1_partfun1(sK5,sK6) ),
    inference(cnf_transformation,[],[f27])).

fof(f21,plain,(
    ! [X3,X2,X0,X1] :
      ( ? [X4] :
          ( r1_partfun1(X3,X4)
          & r1_partfun1(X2,X4)
          & v1_partfun1(X4,X0)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X4) )
      | ~ sP0(X3,X2,X0,X1) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f22,plain,(
    ! [X0,X1,X2,X3] :
      ( ? [X4] :
          ( r1_partfun1(X0,X4)
          & r1_partfun1(X1,X4)
          & v1_partfun1(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
          & v1_funct_1(X4) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f21])).

fof(f23,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( r1_partfun1(X0,X4)
          & r1_partfun1(X1,X4)
          & v1_partfun1(X4,X2)
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
          & v1_funct_1(X4) )
     => ( r1_partfun1(X0,sK2(X0,X1,X2,X3))
        & r1_partfun1(X1,sK2(X0,X1,X2,X3))
        & v1_partfun1(sK2(X0,X1,X2,X3),X2)
        & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(sK2(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r1_partfun1(X0,sK2(X0,X1,X2,X3))
        & r1_partfun1(X1,sK2(X0,X1,X2,X3))
        & v1_partfun1(sK2(X0,X1,X2,X3),X2)
        & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(sK2(X0,X1,X2,X3)) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X0,sK2(X0,X1,X2,X3))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f40,plain,(
    ! [X2,X0,X3,X1] :
      ( m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f39,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_funct_1(sK2(X0,X1,X2,X3))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_1(X3) )
         => ( ( r1_partfun1(X2,X3)
              & v1_partfun1(X3,X0)
              & v1_partfun1(X2,X0) )
           => X2 = X3 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f11,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( X2 = X3
          | ~ r1_partfun1(X2,X3)
          | ~ v1_partfun1(X3,X0)
          | ~ v1_partfun1(X2,X0)
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f11])).

fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( X2 = X3
      | ~ r1_partfun1(X2,X3)
      | ~ v1_partfun1(X3,X0)
      | ~ v1_partfun1(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f41,plain,(
    ! [X2,X0,X3,X1] :
      ( v1_partfun1(sK2(X0,X1,X2,X3),X2)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ~ ( ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ~ r1_partfun1(X2,X3) )
          & ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f9,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f10,plain,(
    ! [X0,X1,X2] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f19,plain,(
    ! [X2,X1,X0] :
      ( ? [X3] :
          ( r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( r1_partfun1(X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK1(X0,X1,X2),X0,X1)
        & v1_funct_1(sK1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( r1_partfun1(X2,sK1(X0,X1,X2))
        & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK1(X0,X1,X2),X0,X1)
        & v1_funct_1(sK1(X0,X1,X2)) )
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f19])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( r1_partfun1(X2,sK1(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f30,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK1(X0,X1,X2))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f28,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK1(X0,X1,X2),X0,X1)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f34,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f42,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_partfun1(X1,sK2(X0,X1,X2,X3))
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f52,plain,(
    ! [X4] :
      ( ~ r1_partfun1(sK6,X4)
      | ~ r1_partfun1(sK5,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
      | ~ v1_funct_2(X4,sK3,sK4)
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f50,plain,
    ( k1_xboole_0 = sK3
    | k1_xboole_0 != sK4 ),
    inference(cnf_transformation,[],[f27])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X3,X2,X0,X1)
      | ~ r1_partfun1(X2,X3)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f58,plain,(
    ! [X2,X3,X1] :
      ( sP0(X3,X2,k1_xboole_0,X1)
      | ~ r1_partfun1(X2,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f45])).

fof(f35,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f55,plain,(
    ! [X2,X1] :
      ( m1_subset_1(sK1(k1_xboole_0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f35])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( r1_partfun1(X2,sK1(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f54,plain,(
    ! [X2,X1] :
      ( r1_partfun1(X2,sK1(k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f37])).

fof(f31,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(sK1(X0,X1,X2))
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f57,plain,(
    ! [X2,X1] :
      ( v1_funct_1(sK1(k1_xboole_0,X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f31])).

fof(f29,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f8])).

fof(f53,plain,(
    ! [X2,X1] :
      ( v1_partfun1(X2,k1_xboole_0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_2(X2,k1_xboole_0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f29])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(sK1(X0,X1,X2),X0,X1)
      | k1_xboole_0 != X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f56,plain,(
    ! [X2,X1] :
      ( v1_funct_2(sK1(k1_xboole_0,X1,X2),k1_xboole_0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(equality_resolution,[],[f33])).

cnf(c_21,negated_conjecture,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f49])).

cnf(c_1593,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_23,negated_conjecture,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(cnf_transformation,[],[f47])).

cnf(c_1591,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_17,plain,
    ( sP0(X0,X1,X2,X3)
    | ~ r1_partfun1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X3 ),
    inference(cnf_transformation,[],[f44])).

cnf(c_1595,plain,
    ( k1_xboole_0 = X0
    | sP0(X1,X2,X3,X0) = iProver_top
    | r1_partfun1(X2,X1) != iProver_top
    | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X2) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_3261,plain,
    ( sK4 = k1_xboole_0
    | sP0(X0,sK5,sK3,sK4) = iProver_top
    | r1_partfun1(sK5,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_1591,c_1595])).

cnf(c_24,negated_conjecture,
    ( v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_25,plain,
    ( v1_funct_1(sK5) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_24])).

cnf(c_4296,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r1_partfun1(sK5,X0) != iProver_top
    | sP0(X0,sK5,sK3,sK4) = iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3261,c_25])).

cnf(c_4297,plain,
    ( sK4 = k1_xboole_0
    | sP0(X0,sK5,sK3,sK4) = iProver_top
    | r1_partfun1(sK5,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_4296])).

cnf(c_4308,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK6,sK5,sK3,sK4) = iProver_top
    | r1_partfun1(sK5,sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1593,c_4297])).

cnf(c_22,negated_conjecture,
    ( v1_funct_1(sK6) ),
    inference(cnf_transformation,[],[f48])).

cnf(c_27,plain,
    ( v1_funct_1(sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_19,negated_conjecture,
    ( r1_partfun1(sK5,sK6) ),
    inference(cnf_transformation,[],[f51])).

cnf(c_29,plain,
    ( r1_partfun1(sK5,sK6) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_4438,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK6,sK5,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_4308,c_27,c_29])).

cnf(c_11,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_partfun1(X0,sK2(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_1601,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(X0,sK2(X0,X1,X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_11])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
    inference(cnf_transformation,[],[f40])).

cnf(c_1598,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_3260,plain,
    ( sK4 = k1_xboole_0
    | sP0(X0,sK6,sK3,sK4) = iProver_top
    | r1_partfun1(sK6,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_1593,c_1595])).

cnf(c_3826,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | r1_partfun1(sK6,X0) != iProver_top
    | sP0(X0,sK6,sK3,sK4) = iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_3260,c_27])).

cnf(c_3827,plain,
    ( sK4 = k1_xboole_0
    | sP0(X0,sK6,sK3,sK4) = iProver_top
    | r1_partfun1(sK6,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_3826])).

cnf(c_3837,plain,
    ( sK4 = k1_xboole_0
    | sP0(X0,X1,sK3,sK4) != iProver_top
    | sP0(sK2(X0,X1,sK3,sK4),sK6,sK3,sK4) = iProver_top
    | r1_partfun1(sK6,sK2(X0,X1,sK3,sK4)) != iProver_top
    | v1_funct_1(sK2(X0,X1,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_3827])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | v1_funct_1(sK2(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f39])).

cnf(c_1597,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_funct_1(sK2(X0,X1,X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_4614,plain,
    ( sK4 = k1_xboole_0
    | sP0(X0,X1,sK3,sK4) != iProver_top
    | sP0(sK2(X0,X1,sK3,sK4),sK6,sK3,sK4) = iProver_top
    | r1_partfun1(sK6,sK2(X0,X1,sK3,sK4)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_3837,c_1597])).

cnf(c_10,plain,
    ( ~ r1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ v1_partfun1(X1,X2)
    | ~ v1_partfun1(X0,X2)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X1)
    | X1 = X0 ),
    inference(cnf_transformation,[],[f38])).

cnf(c_1602,plain,
    ( X0 = X1
    | r1_partfun1(X1,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_partfun1(X0,X2) != iProver_top
    | v1_partfun1(X1,X2) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_10])).

cnf(c_3335,plain,
    ( sK2(X0,X1,X2,X3) = X4
    | sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(sK2(X0,X1,X2,X3),X4) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_partfun1(X4,X2) != iProver_top
    | v1_partfun1(sK2(X0,X1,X2,X3),X2) != iProver_top
    | v1_funct_1(X4) != iProver_top
    | v1_funct_1(sK2(X0,X1,X2,X3)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_1602])).

cnf(c_39,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_funct_1(sK2(X0,X1,X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | v1_partfun1(sK2(X0,X1,X2,X3),X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_45,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_partfun1(sK2(X0,X1,X2,X3),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_8682,plain,
    ( v1_funct_1(X4) != iProver_top
    | sK2(X0,X1,X2,X3) = X4
    | sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(sK2(X0,X1,X2,X3),X4) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_partfun1(X4,X2) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3335,c_39,c_45])).

cnf(c_8683,plain,
    ( sK2(X0,X1,X2,X3) = X4
    | sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(sK2(X0,X1,X2,X3),X4) != iProver_top
    | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_partfun1(X4,X2) != iProver_top
    | v1_funct_1(X4) != iProver_top ),
    inference(renaming,[status(thm)],[c_8682])).

cnf(c_8694,plain,
    ( sK2(sK2(X0,X1,X2,X3),X4,X5,X6) = sK2(X0,X1,X2,X3)
    | sP0(X0,X1,X2,X3) != iProver_top
    | sP0(sK2(X0,X1,X2,X3),X4,X5,X6) != iProver_top
    | m1_subset_1(sK2(sK2(X0,X1,X2,X3),X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_partfun1(sK2(sK2(X0,X1,X2,X3),X4,X5,X6),X2) != iProver_top
    | v1_funct_1(sK2(sK2(X0,X1,X2,X3),X4,X5,X6)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1601,c_8683])).

cnf(c_13400,plain,
    ( sK2(sK2(X0,X1,X2,X3),X4,X5,X6) = sK2(X0,X1,X2,X3)
    | sP0(X0,X1,X2,X3) != iProver_top
    | sP0(sK2(X0,X1,X2,X3),X4,X5,X6) != iProver_top
    | m1_subset_1(sK2(sK2(X0,X1,X2,X3),X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
    | v1_partfun1(sK2(sK2(X0,X1,X2,X3),X4,X5,X6),X2) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8694,c_1597])).

cnf(c_13404,plain,
    ( sK2(sK2(X0,X1,X2,X3),X4,X2,X3) = sK2(X0,X1,X2,X3)
    | sP0(X0,X1,X2,X3) != iProver_top
    | sP0(sK2(X0,X1,X2,X3),X4,X2,X3) != iProver_top
    | v1_partfun1(sK2(sK2(X0,X1,X2,X3),X4,X2,X3),X2) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_13400])).

cnf(c_1599,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | v1_partfun1(sK2(X0,X1,X2,X3),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_13453,plain,
    ( sK2(sK2(X0,X1,X2,X3),X4,X2,X3) = sK2(X0,X1,X2,X3)
    | sP0(X0,X1,X2,X3) != iProver_top
    | sP0(sK2(X0,X1,X2,X3),X4,X2,X3) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_13404,c_1599])).

cnf(c_13461,plain,
    ( sK2(sK2(X0,X1,sK3,sK4),sK6,sK3,sK4) = sK2(X0,X1,sK3,sK4)
    | sK4 = k1_xboole_0
    | sP0(X0,X1,sK3,sK4) != iProver_top
    | r1_partfun1(sK6,sK2(X0,X1,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4614,c_13453])).

cnf(c_13833,plain,
    ( sK2(sK2(sK6,X0,sK3,sK4),sK6,sK3,sK4) = sK2(sK6,X0,sK3,sK4)
    | sK4 = k1_xboole_0
    | sP0(sK6,X0,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1601,c_13461])).

cnf(c_14148,plain,
    ( sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) = sK2(sK6,sK5,sK3,sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4438,c_13833])).

cnf(c_3,plain,
    ( r1_partfun1(X0,sK1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f36])).

cnf(c_1607,plain,
    ( k1_xboole_0 = X0
    | r1_partfun1(X1,sK1(X2,X0,X1)) = iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_3])).

cnf(c_2938,plain,
    ( k1_xboole_0 = X0
    | sP0(X1,X2,X3,X0) != iProver_top
    | r1_partfun1(sK2(X1,X2,X3,X0),sK1(X3,X0,sK2(X1,X2,X3,X0))) = iProver_top
    | v1_funct_1(sK2(X1,X2,X3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_1607])).

cnf(c_5871,plain,
    ( k1_xboole_0 = X0
    | sP0(X1,X2,X3,X0) != iProver_top
    | r1_partfun1(sK2(X1,X2,X3,X0),sK1(X3,X0,sK2(X1,X2,X3,X0))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2938,c_1597])).

cnf(c_8697,plain,
    ( sK1(X0,X1,sK2(X2,X3,X0,X1)) = sK2(X2,X3,X0,X1)
    | k1_xboole_0 = X1
    | sP0(X2,X3,X0,X1) != iProver_top
    | m1_subset_1(sK1(X0,X1,sK2(X2,X3,X0,X1)),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
    | v1_partfun1(sK1(X0,X1,sK2(X2,X3,X0,X1)),X0) != iProver_top
    | v1_funct_1(sK1(X0,X1,sK2(X2,X3,X0,X1))) != iProver_top ),
    inference(superposition,[status(thm)],[c_5871,c_8683])).

cnf(c_9,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(sK1(X1,X2,X0))
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f30])).

cnf(c_1603,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_funct_1(X1) != iProver_top
    | v1_funct_1(sK1(X2,X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_9])).

cnf(c_2895,plain,
    ( k1_xboole_0 = X0
    | sP0(X1,X2,X3,X0) != iProver_top
    | v1_funct_1(sK2(X1,X2,X3,X0)) != iProver_top
    | v1_funct_1(sK1(X3,X0,sK2(X1,X2,X3,X0))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_1603])).

cnf(c_3492,plain,
    ( k1_xboole_0 = X0
    | sP0(X1,X2,X3,X0) != iProver_top
    | v1_funct_1(sK1(X3,X0,sK2(X1,X2,X3,X0))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2895,c_1597])).

cnf(c_1,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f28])).

cnf(c_7,plain,
    ( v1_funct_2(sK1(X0,X1,X2),X0,X1)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(X2)
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f32])).

cnf(c_307,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X3)
    | X4 != X1
    | X5 != X2
    | sK1(X4,X5,X3) != X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X5 ),
    inference(resolution_lifted,[status(thm)],[c_1,c_7])).

cnf(c_308,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(sK1(X1,X2,X0),X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1(X1,X2,X0))
    | k1_xboole_0 = X2 ),
    inference(unflattening,[status(thm)],[c_307])).

cnf(c_5,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f34])).

cnf(c_310,plain,
    ( ~ v1_funct_1(X0)
    | v1_partfun1(sK1(X1,X2,X0),X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | k1_xboole_0 = X2 ),
    inference(global_propositional_subsumption,[status(thm)],[c_308,c_9,c_5])).

cnf(c_311,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_partfun1(sK1(X1,X2,X0),X1)
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = X2 ),
    inference(renaming,[status(thm)],[c_310])).

cnf(c_1588,plain,
    ( k1_xboole_0 = X0
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
    | v1_partfun1(sK1(X2,X0,X1),X2) = iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_311])).

cnf(c_2762,plain,
    ( k1_xboole_0 = X0
    | sP0(X1,X2,X3,X0) != iProver_top
    | v1_partfun1(sK1(X3,X0,sK2(X1,X2,X3,X0)),X3) = iProver_top
    | v1_funct_1(sK2(X1,X2,X3,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_1588])).

cnf(c_4503,plain,
    ( k1_xboole_0 = X0
    | sP0(X1,X2,X3,X0) != iProver_top
    | v1_partfun1(sK1(X3,X0,sK2(X1,X2,X3,X0)),X3) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2762,c_1597])).

cnf(c_27851,plain,
    ( sK1(X0,X1,sK2(X2,X3,X0,X1)) = sK2(X2,X3,X0,X1)
    | k1_xboole_0 = X1
    | sP0(X2,X3,X0,X1) != iProver_top
    | m1_subset_1(sK1(X0,X1,sK2(X2,X3,X0,X1)),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8697,c_3492,c_4503])).

cnf(c_27857,plain,
    ( sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) = sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)
    | sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14148,c_27851])).

cnf(c_1170,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_2061,plain,
    ( X0 != X1
    | sK4 != X1
    | sK4 = X0 ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_2737,plain,
    ( X0 != sK4
    | sK4 = X0
    | sK4 != sK4 ),
    inference(instantiation,[status(thm)],[c_2061])).

cnf(c_2739,plain,
    ( sK4 != sK4
    | sK4 = k1_xboole_0
    | k1_xboole_0 != sK4 ),
    inference(instantiation,[status(thm)],[c_2737])).

cnf(c_1169,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_2738,plain,
    ( sK4 = sK4 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_14497,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) != iProver_top
    | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14148,c_1597])).

cnf(c_14221,plain,
    ( ~ sP0(sK6,sK5,sK3,sK4)
    | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_14222,plain,
    ( sP0(sK6,sK5,sK3,sK4) != iProver_top
    | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14221])).

cnf(c_15578,plain,
    ( sK4 = k1_xboole_0
    | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14497,c_27,c_29,c_4308,c_14222])).

cnf(c_14493,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) != iProver_top
    | m1_subset_1(sK2(sK6,sK5,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_14148,c_1598])).

cnf(c_14217,plain,
    ( ~ sP0(sK6,sK5,sK3,sK4)
    | m1_subset_1(sK2(sK6,sK5,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_14230,plain,
    ( sP0(sK6,sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK2(sK6,sK5,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14217])).

cnf(c_16688,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK2(sK6,sK5,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14493,c_27,c_29,c_4308,c_14230])).

cnf(c_16701,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) = iProver_top
    | r1_partfun1(sK6,sK2(sK6,sK5,sK3,sK4)) != iProver_top
    | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16688,c_3827])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | r1_partfun1(X1,sK2(X0,X1,X2,X3)) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_1600,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r1_partfun1(X1,sK2(X0,X1,X2,X3)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_14495,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) != iProver_top
    | r1_partfun1(sK6,sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14148,c_1600])).

cnf(c_14220,plain,
    ( ~ sP0(sK6,sK5,sK3,sK4)
    | r1_partfun1(sK6,sK2(sK6,sK5,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_14224,plain,
    ( sP0(sK6,sK5,sK3,sK4) != iProver_top
    | r1_partfun1(sK6,sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14220])).

cnf(c_15590,plain,
    ( sK4 = k1_xboole_0
    | r1_partfun1(sK6,sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14495,c_27,c_29,c_4308,c_14224])).

cnf(c_16943,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16701,c_15578,c_15590])).

cnf(c_1911,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
    | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_5])).

cnf(c_20361,plain,
    ( ~ m1_subset_1(sK2(sK6,sK5,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | m1_subset_1(sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(sK2(sK6,sK5,sK3,sK4))
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1911])).

cnf(c_20371,plain,
    ( k1_xboole_0 = sK4
    | m1_subset_1(sK2(sK6,sK5,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top
    | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20361])).

cnf(c_36958,plain,
    ( sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) = sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_27857,c_2739,c_2738,c_15578,c_16688,c_16943,c_20371])).

cnf(c_36962,plain,
    ( sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) = sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4))
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14148,c_36958])).

cnf(c_4307,plain,
    ( sK4 = k1_xboole_0
    | sP0(X0,X1,sK3,sK4) != iProver_top
    | sP0(sK2(X0,X1,sK3,sK4),sK5,sK3,sK4) = iProver_top
    | r1_partfun1(sK5,sK2(X0,X1,sK3,sK4)) != iProver_top
    | v1_funct_1(sK2(X0,X1,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_4297])).

cnf(c_4624,plain,
    ( sK4 = k1_xboole_0
    | sP0(X0,X1,sK3,sK4) != iProver_top
    | sP0(sK2(X0,X1,sK3,sK4),sK5,sK3,sK4) = iProver_top
    | r1_partfun1(sK5,sK2(X0,X1,sK3,sK4)) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_4307,c_1597])).

cnf(c_13462,plain,
    ( sK2(sK2(X0,X1,sK3,sK4),sK5,sK3,sK4) = sK2(X0,X1,sK3,sK4)
    | sK4 = k1_xboole_0
    | sP0(X0,X1,sK3,sK4) != iProver_top
    | r1_partfun1(sK5,sK2(X0,X1,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_4624,c_13453])).

cnf(c_14498,plain,
    ( sK2(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4),sK5,sK3,sK4) = sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)
    | sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) != iProver_top
    | r1_partfun1(sK5,sK2(sK6,sK5,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_14148,c_13462])).

cnf(c_13873,plain,
    ( sK2(sK2(X0,sK5,sK3,sK4),sK5,sK3,sK4) = sK2(X0,sK5,sK3,sK4)
    | sK4 = k1_xboole_0
    | sP0(X0,sK5,sK3,sK4) != iProver_top ),
    inference(superposition,[status(thm)],[c_1600,c_13462])).

cnf(c_14450,plain,
    ( sK2(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) = sK2(sK6,sK5,sK3,sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4438,c_13873])).

cnf(c_14848,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) != iProver_top
    | r1_partfun1(sK5,sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_14450,c_1600])).

cnf(c_14219,plain,
    ( ~ sP0(sK6,sK5,sK3,sK4)
    | r1_partfun1(sK5,sK2(sK6,sK5,sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_14226,plain,
    ( sP0(sK6,sK5,sK3,sK4) != iProver_top
    | r1_partfun1(sK5,sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14219])).

cnf(c_16552,plain,
    ( sK4 = k1_xboole_0
    | r1_partfun1(sK5,sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_14848,c_27,c_29,c_4308,c_14226])).

cnf(c_19096,plain,
    ( sK2(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4),sK5,sK3,sK4) = sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_14498,c_16552,c_16943])).

cnf(c_19100,plain,
    ( sK2(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) = sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)
    | sK4 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_14148,c_19096])).

cnf(c_19490,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) != iProver_top
    | m1_subset_1(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_19100,c_1598])).

cnf(c_16700,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) = iProver_top
    | r1_partfun1(sK5,sK2(sK6,sK5,sK3,sK4)) != iProver_top
    | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_16688,c_4297])).

cnf(c_16921,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_16700,c_15578,c_16552])).

cnf(c_21198,plain,
    ( sK4 = k1_xboole_0
    | m1_subset_1(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19490,c_16921])).

cnf(c_21211,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4),sK5,sK3,sK4) = iProver_top
    | r1_partfun1(sK5,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) != iProver_top
    | v1_funct_1(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21198,c_4297])).

cnf(c_19492,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) != iProver_top
    | r1_partfun1(sK5,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19100,c_1600])).

cnf(c_19494,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) != iProver_top
    | v1_funct_1(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) = iProver_top ),
    inference(superposition,[status(thm)],[c_19100,c_1597])).

cnf(c_21408,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4),sK5,sK3,sK4) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_21211,c_16921,c_19492,c_19494])).

cnf(c_37727,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4)),sK5,sK3,sK4) = iProver_top ),
    inference(superposition,[status(thm)],[c_36962,c_21408])).

cnf(c_20622,plain,
    ( sK4 = k1_xboole_0
    | r1_partfun1(sK5,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_19492,c_16921])).

cnf(c_18,negated_conjecture,
    ( ~ v1_funct_2(X0,sK3,sK4)
    | ~ r1_partfun1(sK5,X0)
    | ~ r1_partfun1(sK6,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f52])).

cnf(c_358,plain,
    ( ~ r1_partfun1(sK5,X0)
    | ~ r1_partfun1(sK6,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | sK1(X2,X3,X1) != X0
    | sK4 != X3
    | sK3 != X2
    | k1_xboole_0 = X3 ),
    inference(resolution_lifted,[status(thm)],[c_7,c_18])).

cnf(c_359,plain,
    ( ~ r1_partfun1(sK5,sK1(sK3,sK4,X0))
    | ~ r1_partfun1(sK6,sK1(sK3,sK4,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ m1_subset_1(sK1(sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1(sK3,sK4,X0))
    | k1_xboole_0 = sK4 ),
    inference(unflattening,[status(thm)],[c_358])).

cnf(c_377,plain,
    ( ~ r1_partfun1(sK5,sK1(sK3,sK4,X0))
    | ~ r1_partfun1(sK6,sK1(sK3,sK4,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X0)
    | k1_xboole_0 = sK4 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_359,c_9,c_5])).

cnf(c_1586,plain,
    ( k1_xboole_0 = sK4
    | r1_partfun1(sK5,sK1(sK3,sK4,X0)) != iProver_top
    | r1_partfun1(sK6,sK1(sK3,sK4,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_377])).

cnf(c_21215,plain,
    ( sK4 = k1_xboole_0
    | r1_partfun1(sK5,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top
    | r1_partfun1(sK6,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top
    | v1_funct_1(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) != iProver_top ),
    inference(superposition,[status(thm)],[c_21198,c_1586])).

cnf(c_21612,plain,
    ( r1_partfun1(sK6,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top
    | r1_partfun1(sK5,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top
    | sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_21215,c_16921,c_19494])).

cnf(c_21613,plain,
    ( sK4 = k1_xboole_0
    | r1_partfun1(sK5,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top
    | r1_partfun1(sK6,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top ),
    inference(renaming,[status(thm)],[c_21612])).

cnf(c_21619,plain,
    ( sK4 = k1_xboole_0
    | r1_partfun1(sK5,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top
    | r1_partfun1(sK6,sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_14148,c_21613])).

cnf(c_36999,plain,
    ( sK4 = k1_xboole_0
    | r1_partfun1(sK5,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) != iProver_top
    | r1_partfun1(sK6,sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4))) != iProver_top ),
    inference(superposition,[status(thm)],[c_36958,c_21619])).

cnf(c_37666,plain,
    ( sK4 = k1_xboole_0
    | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) != iProver_top
    | r1_partfun1(sK6,sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4))) = iProver_top ),
    inference(superposition,[status(thm)],[c_36962,c_1600])).

cnf(c_38361,plain,
    ( sK4 = k1_xboole_0 ),
    inference(global_propositional_subsumption,[status(thm)],[c_37727,c_16943,c_20622,c_36999,c_37666])).

cnf(c_38563,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_38361,c_1593])).

cnf(c_20,negated_conjecture,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 = sK3 ),
    inference(cnf_transformation,[],[f50])).

cnf(c_38565,plain,
    ( sK3 = k1_xboole_0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(demodulation,[status(thm)],[c_38361,c_20])).

cnf(c_38566,plain,
    ( sK3 = k1_xboole_0 ),
    inference(equality_resolution_simp,[status(thm)],[c_38565])).

cnf(c_38572,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38563,c_38566])).

cnf(c_38564,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
    inference(demodulation,[status(thm)],[c_38361,c_1591])).

cnf(c_38569,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38564,c_38566])).

cnf(c_16,plain,
    ( sP0(X0,X1,k1_xboole_0,X2)
    | ~ r1_partfun1(X1,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f58])).

cnf(c_1596,plain,
    ( sP0(X0,X1,k1_xboole_0,X2) = iProver_top
    | r1_partfun1(X1,X0) != iProver_top
    | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_16])).

cnf(c_38750,plain,
    ( sP0(X0,sK5,k1_xboole_0,k1_xboole_0) = iProver_top
    | r1_partfun1(sK5,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK5) != iProver_top ),
    inference(superposition,[status(thm)],[c_38569,c_1596])).

cnf(c_39480,plain,
    ( v1_funct_1(X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | r1_partfun1(sK5,X0) != iProver_top
    | sP0(X0,sK5,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_38750,c_25])).

cnf(c_39481,plain,
    ( sP0(X0,sK5,k1_xboole_0,k1_xboole_0) = iProver_top
    | r1_partfun1(sK5,X0) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(renaming,[status(thm)],[c_39480])).

cnf(c_39493,plain,
    ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) = iProver_top
    | r1_partfun1(sK5,sK6) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(superposition,[status(thm)],[c_38572,c_39481])).

cnf(c_26,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_28,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_21])).

cnf(c_1188,plain,
    ( k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_1874,plain,
    ( sK4 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK4 ),
    inference(instantiation,[status(thm)],[c_1170])).

cnf(c_1875,plain,
    ( sK4 != k1_xboole_0
    | k1_xboole_0 = sK4
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1874])).

cnf(c_2077,plain,
    ( sK6 = sK6 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_2098,plain,
    ( sK5 = sK5 ),
    inference(instantiation,[status(thm)],[c_1169])).

cnf(c_1925,plain,
    ( sP0(X0,sK5,k1_xboole_0,X1)
    | ~ r1_partfun1(sK5,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK5) ),
    inference(instantiation,[status(thm)],[c_16])).

cnf(c_2175,plain,
    ( sP0(sK6,sK5,k1_xboole_0,X0)
    | ~ r1_partfun1(sK5,sK6)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_1(sK5)
    | ~ v1_funct_1(sK6) ),
    inference(instantiation,[status(thm)],[c_1925])).

cnf(c_2176,plain,
    ( sP0(sK6,sK5,k1_xboole_0,X0) = iProver_top
    | r1_partfun1(sK5,sK6) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2175])).

cnf(c_2178,plain,
    ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) = iProver_top
    | r1_partfun1(sK5,sK6) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK5) != iProver_top
    | v1_funct_1(sK6) != iProver_top ),
    inference(instantiation,[status(thm)],[c_2176])).

cnf(c_1173,plain,
    ( X0 != X1
    | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
    theory(equality)).

cnf(c_2858,plain,
    ( X0 != k2_zfmisc_1(sK3,sK4)
    | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_1173])).

cnf(c_3734,plain,
    ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK3,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_2858])).

cnf(c_3736,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK3,sK4)
    | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
    inference(instantiation,[status(thm)],[c_3734])).

cnf(c_1172,plain,
    ( X0 != X1
    | X2 != X3
    | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
    theory(equality)).

cnf(c_3735,plain,
    ( X0 != sK4
    | X1 != sK3
    | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK3,sK4) ),
    inference(instantiation,[status(thm)],[c_1172])).

cnf(c_3737,plain,
    ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK3,sK4)
    | k1_xboole_0 != sK4
    | k1_xboole_0 != sK3 ),
    inference(instantiation,[status(thm)],[c_3735])).

cnf(c_1174,plain,
    ( ~ m1_subset_1(X0,X1)
    | m1_subset_1(X2,X3)
    | X2 != X0
    | X3 != X1 ),
    theory(equality)).

cnf(c_1891,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | X0 != sK5 ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_2097,plain,
    ( m1_subset_1(sK5,X0)
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | X0 != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_1891])).

cnf(c_5119,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != sK5 ),
    inference(instantiation,[status(thm)],[c_2097])).

cnf(c_5121,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5119])).

cnf(c_5123,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK5 != sK5
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5121])).

cnf(c_1886,plain,
    ( m1_subset_1(X0,X1)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | X1 != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | X0 != sK6 ),
    inference(instantiation,[status(thm)],[c_1174])).

cnf(c_2076,plain,
    ( m1_subset_1(sK6,X0)
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | X0 != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_1886])).

cnf(c_2857,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(X0))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2076])).

cnf(c_5127,plain,
    ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != sK6 ),
    inference(instantiation,[status(thm)],[c_2857])).

cnf(c_5128,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != sK6
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_5127])).

cnf(c_5130,plain,
    ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
    | sK6 != sK6
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_5128])).

cnf(c_39661,plain,
    ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_39493,c_25,c_26,c_27,c_28,c_20,c_29,c_1188,c_1875,c_2077,c_2098,c_2178,c_3736,c_3737,c_5123,c_5130,c_16943,c_20622,c_36999,c_37666])).

cnf(c_4,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | m1_subset_1(sK1(k1_xboole_0,X1,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f55])).

cnf(c_1606,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | m1_subset_1(sK1(k1_xboole_0,X1,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_4])).

cnf(c_2,plain,
    ( r1_partfun1(X0,sK1(k1_xboole_0,X1,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f54])).

cnf(c_1608,plain,
    ( r1_partfun1(X0,sK1(k1_xboole_0,X1,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_2])).

cnf(c_2692,plain,
    ( sP0(X0,X1,k1_xboole_0,X2) != iProver_top
    | r1_partfun1(sK2(X0,X1,k1_xboole_0,X2),sK1(k1_xboole_0,X2,sK2(X0,X1,k1_xboole_0,X2))) = iProver_top
    | v1_funct_1(sK2(X0,X1,k1_xboole_0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_1608])).

cnf(c_4361,plain,
    ( sP0(X0,X1,k1_xboole_0,X2) != iProver_top
    | r1_partfun1(sK2(X0,X1,k1_xboole_0,X2),sK1(k1_xboole_0,X2,sK2(X0,X1,k1_xboole_0,X2))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2692,c_1597])).

cnf(c_8696,plain,
    ( sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)) = sK2(X1,X2,k1_xboole_0,X0)
    | sP0(X1,X2,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_partfun1(sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)),k1_xboole_0) != iProver_top
    | v1_funct_1(sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0))) != iProver_top ),
    inference(superposition,[status(thm)],[c_4361,c_8683])).

cnf(c_8,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ v1_funct_1(X0)
    | v1_funct_1(sK1(k1_xboole_0,X1,X0)) ),
    inference(cnf_transformation,[],[f57])).

cnf(c_1604,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | v1_funct_1(X0) != iProver_top
    | v1_funct_1(sK1(k1_xboole_0,X1,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8])).

cnf(c_2664,plain,
    ( sP0(X0,X1,k1_xboole_0,X2) != iProver_top
    | v1_funct_1(sK2(X0,X1,k1_xboole_0,X2)) != iProver_top
    | v1_funct_1(sK1(k1_xboole_0,X2,sK2(X0,X1,k1_xboole_0,X2))) = iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_1604])).

cnf(c_2752,plain,
    ( sP0(X0,X1,k1_xboole_0,X2) != iProver_top
    | v1_funct_1(sK1(k1_xboole_0,X2,sK2(X0,X1,k1_xboole_0,X2))) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2664,c_1597])).

cnf(c_0,plain,
    ( ~ v1_funct_2(X0,k1_xboole_0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | v1_partfun1(X0,k1_xboole_0)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_6,plain,
    ( v1_funct_2(sK1(k1_xboole_0,X0,X1),k1_xboole_0,X0)
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
    | ~ v1_funct_1(X1) ),
    inference(cnf_transformation,[],[f56])).

cnf(c_270,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
    | v1_partfun1(X0,k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(X2)
    | X3 != X1
    | sK1(k1_xboole_0,X3,X2) != X0
    | k1_xboole_0 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_6])).

cnf(c_271,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | ~ m1_subset_1(sK1(k1_xboole_0,X1,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | v1_partfun1(sK1(k1_xboole_0,X1,X0),k1_xboole_0)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1(k1_xboole_0,X1,X0)) ),
    inference(unflattening,[status(thm)],[c_270])).

cnf(c_275,plain,
    ( ~ v1_funct_1(X0)
    | v1_partfun1(sK1(k1_xboole_0,X1,X0),k1_xboole_0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
    inference(global_propositional_subsumption,[status(thm)],[c_271,c_8,c_4])).

cnf(c_276,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
    | v1_partfun1(sK1(k1_xboole_0,X1,X0),k1_xboole_0)
    | ~ v1_funct_1(X0) ),
    inference(renaming,[status(thm)],[c_275])).

cnf(c_1589,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
    | v1_partfun1(sK1(k1_xboole_0,X1,X0),k1_xboole_0) = iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_276])).

cnf(c_2672,plain,
    ( sP0(X0,X1,k1_xboole_0,X2) != iProver_top
    | v1_partfun1(sK1(k1_xboole_0,X2,sK2(X0,X1,k1_xboole_0,X2)),k1_xboole_0) = iProver_top
    | v1_funct_1(sK2(X0,X1,k1_xboole_0,X2)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1598,c_1589])).

cnf(c_3443,plain,
    ( sP0(X0,X1,k1_xboole_0,X2) != iProver_top
    | v1_partfun1(sK1(k1_xboole_0,X2,sK2(X0,X1,k1_xboole_0,X2)),k1_xboole_0) = iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_2672,c_1597])).

cnf(c_25453,plain,
    ( sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)) = sK2(X1,X2,k1_xboole_0,X0)
    | sP0(X1,X2,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_8696,c_2752,c_3443])).

cnf(c_25457,plain,
    ( sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)) = sK2(X1,X2,k1_xboole_0,X0)
    | sP0(X1,X2,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(sK2(X1,X2,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
    | v1_funct_1(sK2(X1,X2,k1_xboole_0,X0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_1606,c_25453])).

cnf(c_41464,plain,
    ( sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)) = sK2(X1,X2,k1_xboole_0,X0)
    | sP0(X1,X2,k1_xboole_0,X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_25457,c_1597,c_1598])).

cnf(c_41470,plain,
    ( sK1(k1_xboole_0,k1_xboole_0,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) = sK2(sK6,sK5,k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm)],[c_39661,c_41464])).

cnf(c_329,plain,
    ( ~ r1_partfun1(sK5,X0)
    | ~ r1_partfun1(sK6,X0)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
    | ~ v1_funct_1(X1)
    | ~ v1_funct_1(X0)
    | sK1(k1_xboole_0,X2,X1) != X0
    | sK4 != X2
    | sK3 != k1_xboole_0 ),
    inference(resolution_lifted,[status(thm)],[c_6,c_18])).

cnf(c_330,plain,
    ( ~ r1_partfun1(sK5,sK1(k1_xboole_0,sK4,X0))
    | ~ r1_partfun1(sK6,sK1(k1_xboole_0,sK4,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
    | ~ m1_subset_1(sK1(k1_xboole_0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK1(k1_xboole_0,sK4,X0))
    | sK3 != k1_xboole_0 ),
    inference(unflattening,[status(thm)],[c_329])).

cnf(c_348,plain,
    ( ~ r1_partfun1(sK5,sK1(k1_xboole_0,sK4,X0))
    | ~ r1_partfun1(sK6,sK1(k1_xboole_0,sK4,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
    | ~ m1_subset_1(sK1(k1_xboole_0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
    | ~ v1_funct_1(X0)
    | sK3 != k1_xboole_0 ),
    inference(forward_subsumption_resolution,[status(thm)],[c_330,c_8])).

cnf(c_1587,plain,
    ( sK3 != k1_xboole_0
    | r1_partfun1(sK5,sK1(k1_xboole_0,sK4,X0)) != iProver_top
    | r1_partfun1(sK6,sK1(k1_xboole_0,sK4,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top
    | m1_subset_1(sK1(k1_xboole_0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_348])).

cnf(c_38561,plain,
    ( sK3 != k1_xboole_0
    | r1_partfun1(sK5,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
    | r1_partfun1(sK6,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(demodulation,[status(thm)],[c_38361,c_1587])).

cnf(c_38575,plain,
    ( k1_xboole_0 != k1_xboole_0
    | r1_partfun1(sK5,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
    | r1_partfun1(sK6,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_38561,c_38566])).

cnf(c_38576,plain,
    ( r1_partfun1(sK5,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
    | r1_partfun1(sK6,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(equality_resolution_simp,[status(thm)],[c_38575])).

cnf(c_40769,plain,
    ( r1_partfun1(sK5,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
    | r1_partfun1(sK6,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(forward_subsumption_resolution,[status(thm)],[c_38576,c_1606])).

cnf(c_41913,plain,
    ( r1_partfun1(sK5,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) != iProver_top
    | r1_partfun1(sK6,sK1(k1_xboole_0,k1_xboole_0,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0))) != iProver_top
    | m1_subset_1(sK2(sK6,sK5,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(superposition,[status(thm)],[c_41470,c_40769])).

cnf(c_41918,plain,
    ( r1_partfun1(sK5,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) != iProver_top
    | r1_partfun1(sK6,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) != iProver_top
    | m1_subset_1(sK2(sK6,sK5,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
    | v1_funct_1(sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) != iProver_top ),
    inference(light_normalisation,[status(thm)],[c_41913,c_41470])).

cnf(c_6322,plain,
    ( ~ sP0(sK6,sK5,k1_xboole_0,X0)
    | m1_subset_1(sK2(sK6,sK5,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
    inference(instantiation,[status(thm)],[c_14])).

cnf(c_6343,plain,
    ( sP0(sK6,sK5,k1_xboole_0,X0) != iProver_top
    | m1_subset_1(sK2(sK6,sK5,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6322])).

cnf(c_6345,plain,
    ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) != iProver_top
    | m1_subset_1(sK2(sK6,sK5,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6343])).

cnf(c_6324,plain,
    ( ~ sP0(sK6,sK5,k1_xboole_0,X0)
    | r1_partfun1(sK5,sK2(sK6,sK5,k1_xboole_0,X0)) ),
    inference(instantiation,[status(thm)],[c_12])).

cnf(c_6335,plain,
    ( sP0(sK6,sK5,k1_xboole_0,X0) != iProver_top
    | r1_partfun1(sK5,sK2(sK6,sK5,k1_xboole_0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6324])).

cnf(c_6337,plain,
    ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_partfun1(sK5,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6335])).

cnf(c_6325,plain,
    ( ~ sP0(sK6,sK5,k1_xboole_0,X0)
    | r1_partfun1(sK6,sK2(sK6,sK5,k1_xboole_0,X0)) ),
    inference(instantiation,[status(thm)],[c_11])).

cnf(c_6331,plain,
    ( sP0(sK6,sK5,k1_xboole_0,X0) != iProver_top
    | r1_partfun1(sK6,sK2(sK6,sK5,k1_xboole_0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6325])).

cnf(c_6333,plain,
    ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) != iProver_top
    | r1_partfun1(sK6,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6331])).

cnf(c_6326,plain,
    ( ~ sP0(sK6,sK5,k1_xboole_0,X0)
    | v1_funct_1(sK2(sK6,sK5,k1_xboole_0,X0)) ),
    inference(instantiation,[status(thm)],[c_15])).

cnf(c_6327,plain,
    ( sP0(sK6,sK5,k1_xboole_0,X0) != iProver_top
    | v1_funct_1(sK2(sK6,sK5,k1_xboole_0,X0)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_6326])).

cnf(c_6329,plain,
    ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) != iProver_top
    | v1_funct_1(sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) = iProver_top ),
    inference(instantiation,[status(thm)],[c_6327])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_41918,c_38361,c_6345,c_6337,c_6333,c_6329,c_5130,c_5123,c_3737,c_3736,c_2178,c_2098,c_2077,c_1875,c_1188,c_29,c_20,c_28,c_27,c_26,c_25])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : iproveropt_run.sh %d %s
% 0.12/0.33  % Computer   : n009.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 15:06:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  % Running in FOF mode
% 11.48/1.98  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 11.48/1.98  
% 11.48/1.98  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 11.48/1.98  
% 11.48/1.98  ------  iProver source info
% 11.48/1.98  
% 11.48/1.98  git: date: 2020-06-30 10:37:57 +0100
% 11.48/1.98  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 11.48/1.98  git: non_committed_changes: false
% 11.48/1.98  git: last_make_outside_of_git: false
% 11.48/1.98  
% 11.48/1.98  ------ 
% 11.48/1.98  
% 11.48/1.98  ------ Input Options
% 11.48/1.98  
% 11.48/1.98  --out_options                           all
% 11.48/1.98  --tptp_safe_out                         true
% 11.48/1.98  --problem_path                          ""
% 11.48/1.98  --include_path                          ""
% 11.48/1.98  --clausifier                            res/vclausify_rel
% 11.48/1.98  --clausifier_options                    --mode clausify
% 11.48/1.98  --stdin                                 false
% 11.48/1.98  --stats_out                             all
% 11.48/1.98  
% 11.48/1.98  ------ General Options
% 11.48/1.98  
% 11.48/1.98  --fof                                   false
% 11.48/1.98  --time_out_real                         305.
% 11.48/1.98  --time_out_virtual                      -1.
% 11.48/1.98  --symbol_type_check                     false
% 11.48/1.98  --clausify_out                          false
% 11.48/1.98  --sig_cnt_out                           false
% 11.48/1.98  --trig_cnt_out                          false
% 11.48/1.98  --trig_cnt_out_tolerance                1.
% 11.48/1.98  --trig_cnt_out_sk_spl                   false
% 11.48/1.98  --abstr_cl_out                          false
% 11.48/1.98  
% 11.48/1.98  ------ Global Options
% 11.48/1.98  
% 11.48/1.98  --schedule                              default
% 11.48/1.98  --add_important_lit                     false
% 11.48/1.98  --prop_solver_per_cl                    1000
% 11.48/1.98  --min_unsat_core                        false
% 11.48/1.98  --soft_assumptions                      false
% 11.48/1.98  --soft_lemma_size                       3
% 11.48/1.98  --prop_impl_unit_size                   0
% 11.48/1.98  --prop_impl_unit                        []
% 11.48/1.98  --share_sel_clauses                     true
% 11.48/1.98  --reset_solvers                         false
% 11.48/1.98  --bc_imp_inh                            [conj_cone]
% 11.48/1.98  --conj_cone_tolerance                   3.
% 11.48/1.98  --extra_neg_conj                        none
% 11.48/1.98  --large_theory_mode                     true
% 11.48/1.98  --prolific_symb_bound                   200
% 11.48/1.98  --lt_threshold                          2000
% 11.48/1.98  --clause_weak_htbl                      true
% 11.48/1.98  --gc_record_bc_elim                     false
% 11.48/1.98  
% 11.48/1.98  ------ Preprocessing Options
% 11.48/1.98  
% 11.48/1.98  --preprocessing_flag                    true
% 11.48/1.98  --time_out_prep_mult                    0.1
% 11.48/1.98  --splitting_mode                        input
% 11.48/1.98  --splitting_grd                         true
% 11.48/1.98  --splitting_cvd                         false
% 11.48/1.98  --splitting_cvd_svl                     false
% 11.48/1.98  --splitting_nvd                         32
% 11.48/1.98  --sub_typing                            true
% 11.48/1.98  --prep_gs_sim                           true
% 11.48/1.98  --prep_unflatten                        true
% 11.48/1.98  --prep_res_sim                          true
% 11.48/1.98  --prep_upred                            true
% 11.48/1.98  --prep_sem_filter                       exhaustive
% 11.48/1.98  --prep_sem_filter_out                   false
% 11.48/1.98  --pred_elim                             true
% 11.48/1.98  --res_sim_input                         true
% 11.48/1.98  --eq_ax_congr_red                       true
% 11.48/1.98  --pure_diseq_elim                       true
% 11.48/1.98  --brand_transform                       false
% 11.48/1.98  --non_eq_to_eq                          false
% 11.48/1.98  --prep_def_merge                        true
% 11.48/1.98  --prep_def_merge_prop_impl              false
% 11.48/1.98  --prep_def_merge_mbd                    true
% 11.48/1.98  --prep_def_merge_tr_red                 false
% 11.48/1.98  --prep_def_merge_tr_cl                  false
% 11.48/1.98  --smt_preprocessing                     true
% 11.48/1.98  --smt_ac_axioms                         fast
% 11.48/1.98  --preprocessed_out                      false
% 11.48/1.98  --preprocessed_stats                    false
% 11.48/1.98  
% 11.48/1.98  ------ Abstraction refinement Options
% 11.48/1.98  
% 11.48/1.98  --abstr_ref                             []
% 11.48/1.98  --abstr_ref_prep                        false
% 11.48/1.98  --abstr_ref_until_sat                   false
% 11.48/1.98  --abstr_ref_sig_restrict                funpre
% 11.48/1.98  --abstr_ref_af_restrict_to_split_sk     false
% 11.48/1.98  --abstr_ref_under                       []
% 11.48/1.98  
% 11.48/1.98  ------ SAT Options
% 11.48/1.98  
% 11.48/1.98  --sat_mode                              false
% 11.48/1.98  --sat_fm_restart_options                ""
% 11.48/1.98  --sat_gr_def                            false
% 11.48/1.98  --sat_epr_types                         true
% 11.48/1.98  --sat_non_cyclic_types                  false
% 11.48/1.98  --sat_finite_models                     false
% 11.48/1.98  --sat_fm_lemmas                         false
% 11.48/1.98  --sat_fm_prep                           false
% 11.48/1.98  --sat_fm_uc_incr                        true
% 11.48/1.98  --sat_out_model                         small
% 11.48/1.98  --sat_out_clauses                       false
% 11.48/1.98  
% 11.48/1.98  ------ QBF Options
% 11.48/1.98  
% 11.48/1.98  --qbf_mode                              false
% 11.48/1.98  --qbf_elim_univ                         false
% 11.48/1.98  --qbf_dom_inst                          none
% 11.48/1.98  --qbf_dom_pre_inst                      false
% 11.48/1.98  --qbf_sk_in                             false
% 11.48/1.98  --qbf_pred_elim                         true
% 11.48/1.98  --qbf_split                             512
% 11.48/1.98  
% 11.48/1.98  ------ BMC1 Options
% 11.48/1.98  
% 11.48/1.98  --bmc1_incremental                      false
% 11.48/1.98  --bmc1_axioms                           reachable_all
% 11.48/1.98  --bmc1_min_bound                        0
% 11.48/1.98  --bmc1_max_bound                        -1
% 11.48/1.98  --bmc1_max_bound_default                -1
% 11.48/1.98  --bmc1_symbol_reachability              true
% 11.48/1.98  --bmc1_property_lemmas                  false
% 11.48/1.98  --bmc1_k_induction                      false
% 11.48/1.98  --bmc1_non_equiv_states                 false
% 11.48/1.98  --bmc1_deadlock                         false
% 11.48/1.98  --bmc1_ucm                              false
% 11.48/1.98  --bmc1_add_unsat_core                   none
% 11.48/1.98  --bmc1_unsat_core_children              false
% 11.48/1.98  --bmc1_unsat_core_extrapolate_axioms    false
% 11.48/1.98  --bmc1_out_stat                         full
% 11.48/1.98  --bmc1_ground_init                      false
% 11.48/1.98  --bmc1_pre_inst_next_state              false
% 11.48/1.98  --bmc1_pre_inst_state                   false
% 11.48/1.98  --bmc1_pre_inst_reach_state             false
% 11.48/1.98  --bmc1_out_unsat_core                   false
% 11.48/1.98  --bmc1_aig_witness_out                  false
% 11.48/1.98  --bmc1_verbose                          false
% 11.48/1.98  --bmc1_dump_clauses_tptp                false
% 11.48/1.98  --bmc1_dump_unsat_core_tptp             false
% 11.48/1.98  --bmc1_dump_file                        -
% 11.48/1.98  --bmc1_ucm_expand_uc_limit              128
% 11.48/1.98  --bmc1_ucm_n_expand_iterations          6
% 11.48/1.98  --bmc1_ucm_extend_mode                  1
% 11.48/1.98  --bmc1_ucm_init_mode                    2
% 11.48/1.98  --bmc1_ucm_cone_mode                    none
% 11.48/1.98  --bmc1_ucm_reduced_relation_type        0
% 11.48/1.98  --bmc1_ucm_relax_model                  4
% 11.48/1.98  --bmc1_ucm_full_tr_after_sat            true
% 11.48/1.98  --bmc1_ucm_expand_neg_assumptions       false
% 11.48/1.98  --bmc1_ucm_layered_model                none
% 11.48/1.98  --bmc1_ucm_max_lemma_size               10
% 11.48/1.98  
% 11.48/1.98  ------ AIG Options
% 11.48/1.98  
% 11.48/1.98  --aig_mode                              false
% 11.48/1.98  
% 11.48/1.98  ------ Instantiation Options
% 11.48/1.98  
% 11.48/1.98  --instantiation_flag                    true
% 11.48/1.98  --inst_sos_flag                         false
% 11.48/1.98  --inst_sos_phase                        true
% 11.48/1.98  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.48/1.98  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.48/1.98  --inst_lit_sel_side                     num_symb
% 11.48/1.98  --inst_solver_per_active                1400
% 11.48/1.98  --inst_solver_calls_frac                1.
% 11.48/1.98  --inst_passive_queue_type               priority_queues
% 11.48/1.98  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.48/1.98  --inst_passive_queues_freq              [25;2]
% 11.48/1.98  --inst_dismatching                      true
% 11.48/1.98  --inst_eager_unprocessed_to_passive     true
% 11.48/1.98  --inst_prop_sim_given                   true
% 11.48/1.98  --inst_prop_sim_new                     false
% 11.48/1.98  --inst_subs_new                         false
% 11.48/1.98  --inst_eq_res_simp                      false
% 11.48/1.98  --inst_subs_given                       false
% 11.48/1.98  --inst_orphan_elimination               true
% 11.48/1.98  --inst_learning_loop_flag               true
% 11.48/1.98  --inst_learning_start                   3000
% 11.48/1.98  --inst_learning_factor                  2
% 11.48/1.98  --inst_start_prop_sim_after_learn       3
% 11.48/1.98  --inst_sel_renew                        solver
% 11.48/1.98  --inst_lit_activity_flag                true
% 11.48/1.98  --inst_restr_to_given                   false
% 11.48/1.98  --inst_activity_threshold               500
% 11.48/1.98  --inst_out_proof                        true
% 11.48/1.98  
% 11.48/1.98  ------ Resolution Options
% 11.48/1.98  
% 11.48/1.98  --resolution_flag                       true
% 11.48/1.98  --res_lit_sel                           adaptive
% 11.48/1.98  --res_lit_sel_side                      none
% 11.48/1.98  --res_ordering                          kbo
% 11.48/1.98  --res_to_prop_solver                    active
% 11.48/1.98  --res_prop_simpl_new                    false
% 11.48/1.98  --res_prop_simpl_given                  true
% 11.48/1.98  --res_passive_queue_type                priority_queues
% 11.48/1.98  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.48/1.98  --res_passive_queues_freq               [15;5]
% 11.48/1.98  --res_forward_subs                      full
% 11.48/1.98  --res_backward_subs                     full
% 11.48/1.98  --res_forward_subs_resolution           true
% 11.48/1.98  --res_backward_subs_resolution          true
% 11.48/1.98  --res_orphan_elimination                true
% 11.48/1.98  --res_time_limit                        2.
% 11.48/1.98  --res_out_proof                         true
% 11.48/1.98  
% 11.48/1.98  ------ Superposition Options
% 11.48/1.98  
% 11.48/1.98  --superposition_flag                    true
% 11.48/1.98  --sup_passive_queue_type                priority_queues
% 11.48/1.98  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.48/1.98  --sup_passive_queues_freq               [8;1;4]
% 11.48/1.98  --demod_completeness_check              fast
% 11.48/1.98  --demod_use_ground                      true
% 11.48/1.98  --sup_to_prop_solver                    passive
% 11.48/1.98  --sup_prop_simpl_new                    true
% 11.48/1.98  --sup_prop_simpl_given                  true
% 11.48/1.98  --sup_fun_splitting                     false
% 11.48/1.98  --sup_smt_interval                      50000
% 11.48/1.98  
% 11.48/1.98  ------ Superposition Simplification Setup
% 11.48/1.98  
% 11.48/1.98  --sup_indices_passive                   []
% 11.48/1.98  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.98  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.98  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.98  --sup_full_triv                         [TrivRules;PropSubs]
% 11.48/1.98  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.48/1.98  --sup_full_bw                           [BwDemod]
% 11.48/1.98  --sup_immed_triv                        [TrivRules]
% 11.48/1.98  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.48/1.98  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.48/1.98  --sup_immed_bw_main                     []
% 11.48/1.98  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.48/1.98  --sup_input_triv                        [Unflattening;TrivRules]
% 11.48/1.98  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.48/1.98  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.48/1.98  
% 11.48/1.98  ------ Combination Options
% 11.48/1.98  
% 11.48/1.98  --comb_res_mult                         3
% 11.48/1.98  --comb_sup_mult                         2
% 11.48/1.98  --comb_inst_mult                        10
% 11.48/1.98  
% 11.48/1.98  ------ Debug Options
% 11.48/1.98  
% 11.48/1.98  --dbg_backtrace                         false
% 11.48/1.98  --dbg_dump_prop_clauses                 false
% 11.48/1.98  --dbg_dump_prop_clauses_file            -
% 11.48/1.98  --dbg_out_stat                          false
% 11.48/1.98  ------ Parsing...
% 11.48/1.98  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 11.48/1.98  
% 11.48/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 11.48/1.98  
% 11.48/1.98  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 11.48/1.98  
% 11.48/1.98  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 11.48/1.98  ------ Proving...
% 11.48/1.98  ------ Problem Properties 
% 11.48/1.98  
% 11.48/1.98  
% 11.48/1.98  clauses                                 24
% 11.48/1.98  conjectures                             6
% 11.48/1.98  EPR                                     4
% 11.48/1.98  Horn                                    19
% 11.48/1.98  unary                                   5
% 11.48/1.98  binary                                  6
% 11.48/1.98  lits                                    77
% 11.48/1.98  lits eq                                 10
% 11.48/1.98  fd_pure                                 0
% 11.48/1.98  fd_pseudo                               0
% 11.48/1.98  fd_cond                                 5
% 11.48/1.98  fd_pseudo_cond                          1
% 11.48/1.98  AC symbols                              0
% 11.48/1.98  
% 11.48/1.98  ------ Schedule dynamic 5 is on 
% 11.48/1.98  
% 11.48/1.98  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 11.48/1.98  
% 11.48/1.98  
% 11.48/1.98  ------ 
% 11.48/1.98  Current options:
% 11.48/1.98  ------ 
% 11.48/1.98  
% 11.48/1.98  ------ Input Options
% 11.48/1.98  
% 11.48/1.98  --out_options                           all
% 11.48/1.98  --tptp_safe_out                         true
% 11.48/1.98  --problem_path                          ""
% 11.48/1.98  --include_path                          ""
% 11.48/1.98  --clausifier                            res/vclausify_rel
% 11.48/1.98  --clausifier_options                    --mode clausify
% 11.48/1.98  --stdin                                 false
% 11.48/1.98  --stats_out                             all
% 11.48/1.98  
% 11.48/1.98  ------ General Options
% 11.48/1.98  
% 11.48/1.98  --fof                                   false
% 11.48/1.98  --time_out_real                         305.
% 11.48/1.98  --time_out_virtual                      -1.
% 11.48/1.98  --symbol_type_check                     false
% 11.48/1.98  --clausify_out                          false
% 11.48/1.98  --sig_cnt_out                           false
% 11.48/1.98  --trig_cnt_out                          false
% 11.48/1.98  --trig_cnt_out_tolerance                1.
% 11.48/1.98  --trig_cnt_out_sk_spl                   false
% 11.48/1.98  --abstr_cl_out                          false
% 11.48/1.98  
% 11.48/1.98  ------ Global Options
% 11.48/1.98  
% 11.48/1.98  --schedule                              default
% 11.48/1.98  --add_important_lit                     false
% 11.48/1.98  --prop_solver_per_cl                    1000
% 11.48/1.98  --min_unsat_core                        false
% 11.48/1.98  --soft_assumptions                      false
% 11.48/1.98  --soft_lemma_size                       3
% 11.48/1.98  --prop_impl_unit_size                   0
% 11.48/1.98  --prop_impl_unit                        []
% 11.48/1.98  --share_sel_clauses                     true
% 11.48/1.98  --reset_solvers                         false
% 11.48/1.98  --bc_imp_inh                            [conj_cone]
% 11.48/1.98  --conj_cone_tolerance                   3.
% 11.48/1.99  --extra_neg_conj                        none
% 11.48/1.99  --large_theory_mode                     true
% 11.48/1.99  --prolific_symb_bound                   200
% 11.48/1.99  --lt_threshold                          2000
% 11.48/1.99  --clause_weak_htbl                      true
% 11.48/1.99  --gc_record_bc_elim                     false
% 11.48/1.99  
% 11.48/1.99  ------ Preprocessing Options
% 11.48/1.99  
% 11.48/1.99  --preprocessing_flag                    true
% 11.48/1.99  --time_out_prep_mult                    0.1
% 11.48/1.99  --splitting_mode                        input
% 11.48/1.99  --splitting_grd                         true
% 11.48/1.99  --splitting_cvd                         false
% 11.48/1.99  --splitting_cvd_svl                     false
% 11.48/1.99  --splitting_nvd                         32
% 11.48/1.99  --sub_typing                            true
% 11.48/1.99  --prep_gs_sim                           true
% 11.48/1.99  --prep_unflatten                        true
% 11.48/1.99  --prep_res_sim                          true
% 11.48/1.99  --prep_upred                            true
% 11.48/1.99  --prep_sem_filter                       exhaustive
% 11.48/1.99  --prep_sem_filter_out                   false
% 11.48/1.99  --pred_elim                             true
% 11.48/1.99  --res_sim_input                         true
% 11.48/1.99  --eq_ax_congr_red                       true
% 11.48/1.99  --pure_diseq_elim                       true
% 11.48/1.99  --brand_transform                       false
% 11.48/1.99  --non_eq_to_eq                          false
% 11.48/1.99  --prep_def_merge                        true
% 11.48/1.99  --prep_def_merge_prop_impl              false
% 11.48/1.99  --prep_def_merge_mbd                    true
% 11.48/1.99  --prep_def_merge_tr_red                 false
% 11.48/1.99  --prep_def_merge_tr_cl                  false
% 11.48/1.99  --smt_preprocessing                     true
% 11.48/1.99  --smt_ac_axioms                         fast
% 11.48/1.99  --preprocessed_out                      false
% 11.48/1.99  --preprocessed_stats                    false
% 11.48/1.99  
% 11.48/1.99  ------ Abstraction refinement Options
% 11.48/1.99  
% 11.48/1.99  --abstr_ref                             []
% 11.48/1.99  --abstr_ref_prep                        false
% 11.48/1.99  --abstr_ref_until_sat                   false
% 11.48/1.99  --abstr_ref_sig_restrict                funpre
% 11.48/1.99  --abstr_ref_af_restrict_to_split_sk     false
% 11.48/1.99  --abstr_ref_under                       []
% 11.48/1.99  
% 11.48/1.99  ------ SAT Options
% 11.48/1.99  
% 11.48/1.99  --sat_mode                              false
% 11.48/1.99  --sat_fm_restart_options                ""
% 11.48/1.99  --sat_gr_def                            false
% 11.48/1.99  --sat_epr_types                         true
% 11.48/1.99  --sat_non_cyclic_types                  false
% 11.48/1.99  --sat_finite_models                     false
% 11.48/1.99  --sat_fm_lemmas                         false
% 11.48/1.99  --sat_fm_prep                           false
% 11.48/1.99  --sat_fm_uc_incr                        true
% 11.48/1.99  --sat_out_model                         small
% 11.48/1.99  --sat_out_clauses                       false
% 11.48/1.99  
% 11.48/1.99  ------ QBF Options
% 11.48/1.99  
% 11.48/1.99  --qbf_mode                              false
% 11.48/1.99  --qbf_elim_univ                         false
% 11.48/1.99  --qbf_dom_inst                          none
% 11.48/1.99  --qbf_dom_pre_inst                      false
% 11.48/1.99  --qbf_sk_in                             false
% 11.48/1.99  --qbf_pred_elim                         true
% 11.48/1.99  --qbf_split                             512
% 11.48/1.99  
% 11.48/1.99  ------ BMC1 Options
% 11.48/1.99  
% 11.48/1.99  --bmc1_incremental                      false
% 11.48/1.99  --bmc1_axioms                           reachable_all
% 11.48/1.99  --bmc1_min_bound                        0
% 11.48/1.99  --bmc1_max_bound                        -1
% 11.48/1.99  --bmc1_max_bound_default                -1
% 11.48/1.99  --bmc1_symbol_reachability              true
% 11.48/1.99  --bmc1_property_lemmas                  false
% 11.48/1.99  --bmc1_k_induction                      false
% 11.48/1.99  --bmc1_non_equiv_states                 false
% 11.48/1.99  --bmc1_deadlock                         false
% 11.48/1.99  --bmc1_ucm                              false
% 11.48/1.99  --bmc1_add_unsat_core                   none
% 11.48/1.99  --bmc1_unsat_core_children              false
% 11.48/1.99  --bmc1_unsat_core_extrapolate_axioms    false
% 11.48/1.99  --bmc1_out_stat                         full
% 11.48/1.99  --bmc1_ground_init                      false
% 11.48/1.99  --bmc1_pre_inst_next_state              false
% 11.48/1.99  --bmc1_pre_inst_state                   false
% 11.48/1.99  --bmc1_pre_inst_reach_state             false
% 11.48/1.99  --bmc1_out_unsat_core                   false
% 11.48/1.99  --bmc1_aig_witness_out                  false
% 11.48/1.99  --bmc1_verbose                          false
% 11.48/1.99  --bmc1_dump_clauses_tptp                false
% 11.48/1.99  --bmc1_dump_unsat_core_tptp             false
% 11.48/1.99  --bmc1_dump_file                        -
% 11.48/1.99  --bmc1_ucm_expand_uc_limit              128
% 11.48/1.99  --bmc1_ucm_n_expand_iterations          6
% 11.48/1.99  --bmc1_ucm_extend_mode                  1
% 11.48/1.99  --bmc1_ucm_init_mode                    2
% 11.48/1.99  --bmc1_ucm_cone_mode                    none
% 11.48/1.99  --bmc1_ucm_reduced_relation_type        0
% 11.48/1.99  --bmc1_ucm_relax_model                  4
% 11.48/1.99  --bmc1_ucm_full_tr_after_sat            true
% 11.48/1.99  --bmc1_ucm_expand_neg_assumptions       false
% 11.48/1.99  --bmc1_ucm_layered_model                none
% 11.48/1.99  --bmc1_ucm_max_lemma_size               10
% 11.48/1.99  
% 11.48/1.99  ------ AIG Options
% 11.48/1.99  
% 11.48/1.99  --aig_mode                              false
% 11.48/1.99  
% 11.48/1.99  ------ Instantiation Options
% 11.48/1.99  
% 11.48/1.99  --instantiation_flag                    true
% 11.48/1.99  --inst_sos_flag                         false
% 11.48/1.99  --inst_sos_phase                        true
% 11.48/1.99  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 11.48/1.99  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 11.48/1.99  --inst_lit_sel_side                     none
% 11.48/1.99  --inst_solver_per_active                1400
% 11.48/1.99  --inst_solver_calls_frac                1.
% 11.48/1.99  --inst_passive_queue_type               priority_queues
% 11.48/1.99  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 11.48/1.99  --inst_passive_queues_freq              [25;2]
% 11.48/1.99  --inst_dismatching                      true
% 11.48/1.99  --inst_eager_unprocessed_to_passive     true
% 11.48/1.99  --inst_prop_sim_given                   true
% 11.48/1.99  --inst_prop_sim_new                     false
% 11.48/1.99  --inst_subs_new                         false
% 11.48/1.99  --inst_eq_res_simp                      false
% 11.48/1.99  --inst_subs_given                       false
% 11.48/1.99  --inst_orphan_elimination               true
% 11.48/1.99  --inst_learning_loop_flag               true
% 11.48/1.99  --inst_learning_start                   3000
% 11.48/1.99  --inst_learning_factor                  2
% 11.48/1.99  --inst_start_prop_sim_after_learn       3
% 11.48/1.99  --inst_sel_renew                        solver
% 11.48/1.99  --inst_lit_activity_flag                true
% 11.48/1.99  --inst_restr_to_given                   false
% 11.48/1.99  --inst_activity_threshold               500
% 11.48/1.99  --inst_out_proof                        true
% 11.48/1.99  
% 11.48/1.99  ------ Resolution Options
% 11.48/1.99  
% 11.48/1.99  --resolution_flag                       false
% 11.48/1.99  --res_lit_sel                           adaptive
% 11.48/1.99  --res_lit_sel_side                      none
% 11.48/1.99  --res_ordering                          kbo
% 11.48/1.99  --res_to_prop_solver                    active
% 11.48/1.99  --res_prop_simpl_new                    false
% 11.48/1.99  --res_prop_simpl_given                  true
% 11.48/1.99  --res_passive_queue_type                priority_queues
% 11.48/1.99  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 11.48/1.99  --res_passive_queues_freq               [15;5]
% 11.48/1.99  --res_forward_subs                      full
% 11.48/1.99  --res_backward_subs                     full
% 11.48/1.99  --res_forward_subs_resolution           true
% 11.48/1.99  --res_backward_subs_resolution          true
% 11.48/1.99  --res_orphan_elimination                true
% 11.48/1.99  --res_time_limit                        2.
% 11.48/1.99  --res_out_proof                         true
% 11.48/1.99  
% 11.48/1.99  ------ Superposition Options
% 11.48/1.99  
% 11.48/1.99  --superposition_flag                    true
% 11.48/1.99  --sup_passive_queue_type                priority_queues
% 11.48/1.99  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 11.48/1.99  --sup_passive_queues_freq               [8;1;4]
% 11.48/1.99  --demod_completeness_check              fast
% 11.48/1.99  --demod_use_ground                      true
% 11.48/1.99  --sup_to_prop_solver                    passive
% 11.48/1.99  --sup_prop_simpl_new                    true
% 11.48/1.99  --sup_prop_simpl_given                  true
% 11.48/1.99  --sup_fun_splitting                     false
% 11.48/1.99  --sup_smt_interval                      50000
% 11.48/1.99  
% 11.48/1.99  ------ Superposition Simplification Setup
% 11.48/1.99  
% 11.48/1.99  --sup_indices_passive                   []
% 11.48/1.99  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.99  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.99  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 11.48/1.99  --sup_full_triv                         [TrivRules;PropSubs]
% 11.48/1.99  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.48/1.99  --sup_full_bw                           [BwDemod]
% 11.48/1.99  --sup_immed_triv                        [TrivRules]
% 11.48/1.99  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 11.48/1.99  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.48/1.99  --sup_immed_bw_main                     []
% 11.48/1.99  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.48/1.99  --sup_input_triv                        [Unflattening;TrivRules]
% 11.48/1.99  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 11.48/1.99  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 11.48/1.99  
% 11.48/1.99  ------ Combination Options
% 11.48/1.99  
% 11.48/1.99  --comb_res_mult                         3
% 11.48/1.99  --comb_sup_mult                         2
% 11.48/1.99  --comb_inst_mult                        10
% 11.48/1.99  
% 11.48/1.99  ------ Debug Options
% 11.48/1.99  
% 11.48/1.99  --dbg_backtrace                         false
% 11.48/1.99  --dbg_dump_prop_clauses                 false
% 11.48/1.99  --dbg_dump_prop_clauses_file            -
% 11.48/1.99  --dbg_out_stat                          false
% 11.48/1.99  
% 11.48/1.99  
% 11.48/1.99  
% 11.48/1.99  
% 11.48/1.99  ------ Proving...
% 11.48/1.99  
% 11.48/1.99  
% 11.48/1.99  % SZS status Theorem for theBenchmark.p
% 11.48/1.99  
% 11.48/1.99  % SZS output start CNFRefutation for theBenchmark.p
% 11.48/1.99  
% 11.48/1.99  fof(f5,conjecture,(
% 11.48/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ~(r1_partfun1(X3,X4) & r1_partfun1(X2,X4))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X1 => k1_xboole_0 = X0))))),
% 11.48/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.99  
% 11.48/1.99  fof(f6,negated_conjecture,(
% 11.48/1.99    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X4,X0,X1) & v1_funct_1(X4)) => ~(r1_partfun1(X3,X4) & r1_partfun1(X2,X4))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X1 => k1_xboole_0 = X0))))),
% 11.48/1.99    inference(negated_conjecture,[],[f5])).
% 11.48/1.99  
% 11.48/1.99  fof(f15,plain,(
% 11.48/1.99    ? [X0,X1,X2] : (? [X3] : ((! [X4] : ((~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4)) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 11.48/1.99    inference(ennf_transformation,[],[f6])).
% 11.48/1.99  
% 11.48/1.99  fof(f16,plain,(
% 11.48/1.99    ? [X0,X1,X2] : (? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4)) & r1_partfun1(X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 11.48/1.99    inference(flattening,[],[f15])).
% 11.48/1.99  
% 11.48/1.99  fof(f26,plain,(
% 11.48/1.99    ( ! [X2,X0,X1] : (? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4)) & r1_partfun1(X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => (! [X4] : (~r1_partfun1(sK6,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4)) & r1_partfun1(X2,sK6) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(sK6))) )),
% 11.48/1.99    introduced(choice_axiom,[])).
% 11.48/1.99  
% 11.48/1.99  fof(f25,plain,(
% 11.48/1.99    ? [X0,X1,X2] : (? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(X2,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X4,X0,X1) | ~v1_funct_1(X4)) & r1_partfun1(X2,X3) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (! [X4] : (~r1_partfun1(X3,X4) | ~r1_partfun1(sK5,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(X4,sK3,sK4) | ~v1_funct_1(X4)) & r1_partfun1(sK5,X3) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(X3)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5))),
% 11.48/1.99    introduced(choice_axiom,[])).
% 11.48/1.99  
% 11.48/1.99  fof(f27,plain,(
% 11.48/1.99    (! [X4] : (~r1_partfun1(sK6,X4) | ~r1_partfun1(sK5,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(X4,sK3,sK4) | ~v1_funct_1(X4)) & r1_partfun1(sK5,sK6) & (k1_xboole_0 = sK3 | k1_xboole_0 != sK4) & m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK6)) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) & v1_funct_1(sK5)),
% 11.48/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK3,sK4,sK5,sK6])],[f16,f26,f25])).
% 11.48/1.99  
% 11.48/1.99  fof(f49,plain,(
% 11.48/1.99    m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 11.48/1.99    inference(cnf_transformation,[],[f27])).
% 11.48/1.99  
% 11.48/1.99  fof(f47,plain,(
% 11.48/1.99    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))),
% 11.48/1.99    inference(cnf_transformation,[],[f27])).
% 11.48/1.99  
% 11.48/1.99  fof(f4,axiom,(
% 11.48/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ~(! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => ~(r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0))) & r1_partfun1(X2,X3) & (k1_xboole_0 = X1 => k1_xboole_0 = X0))))),
% 11.48/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.99  
% 11.48/1.99  fof(f13,plain,(
% 11.48/1.99    ! [X0,X1,X2] : (! [X3] : ((? [X4] : ((r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0)) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4))) | ~r1_partfun1(X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.48/1.99    inference(ennf_transformation,[],[f4])).
% 11.48/1.99  
% 11.48/1.99  fof(f14,plain,(
% 11.48/1.99    ! [X0,X1,X2] : (! [X3] : (? [X4] : (r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) | ~r1_partfun1(X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.48/1.99    inference(flattening,[],[f13])).
% 11.48/1.99  
% 11.48/1.99  fof(f17,plain,(
% 11.48/1.99    ! [X3,X2,X0,X1] : (? [X4] : (r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) | ~sP0(X3,X2,X0,X1))),
% 11.48/1.99    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 11.48/1.99  
% 11.48/1.99  fof(f18,plain,(
% 11.48/1.99    ! [X0,X1,X2] : (! [X3] : (sP0(X3,X2,X0,X1) | ~r1_partfun1(X2,X3) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.48/1.99    inference(definition_folding,[],[f14,f17])).
% 11.48/1.99  
% 11.48/1.99  fof(f44,plain,(
% 11.48/1.99    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X0,X1) | ~r1_partfun1(X2,X3) | k1_xboole_0 = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f18])).
% 11.48/1.99  
% 11.48/1.99  fof(f46,plain,(
% 11.48/1.99    v1_funct_1(sK5)),
% 11.48/1.99    inference(cnf_transformation,[],[f27])).
% 11.48/1.99  
% 11.48/1.99  fof(f48,plain,(
% 11.48/1.99    v1_funct_1(sK6)),
% 11.48/1.99    inference(cnf_transformation,[],[f27])).
% 11.48/1.99  
% 11.48/1.99  fof(f51,plain,(
% 11.48/1.99    r1_partfun1(sK5,sK6)),
% 11.48/1.99    inference(cnf_transformation,[],[f27])).
% 11.48/1.99  
% 11.48/1.99  fof(f21,plain,(
% 11.48/1.99    ! [X3,X2,X0,X1] : (? [X4] : (r1_partfun1(X3,X4) & r1_partfun1(X2,X4) & v1_partfun1(X4,X0) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) | ~sP0(X3,X2,X0,X1))),
% 11.48/1.99    inference(nnf_transformation,[],[f17])).
% 11.48/1.99  
% 11.48/1.99  fof(f22,plain,(
% 11.48/1.99    ! [X0,X1,X2,X3] : (? [X4] : (r1_partfun1(X0,X4) & r1_partfun1(X1,X4) & v1_partfun1(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X4)) | ~sP0(X0,X1,X2,X3))),
% 11.48/1.99    inference(rectify,[],[f21])).
% 11.48/1.99  
% 11.48/1.99  fof(f23,plain,(
% 11.48/1.99    ! [X3,X2,X1,X0] : (? [X4] : (r1_partfun1(X0,X4) & r1_partfun1(X1,X4) & v1_partfun1(X4,X2) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X4)) => (r1_partfun1(X0,sK2(X0,X1,X2,X3)) & r1_partfun1(X1,sK2(X0,X1,X2,X3)) & v1_partfun1(sK2(X0,X1,X2,X3),X2) & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(sK2(X0,X1,X2,X3))))),
% 11.48/1.99    introduced(choice_axiom,[])).
% 11.48/1.99  
% 11.48/1.99  fof(f24,plain,(
% 11.48/1.99    ! [X0,X1,X2,X3] : ((r1_partfun1(X0,sK2(X0,X1,X2,X3)) & r1_partfun1(X1,sK2(X0,X1,X2,X3)) & v1_partfun1(sK2(X0,X1,X2,X3),X2) & m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(sK2(X0,X1,X2,X3))) | ~sP0(X0,X1,X2,X3))),
% 11.48/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f22,f23])).
% 11.48/1.99  
% 11.48/1.99  fof(f43,plain,(
% 11.48/1.99    ( ! [X2,X0,X3,X1] : (r1_partfun1(X0,sK2(X0,X1,X2,X3)) | ~sP0(X0,X1,X2,X3)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f24])).
% 11.48/1.99  
% 11.48/1.99  fof(f40,plain,(
% 11.48/1.99    ( ! [X2,X0,X3,X1] : (m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~sP0(X0,X1,X2,X3)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f24])).
% 11.48/1.99  
% 11.48/1.99  fof(f39,plain,(
% 11.48/1.99    ( ! [X2,X0,X3,X1] : (v1_funct_1(sK2(X0,X1,X2,X3)) | ~sP0(X0,X1,X2,X3)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f24])).
% 11.48/1.99  
% 11.48/1.99  fof(f3,axiom,(
% 11.48/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X3)) => ((r1_partfun1(X2,X3) & v1_partfun1(X3,X0) & v1_partfun1(X2,X0)) => X2 = X3)))),
% 11.48/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.99  
% 11.48/1.99  fof(f11,plain,(
% 11.48/1.99    ! [X0,X1,X2] : (! [X3] : ((X2 = X3 | (~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.48/1.99    inference(ennf_transformation,[],[f3])).
% 11.48/1.99  
% 11.48/1.99  fof(f12,plain,(
% 11.48/1.99    ! [X0,X1,X2] : (! [X3] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.48/1.99    inference(flattening,[],[f11])).
% 11.48/1.99  
% 11.48/1.99  fof(f38,plain,(
% 11.48/1.99    ( ! [X2,X0,X3,X1] : (X2 = X3 | ~r1_partfun1(X2,X3) | ~v1_partfun1(X3,X0) | ~v1_partfun1(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f12])).
% 11.48/1.99  
% 11.48/1.99  fof(f41,plain,(
% 11.48/1.99    ( ! [X2,X0,X3,X1] : (v1_partfun1(sK2(X0,X1,X2,X3),X2) | ~sP0(X0,X1,X2,X3)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f24])).
% 11.48/1.99  
% 11.48/1.99  fof(f2,axiom,(
% 11.48/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ~(! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ~r1_partfun1(X2,X3)) & (k1_xboole_0 = X1 => k1_xboole_0 = X0)))),
% 11.48/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.99  
% 11.48/1.99  fof(f9,plain,(
% 11.48/1.99    ! [X0,X1,X2] : ((? [X3] : (r1_partfun1(X2,X3) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.48/1.99    inference(ennf_transformation,[],[f2])).
% 11.48/1.99  
% 11.48/1.99  fof(f10,plain,(
% 11.48/1.99    ! [X0,X1,X2] : (? [X3] : (r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.48/1.99    inference(flattening,[],[f9])).
% 11.48/1.99  
% 11.48/1.99  fof(f19,plain,(
% 11.48/1.99    ! [X2,X1,X0] : (? [X3] : (r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK1(X0,X1,X2),X0,X1) & v1_funct_1(sK1(X0,X1,X2))))),
% 11.48/1.99    introduced(choice_axiom,[])).
% 11.48/1.99  
% 11.48/1.99  fof(f20,plain,(
% 11.48/1.99    ! [X0,X1,X2] : ((r1_partfun1(X2,sK1(X0,X1,X2)) & m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK1(X0,X1,X2),X0,X1) & v1_funct_1(sK1(X0,X1,X2))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.48/1.99    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1])],[f10,f19])).
% 11.48/1.99  
% 11.48/1.99  fof(f36,plain,(
% 11.48/1.99    ( ! [X2,X0,X1] : (r1_partfun1(X2,sK1(X0,X1,X2)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f20])).
% 11.48/1.99  
% 11.48/1.99  fof(f30,plain,(
% 11.48/1.99    ( ! [X2,X0,X1] : (v1_funct_1(sK1(X0,X1,X2)) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f20])).
% 11.48/1.99  
% 11.48/1.99  fof(f1,axiom,(
% 11.48/1.99    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 11.48/1.99    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 11.48/1.99  
% 11.48/1.99  fof(f7,plain,(
% 11.48/1.99    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 11.48/1.99    inference(ennf_transformation,[],[f1])).
% 11.48/1.99  
% 11.48/1.99  fof(f8,plain,(
% 11.48/1.99    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 11.48/1.99    inference(flattening,[],[f7])).
% 11.48/1.99  
% 11.48/1.99  fof(f28,plain,(
% 11.48/1.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f8])).
% 11.48/1.99  
% 11.48/1.99  fof(f32,plain,(
% 11.48/1.99    ( ! [X2,X0,X1] : (v1_funct_2(sK1(X0,X1,X2),X0,X1) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f20])).
% 11.48/1.99  
% 11.48/1.99  fof(f34,plain,(
% 11.48/1.99    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f20])).
% 11.48/1.99  
% 11.48/1.99  fof(f42,plain,(
% 11.48/1.99    ( ! [X2,X0,X3,X1] : (r1_partfun1(X1,sK2(X0,X1,X2,X3)) | ~sP0(X0,X1,X2,X3)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f24])).
% 11.48/1.99  
% 11.48/1.99  fof(f52,plain,(
% 11.48/1.99    ( ! [X4] : (~r1_partfun1(sK6,X4) | ~r1_partfun1(sK5,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) | ~v1_funct_2(X4,sK3,sK4) | ~v1_funct_1(X4)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f27])).
% 11.48/1.99  
% 11.48/1.99  fof(f50,plain,(
% 11.48/1.99    k1_xboole_0 = sK3 | k1_xboole_0 != sK4),
% 11.48/1.99    inference(cnf_transformation,[],[f27])).
% 11.48/1.99  
% 11.48/1.99  fof(f45,plain,(
% 11.48/1.99    ( ! [X2,X0,X3,X1] : (sP0(X3,X2,X0,X1) | ~r1_partfun1(X2,X3) | k1_xboole_0 != X0 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f18])).
% 11.48/1.99  
% 11.48/1.99  fof(f58,plain,(
% 11.48/1.99    ( ! [X2,X3,X1] : (sP0(X3,X2,k1_xboole_0,X1) | ~r1_partfun1(X2,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(equality_resolution,[],[f45])).
% 11.48/1.99  
% 11.48/1.99  fof(f35,plain,(
% 11.48/1.99    ( ! [X2,X0,X1] : (m1_subset_1(sK1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f20])).
% 11.48/1.99  
% 11.48/1.99  fof(f55,plain,(
% 11.48/1.99    ( ! [X2,X1] : (m1_subset_1(sK1(k1_xboole_0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(equality_resolution,[],[f35])).
% 11.48/1.99  
% 11.48/1.99  fof(f37,plain,(
% 11.48/1.99    ( ! [X2,X0,X1] : (r1_partfun1(X2,sK1(X0,X1,X2)) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f20])).
% 11.48/1.99  
% 11.48/1.99  fof(f54,plain,(
% 11.48/1.99    ( ! [X2,X1] : (r1_partfun1(X2,sK1(k1_xboole_0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(equality_resolution,[],[f37])).
% 11.48/1.99  
% 11.48/1.99  fof(f31,plain,(
% 11.48/1.99    ( ! [X2,X0,X1] : (v1_funct_1(sK1(X0,X1,X2)) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f20])).
% 11.48/1.99  
% 11.48/1.99  fof(f57,plain,(
% 11.48/1.99    ( ! [X2,X1] : (v1_funct_1(sK1(k1_xboole_0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(equality_resolution,[],[f31])).
% 11.48/1.99  
% 11.48/1.99  fof(f29,plain,(
% 11.48/1.99    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f8])).
% 11.48/1.99  
% 11.48/1.99  fof(f53,plain,(
% 11.48/1.99    ( ! [X2,X1] : (v1_partfun1(X2,k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_2(X2,k1_xboole_0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(equality_resolution,[],[f29])).
% 11.48/1.99  
% 11.48/1.99  fof(f33,plain,(
% 11.48/1.99    ( ! [X2,X0,X1] : (v1_funct_2(sK1(X0,X1,X2),X0,X1) | k1_xboole_0 != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(cnf_transformation,[],[f20])).
% 11.48/1.99  
% 11.48/1.99  fof(f56,plain,(
% 11.48/1.99    ( ! [X2,X1] : (v1_funct_2(sK1(k1_xboole_0,X1,X2),k1_xboole_0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | ~v1_funct_1(X2)) )),
% 11.48/1.99    inference(equality_resolution,[],[f33])).
% 11.48/1.99  
% 11.48/1.99  cnf(c_21,negated_conjecture,
% 11.48/1.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 11.48/1.99      inference(cnf_transformation,[],[f49]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1593,plain,
% 11.48/1.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_23,negated_conjecture,
% 11.48/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 11.48/1.99      inference(cnf_transformation,[],[f47]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1591,plain,
% 11.48/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_17,plain,
% 11.48/1.99      ( sP0(X0,X1,X2,X3)
% 11.48/1.99      | ~ r1_partfun1(X1,X0)
% 11.48/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.48/1.99      | ~ v1_funct_1(X1)
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | k1_xboole_0 = X3 ),
% 11.48/1.99      inference(cnf_transformation,[],[f44]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1595,plain,
% 11.48/1.99      ( k1_xboole_0 = X0
% 11.48/1.99      | sP0(X1,X2,X3,X0) = iProver_top
% 11.48/1.99      | r1_partfun1(X2,X1) != iProver_top
% 11.48/1.99      | m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 11.48/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X3,X0))) != iProver_top
% 11.48/1.99      | v1_funct_1(X1) != iProver_top
% 11.48/1.99      | v1_funct_1(X2) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3261,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(X0,sK5,sK3,sK4) = iProver_top
% 11.48/1.99      | r1_partfun1(sK5,X0) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top
% 11.48/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1591,c_1595]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_24,negated_conjecture,
% 11.48/1.99      ( v1_funct_1(sK5) ),
% 11.48/1.99      inference(cnf_transformation,[],[f46]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_25,plain,
% 11.48/1.99      ( v1_funct_1(sK5) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_24]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_4296,plain,
% 11.48/1.99      ( v1_funct_1(X0) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 11.48/1.99      | r1_partfun1(sK5,X0) != iProver_top
% 11.48/1.99      | sP0(X0,sK5,sK3,sK4) = iProver_top
% 11.48/1.99      | sK4 = k1_xboole_0 ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_3261,c_25]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_4297,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(X0,sK5,sK3,sK4) = iProver_top
% 11.48/1.99      | r1_partfun1(sK5,X0) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(renaming,[status(thm)],[c_4296]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_4308,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK6,sK5,sK3,sK4) = iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK6) != iProver_top
% 11.48/1.99      | v1_funct_1(sK6) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1593,c_4297]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_22,negated_conjecture,
% 11.48/1.99      ( v1_funct_1(sK6) ),
% 11.48/1.99      inference(cnf_transformation,[],[f48]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_27,plain,
% 11.48/1.99      ( v1_funct_1(sK6) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_19,negated_conjecture,
% 11.48/1.99      ( r1_partfun1(sK5,sK6) ),
% 11.48/1.99      inference(cnf_transformation,[],[f51]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_29,plain,
% 11.48/1.99      ( r1_partfun1(sK5,sK6) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_19]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_4438,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0 | sP0(sK6,sK5,sK3,sK4) = iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_4308,c_27,c_29]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_11,plain,
% 11.48/1.99      ( ~ sP0(X0,X1,X2,X3) | r1_partfun1(X0,sK2(X0,X1,X2,X3)) ),
% 11.48/1.99      inference(cnf_transformation,[],[f43]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1601,plain,
% 11.48/1.99      ( sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | r1_partfun1(X0,sK2(X0,X1,X2,X3)) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_11]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14,plain,
% 11.48/1.99      ( ~ sP0(X0,X1,X2,X3)
% 11.48/1.99      | m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) ),
% 11.48/1.99      inference(cnf_transformation,[],[f40]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1598,plain,
% 11.48/1.99      ( sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | m1_subset_1(sK2(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_14]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3260,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(X0,sK6,sK3,sK4) = iProver_top
% 11.48/1.99      | r1_partfun1(sK6,X0) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top
% 11.48/1.99      | v1_funct_1(sK6) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1593,c_1595]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3826,plain,
% 11.48/1.99      ( v1_funct_1(X0) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,X0) != iProver_top
% 11.48/1.99      | sP0(X0,sK6,sK3,sK4) = iProver_top
% 11.48/1.99      | sK4 = k1_xboole_0 ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_3260,c_27]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3827,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(X0,sK6,sK3,sK4) = iProver_top
% 11.48/1.99      | r1_partfun1(sK6,X0) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(renaming,[status(thm)],[c_3826]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3837,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(X0,X1,sK3,sK4) != iProver_top
% 11.48/1.99      | sP0(sK2(X0,X1,sK3,sK4),sK6,sK3,sK4) = iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK2(X0,X1,sK3,sK4)) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(X0,X1,sK3,sK4)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1598,c_3827]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_15,plain,
% 11.48/1.99      ( ~ sP0(X0,X1,X2,X3) | v1_funct_1(sK2(X0,X1,X2,X3)) ),
% 11.48/1.99      inference(cnf_transformation,[],[f39]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1597,plain,
% 11.48/1.99      ( sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(X0,X1,X2,X3)) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_4614,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(X0,X1,sK3,sK4) != iProver_top
% 11.48/1.99      | sP0(sK2(X0,X1,sK3,sK4),sK6,sK3,sK4) = iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK2(X0,X1,sK3,sK4)) != iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_3837,c_1597]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_10,plain,
% 11.48/1.99      ( ~ r1_partfun1(X0,X1)
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.48/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.48/1.99      | ~ v1_partfun1(X1,X2)
% 11.48/1.99      | ~ v1_partfun1(X0,X2)
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | ~ v1_funct_1(X1)
% 11.48/1.99      | X1 = X0 ),
% 11.48/1.99      inference(cnf_transformation,[],[f38]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1602,plain,
% 11.48/1.99      ( X0 = X1
% 11.48/1.99      | r1_partfun1(X1,X0) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.48/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.48/1.99      | v1_partfun1(X0,X2) != iProver_top
% 11.48/1.99      | v1_partfun1(X1,X2) != iProver_top
% 11.48/1.99      | v1_funct_1(X1) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_10]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3335,plain,
% 11.48/1.99      ( sK2(X0,X1,X2,X3) = X4
% 11.48/1.99      | sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | r1_partfun1(sK2(X0,X1,X2,X3),X4) != iProver_top
% 11.48/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.48/1.99      | v1_partfun1(X4,X2) != iProver_top
% 11.48/1.99      | v1_partfun1(sK2(X0,X1,X2,X3),X2) != iProver_top
% 11.48/1.99      | v1_funct_1(X4) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(X0,X1,X2,X3)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1598,c_1602]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_39,plain,
% 11.48/1.99      ( sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(X0,X1,X2,X3)) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_15]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_13,plain,
% 11.48/1.99      ( ~ sP0(X0,X1,X2,X3) | v1_partfun1(sK2(X0,X1,X2,X3),X2) ),
% 11.48/1.99      inference(cnf_transformation,[],[f41]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_45,plain,
% 11.48/1.99      ( sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | v1_partfun1(sK2(X0,X1,X2,X3),X2) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_8682,plain,
% 11.48/1.99      ( v1_funct_1(X4) != iProver_top
% 11.48/1.99      | sK2(X0,X1,X2,X3) = X4
% 11.48/1.99      | sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | r1_partfun1(sK2(X0,X1,X2,X3),X4) != iProver_top
% 11.48/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.48/1.99      | v1_partfun1(X4,X2) != iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_3335,c_39,c_45]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_8683,plain,
% 11.48/1.99      ( sK2(X0,X1,X2,X3) = X4
% 11.48/1.99      | sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | r1_partfun1(sK2(X0,X1,X2,X3),X4) != iProver_top
% 11.48/1.99      | m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.48/1.99      | v1_partfun1(X4,X2) != iProver_top
% 11.48/1.99      | v1_funct_1(X4) != iProver_top ),
% 11.48/1.99      inference(renaming,[status(thm)],[c_8682]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_8694,plain,
% 11.48/1.99      ( sK2(sK2(X0,X1,X2,X3),X4,X5,X6) = sK2(X0,X1,X2,X3)
% 11.48/1.99      | sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | sP0(sK2(X0,X1,X2,X3),X4,X5,X6) != iProver_top
% 11.48/1.99      | m1_subset_1(sK2(sK2(X0,X1,X2,X3),X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.48/1.99      | v1_partfun1(sK2(sK2(X0,X1,X2,X3),X4,X5,X6),X2) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK2(X0,X1,X2,X3),X4,X5,X6)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1601,c_8683]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_13400,plain,
% 11.48/1.99      ( sK2(sK2(X0,X1,X2,X3),X4,X5,X6) = sK2(X0,X1,X2,X3)
% 11.48/1.99      | sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | sP0(sK2(X0,X1,X2,X3),X4,X5,X6) != iProver_top
% 11.48/1.99      | m1_subset_1(sK2(sK2(X0,X1,X2,X3),X4,X5,X6),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) != iProver_top
% 11.48/1.99      | v1_partfun1(sK2(sK2(X0,X1,X2,X3),X4,X5,X6),X2) != iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_8694,c_1597]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_13404,plain,
% 11.48/1.99      ( sK2(sK2(X0,X1,X2,X3),X4,X2,X3) = sK2(X0,X1,X2,X3)
% 11.48/1.99      | sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | sP0(sK2(X0,X1,X2,X3),X4,X2,X3) != iProver_top
% 11.48/1.99      | v1_partfun1(sK2(sK2(X0,X1,X2,X3),X4,X2,X3),X2) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1598,c_13400]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1599,plain,
% 11.48/1.99      ( sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | v1_partfun1(sK2(X0,X1,X2,X3),X2) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_13]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_13453,plain,
% 11.48/1.99      ( sK2(sK2(X0,X1,X2,X3),X4,X2,X3) = sK2(X0,X1,X2,X3)
% 11.48/1.99      | sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | sP0(sK2(X0,X1,X2,X3),X4,X2,X3) != iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_13404,c_1599]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_13461,plain,
% 11.48/1.99      ( sK2(sK2(X0,X1,sK3,sK4),sK6,sK3,sK4) = sK2(X0,X1,sK3,sK4)
% 11.48/1.99      | sK4 = k1_xboole_0
% 11.48/1.99      | sP0(X0,X1,sK3,sK4) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK2(X0,X1,sK3,sK4)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_4614,c_13453]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_13833,plain,
% 11.48/1.99      ( sK2(sK2(sK6,X0,sK3,sK4),sK6,sK3,sK4) = sK2(sK6,X0,sK3,sK4)
% 11.48/1.99      | sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK6,X0,sK3,sK4) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1601,c_13461]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14148,plain,
% 11.48/1.99      ( sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) = sK2(sK6,sK5,sK3,sK4)
% 11.48/1.99      | sK4 = k1_xboole_0 ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_4438,c_13833]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3,plain,
% 11.48/1.99      ( r1_partfun1(X0,sK1(X1,X2,X0))
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | k1_xboole_0 = X2 ),
% 11.48/1.99      inference(cnf_transformation,[],[f36]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1607,plain,
% 11.48/1.99      ( k1_xboole_0 = X0
% 11.48/1.99      | r1_partfun1(X1,sK1(X2,X0,X1)) = iProver_top
% 11.48/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 11.48/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_3]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2938,plain,
% 11.48/1.99      ( k1_xboole_0 = X0
% 11.48/1.99      | sP0(X1,X2,X3,X0) != iProver_top
% 11.48/1.99      | r1_partfun1(sK2(X1,X2,X3,X0),sK1(X3,X0,sK2(X1,X2,X3,X0))) = iProver_top
% 11.48/1.99      | v1_funct_1(sK2(X1,X2,X3,X0)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1598,c_1607]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_5871,plain,
% 11.48/1.99      ( k1_xboole_0 = X0
% 11.48/1.99      | sP0(X1,X2,X3,X0) != iProver_top
% 11.48/1.99      | r1_partfun1(sK2(X1,X2,X3,X0),sK1(X3,X0,sK2(X1,X2,X3,X0))) = iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_2938,c_1597]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_8697,plain,
% 11.48/1.99      ( sK1(X0,X1,sK2(X2,X3,X0,X1)) = sK2(X2,X3,X0,X1)
% 11.48/1.99      | k1_xboole_0 = X1
% 11.48/1.99      | sP0(X2,X3,X0,X1) != iProver_top
% 11.48/1.99      | m1_subset_1(sK1(X0,X1,sK2(X2,X3,X0,X1)),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top
% 11.48/1.99      | v1_partfun1(sK1(X0,X1,sK2(X2,X3,X0,X1)),X0) != iProver_top
% 11.48/1.99      | v1_funct_1(sK1(X0,X1,sK2(X2,X3,X0,X1))) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_5871,c_8683]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_9,plain,
% 11.48/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | v1_funct_1(sK1(X1,X2,X0))
% 11.48/1.99      | k1_xboole_0 = X2 ),
% 11.48/1.99      inference(cnf_transformation,[],[f30]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1603,plain,
% 11.48/1.99      ( k1_xboole_0 = X0
% 11.48/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 11.48/1.99      | v1_funct_1(X1) != iProver_top
% 11.48/1.99      | v1_funct_1(sK1(X2,X0,X1)) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_9]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2895,plain,
% 11.48/1.99      ( k1_xboole_0 = X0
% 11.48/1.99      | sP0(X1,X2,X3,X0) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(X1,X2,X3,X0)) != iProver_top
% 11.48/1.99      | v1_funct_1(sK1(X3,X0,sK2(X1,X2,X3,X0))) = iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1598,c_1603]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3492,plain,
% 11.48/1.99      ( k1_xboole_0 = X0
% 11.48/1.99      | sP0(X1,X2,X3,X0) != iProver_top
% 11.48/1.99      | v1_funct_1(sK1(X3,X0,sK2(X1,X2,X3,X0))) = iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_2895,c_1597]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1,plain,
% 11.48/1.99      ( ~ v1_funct_2(X0,X1,X2)
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.48/1.99      | v1_partfun1(X0,X1)
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | k1_xboole_0 = X2 ),
% 11.48/1.99      inference(cnf_transformation,[],[f28]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_7,plain,
% 11.48/1.99      ( v1_funct_2(sK1(X0,X1,X2),X0,X1)
% 11.48/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.48/1.99      | ~ v1_funct_1(X2)
% 11.48/1.99      | k1_xboole_0 = X1 ),
% 11.48/1.99      inference(cnf_transformation,[],[f32]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_307,plain,
% 11.48/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.48/1.99      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 11.48/1.99      | v1_partfun1(X0,X1)
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | ~ v1_funct_1(X3)
% 11.48/1.99      | X4 != X1
% 11.48/1.99      | X5 != X2
% 11.48/1.99      | sK1(X4,X5,X3) != X0
% 11.48/1.99      | k1_xboole_0 = X2
% 11.48/1.99      | k1_xboole_0 = X5 ),
% 11.48/1.99      inference(resolution_lifted,[status(thm)],[c_1,c_7]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_308,plain,
% 11.48/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.48/1.99      | ~ m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.48/1.99      | v1_partfun1(sK1(X1,X2,X0),X1)
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | ~ v1_funct_1(sK1(X1,X2,X0))
% 11.48/1.99      | k1_xboole_0 = X2 ),
% 11.48/1.99      inference(unflattening,[status(thm)],[c_307]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_5,plain,
% 11.48/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.48/1.99      | m1_subset_1(sK1(X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | k1_xboole_0 = X2 ),
% 11.48/1.99      inference(cnf_transformation,[],[f34]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_310,plain,
% 11.48/1.99      ( ~ v1_funct_1(X0)
% 11.48/1.99      | v1_partfun1(sK1(X1,X2,X0),X1)
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.48/1.99      | k1_xboole_0 = X2 ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_308,c_9,c_5]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_311,plain,
% 11.48/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 11.48/1.99      | v1_partfun1(sK1(X1,X2,X0),X1)
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | k1_xboole_0 = X2 ),
% 11.48/1.99      inference(renaming,[status(thm)],[c_310]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1588,plain,
% 11.48/1.99      ( k1_xboole_0 = X0
% 11.48/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) != iProver_top
% 11.48/1.99      | v1_partfun1(sK1(X2,X0,X1),X2) = iProver_top
% 11.48/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_311]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2762,plain,
% 11.48/1.99      ( k1_xboole_0 = X0
% 11.48/1.99      | sP0(X1,X2,X3,X0) != iProver_top
% 11.48/1.99      | v1_partfun1(sK1(X3,X0,sK2(X1,X2,X3,X0)),X3) = iProver_top
% 11.48/1.99      | v1_funct_1(sK2(X1,X2,X3,X0)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1598,c_1588]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_4503,plain,
% 11.48/1.99      ( k1_xboole_0 = X0
% 11.48/1.99      | sP0(X1,X2,X3,X0) != iProver_top
% 11.48/1.99      | v1_partfun1(sK1(X3,X0,sK2(X1,X2,X3,X0)),X3) = iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_2762,c_1597]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_27851,plain,
% 11.48/1.99      ( sK1(X0,X1,sK2(X2,X3,X0,X1)) = sK2(X2,X3,X0,X1)
% 11.48/1.99      | k1_xboole_0 = X1
% 11.48/1.99      | sP0(X2,X3,X0,X1) != iProver_top
% 11.48/1.99      | m1_subset_1(sK1(X0,X1,sK2(X2,X3,X0,X1)),k1_zfmisc_1(k2_zfmisc_1(X0,X1))) != iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_8697,c_3492,c_4503]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_27857,plain,
% 11.48/1.99      ( sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) = sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)
% 11.48/1.99      | sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) != iProver_top
% 11.48/1.99      | m1_subset_1(sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_14148,c_27851]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1170,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2061,plain,
% 11.48/1.99      ( X0 != X1 | sK4 != X1 | sK4 = X0 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1170]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2737,plain,
% 11.48/1.99      ( X0 != sK4 | sK4 = X0 | sK4 != sK4 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_2061]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2739,plain,
% 11.48/1.99      ( sK4 != sK4 | sK4 = k1_xboole_0 | k1_xboole_0 != sK4 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_2737]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1169,plain,( X0 = X0 ),theory(equality) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2738,plain,
% 11.48/1.99      ( sK4 = sK4 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1169]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14497,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_14148,c_1597]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14221,plain,
% 11.48/1.99      ( ~ sP0(sK6,sK5,sK3,sK4) | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_15]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14222,plain,
% 11.48/1.99      ( sP0(sK6,sK5,sK3,sK4) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_14221]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_15578,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_14497,c_27,c_29,c_4308,c_14222]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14493,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) != iProver_top
% 11.48/1.99      | m1_subset_1(sK2(sK6,sK5,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_14148,c_1598]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14217,plain,
% 11.48/1.99      ( ~ sP0(sK6,sK5,sK3,sK4)
% 11.48/1.99      | m1_subset_1(sK2(sK6,sK5,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_14]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14230,plain,
% 11.48/1.99      ( sP0(sK6,sK5,sK3,sK4) != iProver_top
% 11.48/1.99      | m1_subset_1(sK2(sK6,sK5,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_14217]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_16688,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | m1_subset_1(sK2(sK6,sK5,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_14493,c_27,c_29,c_4308,c_14230]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_16701,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) = iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK2(sK6,sK5,sK3,sK4)) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_16688,c_3827]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_12,plain,
% 11.48/1.99      ( ~ sP0(X0,X1,X2,X3) | r1_partfun1(X1,sK2(X0,X1,X2,X3)) ),
% 11.48/1.99      inference(cnf_transformation,[],[f42]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1600,plain,
% 11.48/1.99      ( sP0(X0,X1,X2,X3) != iProver_top
% 11.48/1.99      | r1_partfun1(X1,sK2(X0,X1,X2,X3)) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_12]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14495,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_14148,c_1600]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14220,plain,
% 11.48/1.99      ( ~ sP0(sK6,sK5,sK3,sK4) | r1_partfun1(sK6,sK2(sK6,sK5,sK3,sK4)) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14224,plain,
% 11.48/1.99      ( sP0(sK6,sK5,sK3,sK4) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_14220]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_15590,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | r1_partfun1(sK6,sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_14495,c_27,c_29,c_4308,c_14224]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_16943,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) = iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_16701,c_15578,c_15590]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1911,plain,
% 11.48/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
% 11.48/1.99      | m1_subset_1(sK1(X1,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(X1,sK4)))
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | k1_xboole_0 = sK4 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_5]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_20361,plain,
% 11.48/1.99      ( ~ m1_subset_1(sK2(sK6,sK5,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | m1_subset_1(sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | ~ v1_funct_1(sK2(sK6,sK5,sK3,sK4))
% 11.48/1.99      | k1_xboole_0 = sK4 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1911]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_20371,plain,
% 11.48/1.99      ( k1_xboole_0 = sK4
% 11.48/1.99      | m1_subset_1(sK2(sK6,sK5,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 11.48/1.99      | m1_subset_1(sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4)),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_20361]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_36958,plain,
% 11.48/1.99      ( sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) = sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)
% 11.48/1.99      | sK4 = k1_xboole_0 ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_27857,c_2739,c_2738,c_15578,c_16688,c_16943,c_20371]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_36962,plain,
% 11.48/1.99      ( sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) = sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4))
% 11.48/1.99      | sK4 = k1_xboole_0 ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_14148,c_36958]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_4307,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(X0,X1,sK3,sK4) != iProver_top
% 11.48/1.99      | sP0(sK2(X0,X1,sK3,sK4),sK5,sK3,sK4) = iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK2(X0,X1,sK3,sK4)) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(X0,X1,sK3,sK4)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1598,c_4297]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_4624,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(X0,X1,sK3,sK4) != iProver_top
% 11.48/1.99      | sP0(sK2(X0,X1,sK3,sK4),sK5,sK3,sK4) = iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK2(X0,X1,sK3,sK4)) != iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_4307,c_1597]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_13462,plain,
% 11.48/1.99      ( sK2(sK2(X0,X1,sK3,sK4),sK5,sK3,sK4) = sK2(X0,X1,sK3,sK4)
% 11.48/1.99      | sK4 = k1_xboole_0
% 11.48/1.99      | sP0(X0,X1,sK3,sK4) != iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK2(X0,X1,sK3,sK4)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_4624,c_13453]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14498,plain,
% 11.48/1.99      ( sK2(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4),sK5,sK3,sK4) = sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)
% 11.48/1.99      | sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) != iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK2(sK6,sK5,sK3,sK4)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_14148,c_13462]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_13873,plain,
% 11.48/1.99      ( sK2(sK2(X0,sK5,sK3,sK4),sK5,sK3,sK4) = sK2(X0,sK5,sK3,sK4)
% 11.48/1.99      | sK4 = k1_xboole_0
% 11.48/1.99      | sP0(X0,sK5,sK3,sK4) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1600,c_13462]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14450,plain,
% 11.48/1.99      ( sK2(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) = sK2(sK6,sK5,sK3,sK4)
% 11.48/1.99      | sK4 = k1_xboole_0 ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_4438,c_13873]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14848,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) != iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_14450,c_1600]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14219,plain,
% 11.48/1.99      ( ~ sP0(sK6,sK5,sK3,sK4) | r1_partfun1(sK5,sK2(sK6,sK5,sK3,sK4)) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_12]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_14226,plain,
% 11.48/1.99      ( sP0(sK6,sK5,sK3,sK4) != iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_14219]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_16552,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | r1_partfun1(sK5,sK2(sK6,sK5,sK3,sK4)) = iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_14848,c_27,c_29,c_4308,c_14226]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_19096,plain,
% 11.48/1.99      ( sK2(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4),sK5,sK3,sK4) = sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)
% 11.48/1.99      | sK4 = k1_xboole_0 ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_14498,c_16552,c_16943]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_19100,plain,
% 11.48/1.99      ( sK2(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) = sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)
% 11.48/1.99      | sK4 = k1_xboole_0 ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_14148,c_19096]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_19490,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) != iProver_top
% 11.48/1.99      | m1_subset_1(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_19100,c_1598]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_16700,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) = iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK2(sK6,sK5,sK3,sK4)) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK6,sK5,sK3,sK4)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_16688,c_4297]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_16921,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) = iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_16700,c_15578,c_16552]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_21198,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | m1_subset_1(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_19490,c_16921]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_21211,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4),sK5,sK3,sK4) = iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_21198,c_4297]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_19492,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) != iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) = iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_19100,c_1600]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_19494,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK5,sK3,sK4) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) = iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_19100,c_1597]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_21408,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4),sK5,sK3,sK4) = iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_21211,c_16921,c_19492,c_19494]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_37727,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4)),sK5,sK3,sK4) = iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_36962,c_21408]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_20622,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | r1_partfun1(sK5,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) = iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_19492,c_16921]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_18,negated_conjecture,
% 11.48/1.99      ( ~ v1_funct_2(X0,sK3,sK4)
% 11.48/1.99      | ~ r1_partfun1(sK5,X0)
% 11.48/1.99      | ~ r1_partfun1(sK6,X0)
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | ~ v1_funct_1(X0) ),
% 11.48/1.99      inference(cnf_transformation,[],[f52]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_358,plain,
% 11.48/1.99      ( ~ r1_partfun1(sK5,X0)
% 11.48/1.99      | ~ r1_partfun1(sK6,X0)
% 11.48/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | ~ v1_funct_1(X1)
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | sK1(X2,X3,X1) != X0
% 11.48/1.99      | sK4 != X3
% 11.48/1.99      | sK3 != X2
% 11.48/1.99      | k1_xboole_0 = X3 ),
% 11.48/1.99      inference(resolution_lifted,[status(thm)],[c_7,c_18]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_359,plain,
% 11.48/1.99      ( ~ r1_partfun1(sK5,sK1(sK3,sK4,X0))
% 11.48/1.99      | ~ r1_partfun1(sK6,sK1(sK3,sK4,X0))
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | ~ m1_subset_1(sK1(sK3,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | ~ v1_funct_1(sK1(sK3,sK4,X0))
% 11.48/1.99      | k1_xboole_0 = sK4 ),
% 11.48/1.99      inference(unflattening,[status(thm)],[c_358]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_377,plain,
% 11.48/1.99      ( ~ r1_partfun1(sK5,sK1(sK3,sK4,X0))
% 11.48/1.99      | ~ r1_partfun1(sK6,sK1(sK3,sK4,X0))
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | k1_xboole_0 = sK4 ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_359,c_9,c_5]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1586,plain,
% 11.48/1.99      ( k1_xboole_0 = sK4
% 11.48/1.99      | r1_partfun1(sK5,sK1(sK3,sK4,X0)) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK1(sK3,sK4,X0)) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_377]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_21215,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | r1_partfun1(sK5,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_21198,c_1586]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_21612,plain,
% 11.48/1.99      ( r1_partfun1(sK6,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top
% 11.48/1.99      | sK4 = k1_xboole_0 ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_21215,c_16921,c_19494]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_21613,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | r1_partfun1(sK5,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top ),
% 11.48/1.99      inference(renaming,[status(thm)],[c_21612]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_21619,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | r1_partfun1(sK5,sK1(sK3,sK4,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4))) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4))) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_14148,c_21613]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_36999,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | r1_partfun1(sK5,sK2(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4)) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4))) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_36958,c_21619]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_37666,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0
% 11.48/1.99      | sP0(sK2(sK6,sK5,sK3,sK4),sK6,sK3,sK4) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK1(sK3,sK4,sK2(sK6,sK5,sK3,sK4))) = iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_36962,c_1600]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_38361,plain,
% 11.48/1.99      ( sK4 = k1_xboole_0 ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_37727,c_16943,c_20622,c_36999,c_37666]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_38563,plain,
% 11.48/1.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 11.48/1.99      inference(demodulation,[status(thm)],[c_38361,c_1593]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_20,negated_conjecture,
% 11.48/1.99      ( k1_xboole_0 != sK4 | k1_xboole_0 = sK3 ),
% 11.48/1.99      inference(cnf_transformation,[],[f50]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_38565,plain,
% 11.48/1.99      ( sK3 = k1_xboole_0 | k1_xboole_0 != k1_xboole_0 ),
% 11.48/1.99      inference(demodulation,[status(thm)],[c_38361,c_20]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_38566,plain,
% 11.48/1.99      ( sK3 = k1_xboole_0 ),
% 11.48/1.99      inference(equality_resolution_simp,[status(thm)],[c_38565]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_38572,plain,
% 11.48/1.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.48/1.99      inference(light_normalisation,[status(thm)],[c_38563,c_38566]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_38564,plain,
% 11.48/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) = iProver_top ),
% 11.48/1.99      inference(demodulation,[status(thm)],[c_38361,c_1591]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_38569,plain,
% 11.48/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.48/1.99      inference(light_normalisation,[status(thm)],[c_38564,c_38566]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_16,plain,
% 11.48/1.99      ( sP0(X0,X1,k1_xboole_0,X2)
% 11.48/1.99      | ~ r1_partfun1(X1,X0)
% 11.48/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 11.48/1.99      | ~ v1_funct_1(X1)
% 11.48/1.99      | ~ v1_funct_1(X0) ),
% 11.48/1.99      inference(cnf_transformation,[],[f58]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1596,plain,
% 11.48/1.99      ( sP0(X0,X1,k1_xboole_0,X2) = iProver_top
% 11.48/1.99      | r1_partfun1(X1,X0) != iProver_top
% 11.48/1.99      | m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top
% 11.48/1.99      | v1_funct_1(X1) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_16]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_38750,plain,
% 11.48/1.99      ( sP0(X0,sK5,k1_xboole_0,k1_xboole_0) = iProver_top
% 11.48/1.99      | r1_partfun1(sK5,X0) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top
% 11.48/1.99      | v1_funct_1(sK5) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_38569,c_1596]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_39480,plain,
% 11.48/1.99      ( v1_funct_1(X0) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | r1_partfun1(sK5,X0) != iProver_top
% 11.48/1.99      | sP0(X0,sK5,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_38750,c_25]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_39481,plain,
% 11.48/1.99      ( sP0(X0,sK5,k1_xboole_0,k1_xboole_0) = iProver_top
% 11.48/1.99      | r1_partfun1(sK5,X0) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(renaming,[status(thm)],[c_39480]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_39493,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) = iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK6) != iProver_top
% 11.48/1.99      | v1_funct_1(sK6) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_38572,c_39481]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_26,plain,
% 11.48/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_28,plain,
% 11.48/1.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_21]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1188,plain,
% 11.48/1.99      ( k1_xboole_0 = k1_xboole_0 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1169]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1874,plain,
% 11.48/1.99      ( sK4 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK4 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1170]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1875,plain,
% 11.48/1.99      ( sK4 != k1_xboole_0
% 11.48/1.99      | k1_xboole_0 = sK4
% 11.48/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1874]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2077,plain,
% 11.48/1.99      ( sK6 = sK6 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1169]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2098,plain,
% 11.48/1.99      ( sK5 = sK5 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1169]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1925,plain,
% 11.48/1.99      ( sP0(X0,sK5,k1_xboole_0,X1)
% 11.48/1.99      | ~ r1_partfun1(sK5,X0)
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.48/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | ~ v1_funct_1(sK5) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_16]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2175,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,X0)
% 11.48/1.99      | ~ r1_partfun1(sK5,sK6)
% 11.48/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 11.48/1.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 11.48/1.99      | ~ v1_funct_1(sK5)
% 11.48/1.99      | ~ v1_funct_1(sK6) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1925]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2176,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,X0) = iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK6) != iProver_top
% 11.48/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 11.48/1.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 11.48/1.99      | v1_funct_1(sK5) != iProver_top
% 11.48/1.99      | v1_funct_1(sK6) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_2175]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2178,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) = iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK6) != iProver_top
% 11.48/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | v1_funct_1(sK5) != iProver_top
% 11.48/1.99      | v1_funct_1(sK6) != iProver_top ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_2176]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1173,plain,
% 11.48/1.99      ( X0 != X1 | k1_zfmisc_1(X0) = k1_zfmisc_1(X1) ),
% 11.48/1.99      theory(equality) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2858,plain,
% 11.48/1.99      ( X0 != k2_zfmisc_1(sK3,sK4)
% 11.48/1.99      | k1_zfmisc_1(X0) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1173]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3734,plain,
% 11.48/1.99      ( k2_zfmisc_1(X0,X1) != k2_zfmisc_1(sK3,sK4)
% 11.48/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_2858]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3736,plain,
% 11.48/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) != k2_zfmisc_1(sK3,sK4)
% 11.48/1.99      | k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) = k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_3734]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1172,plain,
% 11.48/1.99      ( X0 != X1 | X2 != X3 | k2_zfmisc_1(X0,X2) = k2_zfmisc_1(X1,X3) ),
% 11.48/1.99      theory(equality) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3735,plain,
% 11.48/1.99      ( X0 != sK4
% 11.48/1.99      | X1 != sK3
% 11.48/1.99      | k2_zfmisc_1(X1,X0) = k2_zfmisc_1(sK3,sK4) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1172]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3737,plain,
% 11.48/1.99      ( k2_zfmisc_1(k1_xboole_0,k1_xboole_0) = k2_zfmisc_1(sK3,sK4)
% 11.48/1.99      | k1_xboole_0 != sK4
% 11.48/1.99      | k1_xboole_0 != sK3 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_3735]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1174,plain,
% 11.48/1.99      ( ~ m1_subset_1(X0,X1) | m1_subset_1(X2,X3) | X2 != X0 | X3 != X1 ),
% 11.48/1.99      theory(equality) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1891,plain,
% 11.48/1.99      ( m1_subset_1(X0,X1)
% 11.48/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | X1 != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 11.48/1.99      | X0 != sK5 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1174]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2097,plain,
% 11.48/1.99      ( m1_subset_1(sK5,X0)
% 11.48/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | X0 != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 11.48/1.99      | sK5 != sK5 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1891]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_5119,plain,
% 11.48/1.99      ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.48/1.99      | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 11.48/1.99      | sK5 != sK5 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_2097]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_5121,plain,
% 11.48/1.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 11.48/1.99      | sK5 != sK5
% 11.48/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 11.48/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_5119]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_5123,plain,
% 11.48/1.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 11.48/1.99      | sK5 != sK5
% 11.48/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 11.48/1.99      | m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_5121]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1886,plain,
% 11.48/1.99      ( m1_subset_1(X0,X1)
% 11.48/1.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | X1 != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 11.48/1.99      | X0 != sK6 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1174]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2076,plain,
% 11.48/1.99      ( m1_subset_1(sK6,X0)
% 11.48/1.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | X0 != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 11.48/1.99      | sK6 != sK6 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_1886]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2857,plain,
% 11.48/1.99      ( m1_subset_1(sK6,k1_zfmisc_1(X0))
% 11.48/1.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | k1_zfmisc_1(X0) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 11.48/1.99      | sK6 != sK6 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_2076]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_5127,plain,
% 11.48/1.99      ( m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 11.48/1.99      | ~ m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 11.48/1.99      | sK6 != sK6 ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_2857]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_5128,plain,
% 11.48/1.99      ( k1_zfmisc_1(k2_zfmisc_1(X0,X1)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 11.48/1.99      | sK6 != sK6
% 11.48/1.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) = iProver_top
% 11.48/1.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_5127]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_5130,plain,
% 11.48/1.99      ( k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)) != k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))
% 11.48/1.99      | sK6 != sK6
% 11.48/1.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 11.48/1.99      | m1_subset_1(sK6,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_5128]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_39661,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) = iProver_top ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_39493,c_25,c_26,c_27,c_28,c_20,c_29,c_1188,c_1875,
% 11.48/1.99                 c_2077,c_2098,c_2178,c_3736,c_3737,c_5123,c_5130,
% 11.48/1.99                 c_16943,c_20622,c_36999,c_37666]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_4,plain,
% 11.48/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.48/1.99      | m1_subset_1(sK1(k1_xboole_0,X1,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.48/1.99      | ~ v1_funct_1(X0) ),
% 11.48/1.99      inference(cnf_transformation,[],[f55]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1606,plain,
% 11.48/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 11.48/1.99      | m1_subset_1(sK1(k1_xboole_0,X1,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) = iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_4]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2,plain,
% 11.48/1.99      ( r1_partfun1(X0,sK1(k1_xboole_0,X1,X0))
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.48/1.99      | ~ v1_funct_1(X0) ),
% 11.48/1.99      inference(cnf_transformation,[],[f54]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1608,plain,
% 11.48/1.99      ( r1_partfun1(X0,sK1(k1_xboole_0,X1,X0)) = iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_2]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2692,plain,
% 11.48/1.99      ( sP0(X0,X1,k1_xboole_0,X2) != iProver_top
% 11.48/1.99      | r1_partfun1(sK2(X0,X1,k1_xboole_0,X2),sK1(k1_xboole_0,X2,sK2(X0,X1,k1_xboole_0,X2))) = iProver_top
% 11.48/1.99      | v1_funct_1(sK2(X0,X1,k1_xboole_0,X2)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1598,c_1608]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_4361,plain,
% 11.48/1.99      ( sP0(X0,X1,k1_xboole_0,X2) != iProver_top
% 11.48/1.99      | r1_partfun1(sK2(X0,X1,k1_xboole_0,X2),sK1(k1_xboole_0,X2,sK2(X0,X1,k1_xboole_0,X2))) = iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_2692,c_1597]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_8696,plain,
% 11.48/1.99      ( sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)) = sK2(X1,X2,k1_xboole_0,X0)
% 11.48/1.99      | sP0(X1,X2,k1_xboole_0,X0) != iProver_top
% 11.48/1.99      | m1_subset_1(sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 11.48/1.99      | v1_partfun1(sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)),k1_xboole_0) != iProver_top
% 11.48/1.99      | v1_funct_1(sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0))) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_4361,c_8683]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_8,plain,
% 11.48/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | v1_funct_1(sK1(k1_xboole_0,X1,X0)) ),
% 11.48/1.99      inference(cnf_transformation,[],[f57]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1604,plain,
% 11.48/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top
% 11.48/1.99      | v1_funct_1(sK1(k1_xboole_0,X1,X0)) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_8]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2664,plain,
% 11.48/1.99      ( sP0(X0,X1,k1_xboole_0,X2) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(X0,X1,k1_xboole_0,X2)) != iProver_top
% 11.48/1.99      | v1_funct_1(sK1(k1_xboole_0,X2,sK2(X0,X1,k1_xboole_0,X2))) = iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1598,c_1604]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2752,plain,
% 11.48/1.99      ( sP0(X0,X1,k1_xboole_0,X2) != iProver_top
% 11.48/1.99      | v1_funct_1(sK1(k1_xboole_0,X2,sK2(X0,X1,k1_xboole_0,X2))) = iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_2664,c_1597]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_0,plain,
% 11.48/1.99      ( ~ v1_funct_2(X0,k1_xboole_0,X1)
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.48/1.99      | v1_partfun1(X0,k1_xboole_0)
% 11.48/1.99      | ~ v1_funct_1(X0) ),
% 11.48/1.99      inference(cnf_transformation,[],[f53]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6,plain,
% 11.48/1.99      ( v1_funct_2(sK1(k1_xboole_0,X0,X1),k1_xboole_0,X0)
% 11.48/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0)))
% 11.48/1.99      | ~ v1_funct_1(X1) ),
% 11.48/1.99      inference(cnf_transformation,[],[f56]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_270,plain,
% 11.48/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.48/1.99      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X3)))
% 11.48/1.99      | v1_partfun1(X0,k1_xboole_0)
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | ~ v1_funct_1(X2)
% 11.48/1.99      | X3 != X1
% 11.48/1.99      | sK1(k1_xboole_0,X3,X2) != X0
% 11.48/1.99      | k1_xboole_0 != k1_xboole_0 ),
% 11.48/1.99      inference(resolution_lifted,[status(thm)],[c_0,c_6]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_271,plain,
% 11.48/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.48/1.99      | ~ m1_subset_1(sK1(k1_xboole_0,X1,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.48/1.99      | v1_partfun1(sK1(k1_xboole_0,X1,X0),k1_xboole_0)
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | ~ v1_funct_1(sK1(k1_xboole_0,X1,X0)) ),
% 11.48/1.99      inference(unflattening,[status(thm)],[c_270]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_275,plain,
% 11.48/1.99      ( ~ v1_funct_1(X0)
% 11.48/1.99      | v1_partfun1(sK1(k1_xboole_0,X1,X0),k1_xboole_0)
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ),
% 11.48/1.99      inference(global_propositional_subsumption,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_271,c_8,c_4]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_276,plain,
% 11.48/1.99      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
% 11.48/1.99      | v1_partfun1(sK1(k1_xboole_0,X1,X0),k1_xboole_0)
% 11.48/1.99      | ~ v1_funct_1(X0) ),
% 11.48/1.99      inference(renaming,[status(thm)],[c_275]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1589,plain,
% 11.48/1.99      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) != iProver_top
% 11.48/1.99      | v1_partfun1(sK1(k1_xboole_0,X1,X0),k1_xboole_0) = iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_276]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_2672,plain,
% 11.48/1.99      ( sP0(X0,X1,k1_xboole_0,X2) != iProver_top
% 11.48/1.99      | v1_partfun1(sK1(k1_xboole_0,X2,sK2(X0,X1,k1_xboole_0,X2)),k1_xboole_0) = iProver_top
% 11.48/1.99      | v1_funct_1(sK2(X0,X1,k1_xboole_0,X2)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1598,c_1589]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_3443,plain,
% 11.48/1.99      ( sP0(X0,X1,k1_xboole_0,X2) != iProver_top
% 11.48/1.99      | v1_partfun1(sK1(k1_xboole_0,X2,sK2(X0,X1,k1_xboole_0,X2)),k1_xboole_0) = iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_2672,c_1597]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_25453,plain,
% 11.48/1.99      ( sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)) = sK2(X1,X2,k1_xboole_0,X0)
% 11.48/1.99      | sP0(X1,X2,k1_xboole_0,X0) != iProver_top
% 11.48/1.99      | m1_subset_1(sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_8696,c_2752,c_3443]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_25457,plain,
% 11.48/1.99      ( sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)) = sK2(X1,X2,k1_xboole_0,X0)
% 11.48/1.99      | sP0(X1,X2,k1_xboole_0,X0) != iProver_top
% 11.48/1.99      | m1_subset_1(sK2(X1,X2,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(X1,X2,k1_xboole_0,X0)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_1606,c_25453]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_41464,plain,
% 11.48/1.99      ( sK1(k1_xboole_0,X0,sK2(X1,X2,k1_xboole_0,X0)) = sK2(X1,X2,k1_xboole_0,X0)
% 11.48/1.99      | sP0(X1,X2,k1_xboole_0,X0) != iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_25457,c_1597,c_1598]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_41470,plain,
% 11.48/1.99      ( sK1(k1_xboole_0,k1_xboole_0,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) = sK2(sK6,sK5,k1_xboole_0,k1_xboole_0) ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_39661,c_41464]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_329,plain,
% 11.48/1.99      ( ~ r1_partfun1(sK5,X0)
% 11.48/1.99      | ~ r1_partfun1(sK6,X0)
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))
% 11.48/1.99      | ~ v1_funct_1(X1)
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | sK1(k1_xboole_0,X2,X1) != X0
% 11.48/1.99      | sK4 != X2
% 11.48/1.99      | sK3 != k1_xboole_0 ),
% 11.48/1.99      inference(resolution_lifted,[status(thm)],[c_6,c_18]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_330,plain,
% 11.48/1.99      ( ~ r1_partfun1(sK5,sK1(k1_xboole_0,sK4,X0))
% 11.48/1.99      | ~ r1_partfun1(sK6,sK1(k1_xboole_0,sK4,X0))
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
% 11.48/1.99      | ~ m1_subset_1(sK1(k1_xboole_0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | ~ v1_funct_1(sK1(k1_xboole_0,sK4,X0))
% 11.48/1.99      | sK3 != k1_xboole_0 ),
% 11.48/1.99      inference(unflattening,[status(thm)],[c_329]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_348,plain,
% 11.48/1.99      ( ~ r1_partfun1(sK5,sK1(k1_xboole_0,sK4,X0))
% 11.48/1.99      | ~ r1_partfun1(sK6,sK1(k1_xboole_0,sK4,X0))
% 11.48/1.99      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4)))
% 11.48/1.99      | ~ m1_subset_1(sK1(k1_xboole_0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4)))
% 11.48/1.99      | ~ v1_funct_1(X0)
% 11.48/1.99      | sK3 != k1_xboole_0 ),
% 11.48/1.99      inference(forward_subsumption_resolution,[status(thm)],[c_330,c_8]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_1587,plain,
% 11.48/1.99      ( sK3 != k1_xboole_0
% 11.48/1.99      | r1_partfun1(sK5,sK1(k1_xboole_0,sK4,X0)) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK1(k1_xboole_0,sK4,X0)) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK4))) != iProver_top
% 11.48/1.99      | m1_subset_1(sK1(k1_xboole_0,sK4,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,sK4))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_348]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_38561,plain,
% 11.48/1.99      ( sK3 != k1_xboole_0
% 11.48/1.99      | r1_partfun1(sK5,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | m1_subset_1(sK1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(sK3,k1_xboole_0))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(demodulation,[status(thm)],[c_38361,c_1587]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_38575,plain,
% 11.48/1.99      ( k1_xboole_0 != k1_xboole_0
% 11.48/1.99      | r1_partfun1(sK5,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | m1_subset_1(sK1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(light_normalisation,[status(thm)],[c_38561,c_38566]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_38576,plain,
% 11.48/1.99      ( r1_partfun1(sK5,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | m1_subset_1(sK1(k1_xboole_0,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(equality_resolution_simp,[status(thm)],[c_38575]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_40769,plain,
% 11.48/1.99      ( r1_partfun1(sK5,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK1(k1_xboole_0,k1_xboole_0,X0)) != iProver_top
% 11.48/1.99      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | v1_funct_1(X0) != iProver_top ),
% 11.48/1.99      inference(forward_subsumption_resolution,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_38576,c_1606]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_41913,plain,
% 11.48/1.99      ( r1_partfun1(sK5,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK1(k1_xboole_0,k1_xboole_0,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | m1_subset_1(sK2(sK6,sK5,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 11.48/1.99      inference(superposition,[status(thm)],[c_41470,c_40769]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_41918,plain,
% 11.48/1.99      ( r1_partfun1(sK5,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) != iProver_top
% 11.48/1.99      | m1_subset_1(sK2(sK6,sK5,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) != iProver_top ),
% 11.48/1.99      inference(light_normalisation,[status(thm)],[c_41913,c_41470]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6322,plain,
% 11.48/1.99      ( ~ sP0(sK6,sK5,k1_xboole_0,X0)
% 11.48/1.99      | m1_subset_1(sK2(sK6,sK5,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_14]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6343,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,X0) != iProver_top
% 11.48/1.99      | m1_subset_1(sK2(sK6,sK5,k1_xboole_0,X0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0))) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_6322]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6345,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) != iProver_top
% 11.48/1.99      | m1_subset_1(sK2(sK6,sK5,k1_xboole_0,k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) = iProver_top ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_6343]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6324,plain,
% 11.48/1.99      ( ~ sP0(sK6,sK5,k1_xboole_0,X0)
% 11.48/1.99      | r1_partfun1(sK5,sK2(sK6,sK5,k1_xboole_0,X0)) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_12]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6335,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,X0) != iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK2(sK6,sK5,k1_xboole_0,X0)) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_6324]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6337,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) != iProver_top
% 11.48/1.99      | r1_partfun1(sK5,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_6335]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6325,plain,
% 11.48/1.99      ( ~ sP0(sK6,sK5,k1_xboole_0,X0)
% 11.48/1.99      | r1_partfun1(sK6,sK2(sK6,sK5,k1_xboole_0,X0)) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_11]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6331,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,X0) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK2(sK6,sK5,k1_xboole_0,X0)) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_6325]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6333,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) != iProver_top
% 11.48/1.99      | r1_partfun1(sK6,sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_6331]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6326,plain,
% 11.48/1.99      ( ~ sP0(sK6,sK5,k1_xboole_0,X0)
% 11.48/1.99      | v1_funct_1(sK2(sK6,sK5,k1_xboole_0,X0)) ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_15]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6327,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,X0) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK6,sK5,k1_xboole_0,X0)) = iProver_top ),
% 11.48/1.99      inference(predicate_to_equality,[status(thm)],[c_6326]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(c_6329,plain,
% 11.48/1.99      ( sP0(sK6,sK5,k1_xboole_0,k1_xboole_0) != iProver_top
% 11.48/1.99      | v1_funct_1(sK2(sK6,sK5,k1_xboole_0,k1_xboole_0)) = iProver_top ),
% 11.48/1.99      inference(instantiation,[status(thm)],[c_6327]) ).
% 11.48/1.99  
% 11.48/1.99  cnf(contradiction,plain,
% 11.48/1.99      ( $false ),
% 11.48/1.99      inference(minisat,
% 11.48/1.99                [status(thm)],
% 11.48/1.99                [c_41918,c_38361,c_6345,c_6337,c_6333,c_6329,c_5130,
% 11.48/1.99                 c_5123,c_3737,c_3736,c_2178,c_2098,c_2077,c_1875,c_1188,
% 11.48/1.99                 c_29,c_20,c_28,c_27,c_26,c_25]) ).
% 11.48/1.99  
% 11.48/1.99  
% 11.48/1.99  % SZS output end CNFRefutation for theBenchmark.p
% 11.48/1.99  
% 11.48/1.99  ------                               Statistics
% 11.48/1.99  
% 11.48/1.99  ------ General
% 11.48/1.99  
% 11.48/1.99  abstr_ref_over_cycles:                  0
% 11.48/1.99  abstr_ref_under_cycles:                 0
% 11.48/1.99  gc_basic_clause_elim:                   0
% 11.48/1.99  forced_gc_time:                         0
% 11.48/1.99  parsing_time:                           0.01
% 11.48/1.99  unif_index_cands_time:                  0.
% 11.48/1.99  unif_index_add_time:                    0.
% 11.48/1.99  orderings_time:                         0.
% 11.48/1.99  out_proof_time:                         0.028
% 11.48/1.99  total_time:                             1.435
% 11.48/1.99  num_of_symbols:                         46
% 11.48/1.99  num_of_terms:                           41338
% 11.48/1.99  
% 11.48/1.99  ------ Preprocessing
% 11.48/1.99  
% 11.48/1.99  num_of_splits:                          0
% 11.48/1.99  num_of_split_atoms:                     0
% 11.48/1.99  num_of_reused_defs:                     0
% 11.48/1.99  num_eq_ax_congr_red:                    25
% 11.48/1.99  num_of_sem_filtered_clauses:            1
% 11.48/1.99  num_of_subtypes:                        0
% 11.48/1.99  monotx_restored_types:                  0
% 11.48/1.99  sat_num_of_epr_types:                   0
% 11.48/1.99  sat_num_of_non_cyclic_types:            0
% 11.48/1.99  sat_guarded_non_collapsed_types:        0
% 11.48/1.99  num_pure_diseq_elim:                    0
% 11.48/1.99  simp_replaced_by:                       0
% 11.48/1.99  res_preprocessed:                       118
% 11.48/1.99  prep_upred:                             0
% 11.48/1.99  prep_unflattend:                        56
% 11.48/1.99  smt_new_axioms:                         0
% 11.48/1.99  pred_elim_cands:                        5
% 11.48/1.99  pred_elim:                              1
% 11.48/1.99  pred_elim_cl:                           1
% 11.48/1.99  pred_elim_cycles:                       3
% 11.48/1.99  merged_defs:                            0
% 11.48/1.99  merged_defs_ncl:                        0
% 11.48/1.99  bin_hyper_res:                          0
% 11.48/1.99  prep_cycles:                            4
% 11.48/1.99  pred_elim_time:                         0.015
% 11.48/1.99  splitting_time:                         0.
% 11.48/1.99  sem_filter_time:                        0.
% 11.48/1.99  monotx_time:                            0.
% 11.48/1.99  subtype_inf_time:                       0.
% 11.48/1.99  
% 11.48/1.99  ------ Problem properties
% 11.48/1.99  
% 11.48/1.99  clauses:                                24
% 11.48/1.99  conjectures:                            6
% 11.48/1.99  epr:                                    4
% 11.48/1.99  horn:                                   19
% 11.48/1.99  ground:                                 6
% 11.48/1.99  unary:                                  5
% 11.48/1.99  binary:                                 6
% 11.48/1.99  lits:                                   77
% 11.48/1.99  lits_eq:                                10
% 11.48/1.99  fd_pure:                                0
% 11.48/1.99  fd_pseudo:                              0
% 11.48/1.99  fd_cond:                                5
% 11.48/1.99  fd_pseudo_cond:                         1
% 11.48/1.99  ac_symbols:                             0
% 11.48/1.99  
% 11.48/1.99  ------ Propositional Solver
% 11.48/1.99  
% 11.48/1.99  prop_solver_calls:                      35
% 11.48/1.99  prop_fast_solver_calls:                 4070
% 11.48/1.99  smt_solver_calls:                       0
% 11.48/1.99  smt_fast_solver_calls:                  0
% 11.48/1.99  prop_num_of_clauses:                    15636
% 11.48/1.99  prop_preprocess_simplified:             22646
% 11.48/1.99  prop_fo_subsumed:                       503
% 11.48/1.99  prop_solver_time:                       0.
% 11.48/1.99  smt_solver_time:                        0.
% 11.48/1.99  smt_fast_solver_time:                   0.
% 11.48/1.99  prop_fast_solver_time:                  0.
% 11.48/1.99  prop_unsat_core_time:                   0.001
% 11.48/1.99  
% 11.48/1.99  ------ QBF
% 11.48/1.99  
% 11.48/1.99  qbf_q_res:                              0
% 11.48/1.99  qbf_num_tautologies:                    0
% 11.48/1.99  qbf_prep_cycles:                        0
% 11.48/1.99  
% 11.48/1.99  ------ BMC1
% 11.48/1.99  
% 11.48/1.99  bmc1_current_bound:                     -1
% 11.48/1.99  bmc1_last_solved_bound:                 -1
% 11.48/1.99  bmc1_unsat_core_size:                   -1
% 11.48/1.99  bmc1_unsat_core_parents_size:           -1
% 11.48/1.99  bmc1_merge_next_fun:                    0
% 11.48/1.99  bmc1_unsat_core_clauses_time:           0.
% 11.48/1.99  
% 11.48/1.99  ------ Instantiation
% 11.48/1.99  
% 11.48/1.99  inst_num_of_clauses:                    3436
% 11.48/1.99  inst_num_in_passive:                    1001
% 11.48/1.99  inst_num_in_active:                     1919
% 11.48/1.99  inst_num_in_unprocessed:                517
% 11.48/1.99  inst_num_of_loops:                      2300
% 11.48/1.99  inst_num_of_learning_restarts:          0
% 11.48/1.99  inst_num_moves_active_passive:          370
% 11.48/1.99  inst_lit_activity:                      0
% 11.48/1.99  inst_lit_activity_moves:                2
% 11.48/1.99  inst_num_tautologies:                   0
% 11.48/1.99  inst_num_prop_implied:                  0
% 11.48/1.99  inst_num_existing_simplified:           0
% 11.48/1.99  inst_num_eq_res_simplified:             0
% 11.48/1.99  inst_num_child_elim:                    0
% 11.48/1.99  inst_num_of_dismatching_blockings:      763
% 11.48/1.99  inst_num_of_non_proper_insts:           2735
% 11.48/1.99  inst_num_of_duplicates:                 0
% 11.48/1.99  inst_inst_num_from_inst_to_res:         0
% 11.48/1.99  inst_dismatching_checking_time:         0.
% 11.48/1.99  
% 11.48/1.99  ------ Resolution
% 11.48/1.99  
% 11.48/1.99  res_num_of_clauses:                     0
% 11.48/1.99  res_num_in_passive:                     0
% 11.48/1.99  res_num_in_active:                      0
% 11.48/1.99  res_num_of_loops:                       122
% 11.48/1.99  res_forward_subset_subsumed:            56
% 11.48/1.99  res_backward_subset_subsumed:           10
% 11.48/1.99  res_forward_subsumed:                   2
% 11.48/1.99  res_backward_subsumed:                  0
% 11.48/1.99  res_forward_subsumption_resolution:     3
% 11.48/1.99  res_backward_subsumption_resolution:    0
% 11.48/1.99  res_clause_to_clause_subsumption:       7375
% 11.48/1.99  res_orphan_elimination:                 0
% 11.48/1.99  res_tautology_del:                      148
% 11.48/1.99  res_num_eq_res_simplified:              0
% 11.48/1.99  res_num_sel_changes:                    0
% 11.48/1.99  res_moves_from_active_to_pass:          0
% 11.48/1.99  
% 11.48/1.99  ------ Superposition
% 11.48/1.99  
% 11.48/1.99  sup_time_total:                         0.
% 11.48/1.99  sup_time_generating:                    0.
% 11.48/1.99  sup_time_sim_full:                      0.
% 11.48/1.99  sup_time_sim_immed:                     0.
% 11.48/1.99  
% 11.48/1.99  sup_num_of_clauses:                     722
% 11.48/1.99  sup_num_in_active:                      112
% 11.48/1.99  sup_num_in_passive:                     610
% 11.48/1.99  sup_num_of_loops:                       458
% 11.48/1.99  sup_fw_superposition:                   726
% 11.48/1.99  sup_bw_superposition:                   1233
% 11.48/1.99  sup_immediate_simplified:               405
% 11.48/1.99  sup_given_eliminated:                   0
% 11.48/1.99  comparisons_done:                       0
% 11.48/1.99  comparisons_avoided:                    475
% 11.48/1.99  
% 11.48/1.99  ------ Simplifications
% 11.48/1.99  
% 11.48/1.99  
% 11.48/1.99  sim_fw_subset_subsumed:                 91
% 11.48/1.99  sim_bw_subset_subsumed:                 355
% 11.48/1.99  sim_fw_subsumed:                        220
% 11.48/1.99  sim_bw_subsumed:                        23
% 11.48/1.99  sim_fw_subsumption_res:                 98
% 11.48/1.99  sim_bw_subsumption_res:                 26
% 11.48/1.99  sim_tautology_del:                      33
% 11.48/1.99  sim_eq_tautology_del:                   245
% 11.48/1.99  sim_eq_res_simp:                        2
% 11.48/1.99  sim_fw_demodulated:                     3
% 11.48/1.99  sim_bw_demodulated:                     204
% 11.48/1.99  sim_light_normalised:                   29
% 11.48/1.99  sim_joinable_taut:                      0
% 11.48/1.99  sim_joinable_simp:                      0
% 11.48/1.99  sim_ac_normalised:                      0
% 11.48/1.99  sim_smt_subsumption:                    0
% 11.48/1.99  
%------------------------------------------------------------------------------
