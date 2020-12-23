%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT1042+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n028.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:44:45 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 434 expanded)
%              Number of clauses        :   40 ( 114 expanded)
%              Number of leaves         :   10 ( 124 expanded)
%              Depth                    :   13
%              Number of atoms          :  383 (2945 expanded)
%              Number of equality atoms :   99 ( 459 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal clause size      :   26 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
         => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f4,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
           => ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) ) ) ) ),
    inference(negated_conjecture,[],[f3])).

fof(f9,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f10,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f9])).

fof(f23,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            | ~ v1_funct_2(X3,X0,X1)
            | ~ v1_funct_1(X3) )
          & r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
     => ( ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          | ~ v1_funct_2(sK8,X0,X1)
          | ~ v1_funct_1(sK8) )
        & r2_hidden(sK8,k5_partfun1(X0,X1,X2)) ) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              | ~ v1_funct_2(X3,X0,X1)
              | ~ v1_funct_1(X3) )
            & r2_hidden(X3,k5_partfun1(X0,X1,X2)) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
            | ~ v1_funct_2(X3,sK5,sK6)
            | ~ v1_funct_1(X3) )
          & r2_hidden(X3,k5_partfun1(sK5,sK6,sK7)) )
      & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      & v1_funct_1(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
      | ~ v1_funct_2(sK8,sK5,sK6)
      | ~ v1_funct_1(sK8) )
    & r2_hidden(sK8,k5_partfun1(sK5,sK6,sK7))
    & m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    & v1_funct_1(sK7) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK5,sK6,sK7,sK8])],[f10,f23,f22])).

fof(f44,plain,(
    r2_hidden(sK8,k5_partfun1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f24])).

fof(f12,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f14,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f12])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f14])).

fof(f27,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f27])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f7,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f8,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> ! [X4] :
              ( r2_hidden(X4,X3)
            <=> ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f7])).

fof(f11,plain,(
    ! [X2,X0,X1,X3] :
      ( sP0(X2,X0,X1,X3)
    <=> ! [X4] :
          ( r2_hidden(X4,X3)
        <=> ? [X5] :
              ( r1_partfun1(X2,X5)
              & v1_partfun1(X5,X0)
              & X4 = X5
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_1(X5) ) ) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f13,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f8,f12,f11])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f16,plain,(
    ! [X2,X0,X1,X3] :
      ( ( sP0(X2,X0,X1,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X4] :
            ( ( r2_hidden(X4,X3)
              | ! [X5] :
                  ( ~ r1_partfun1(X2,X5)
                  | ~ v1_partfun1(X5,X0)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  | ~ v1_funct_1(X5) ) )
            & ( ? [X5] :
                  ( r1_partfun1(X2,X5)
                  & v1_partfun1(X5,X0)
                  & X4 = X5
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) ) )
        | ~ sP0(X2,X0,X1,X3) ) ) ),
    inference(nnf_transformation,[],[f11])).

fof(f17,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ? [X4] :
            ( ( ! [X5] :
                  ( ~ r1_partfun1(X0,X5)
                  | ~ v1_partfun1(X5,X1)
                  | X4 != X5
                  | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X5) )
              | ~ r2_hidden(X4,X3) )
            & ( ? [X6] :
                  ( r1_partfun1(X0,X6)
                  & v1_partfun1(X6,X1)
                  & X4 = X6
                  & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X6) )
              | r2_hidden(X4,X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ? [X9] :
                  ( r1_partfun1(X0,X9)
                  & v1_partfun1(X9,X1)
                  & X7 = X9
                  & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_1(X9) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(rectify,[],[f16])).

fof(f20,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK4(X0,X1,X2,X7))
        & v1_partfun1(sK4(X0,X1,X2,X7),X1)
        & sK4(X0,X1,X2,X7) = X7
        & m1_subset_1(sK4(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK4(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f19,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & X4 = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK3(X0,X1,X2,X3))
        & v1_partfun1(sK3(X0,X1,X2,X3),X1)
        & sK3(X0,X1,X2,X3) = X4
        & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK3(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ! [X3,X2,X1,X0] :
      ( ? [X4] :
          ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | X4 != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(X4,X3) )
          & ( ? [X6] :
                ( r1_partfun1(X0,X6)
                & v1_partfun1(X6,X1)
                & X4 = X6
                & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(X6) )
            | r2_hidden(X4,X3) ) )
     => ( ( ! [X5] :
              ( ~ r1_partfun1(X0,X5)
              | ~ v1_partfun1(X5,X1)
              | sK2(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK2(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK2(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK2(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK3(X0,X1,X2,X3))
              & v1_partfun1(sK3(X0,X1,X2,X3),X1)
              & sK2(X0,X1,X2,X3) = sK3(X0,X1,X2,X3)
              & m1_subset_1(sK3(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK3(X0,X1,X2,X3)) )
            | r2_hidden(sK2(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK4(X0,X1,X2,X7))
                & v1_partfun1(sK4(X0,X1,X2,X7),X1)
                & sK4(X0,X1,X2,X7) = X7
                & m1_subset_1(sK4(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK4(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4])],[f17,f20,f19,f18])).

fof(f31,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( sK4(X0,X1,X2,X7) = X7
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f42,plain,(
    v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f24])).

fof(f43,plain,(
    m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f24])).

fof(f32,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_partfun1(sK4(X0,X1,X2,X7),X1)
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f30,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( m1_subset_1(sK4(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f29,plain,(
    ! [X2,X0,X7,X3,X1] :
      ( v1_funct_1(sK4(X0,X1,X2,X7))
      | ~ r2_hidden(X7,X3)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v1_partfun1(X2,X0)
          & v1_funct_1(X2) )
       => ( v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f5,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f6,plain,(
    ! [X0,X1,X2] :
      ( ( v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f5])).

fof(f26,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(X2,X0,X1)
      | ~ v1_partfun1(X2,X0)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f45,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_2(sK8,sK5,sK6)
    | ~ v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f24])).

cnf(c_18,negated_conjecture,
    ( r2_hidden(sK8,k5_partfun1(sK5,sK6,sK7)) ),
    inference(cnf_transformation,[],[f44])).

cnf(c_7229,plain,
    ( r2_hidden(sK8,k5_partfun1(sK5,sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_3,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f46])).

cnf(c_16,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f41])).

cnf(c_247,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | X4 != X1
    | X3 != X0
    | X5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_3,c_16])).

cnf(c_248,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_247])).

cnf(c_7225,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) = iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_248])).

cnf(c_13,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | sK4(X0,X1,X2,X4) = X4 ),
    inference(cnf_transformation,[],[f31])).

cnf(c_7232,plain,
    ( sK4(X0,X1,X2,X3) = X3
    | sP0(X0,X1,X2,X4) != iProver_top
    | r2_hidden(X3,X4) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_13])).

cnf(c_7913,plain,
    ( sK4(X0,X1,X2,X3) = X3
    | r2_hidden(X3,k5_partfun1(X1,X2,X0)) != iProver_top
    | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_7225,c_7232])).

cnf(c_7968,plain,
    ( sK4(sK7,sK5,sK6,sK8) = sK8
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7229,c_7913])).

cnf(c_20,negated_conjecture,
    ( v1_funct_1(sK7) ),
    inference(cnf_transformation,[],[f42])).

cnf(c_19,negated_conjecture,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) ),
    inference(cnf_transformation,[],[f43])).

cnf(c_7416,plain,
    ( sP0(sK7,X0,X1,k5_partfun1(X0,X1,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_248])).

cnf(c_7504,plain,
    ( sP0(sK7,sK5,sK6,k5_partfun1(sK5,sK6,sK7))
    | ~ m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK7) ),
    inference(instantiation,[status(thm)],[c_7416])).

cnf(c_7425,plain,
    ( ~ sP0(X0,X1,X2,k5_partfun1(sK5,sK6,sK7))
    | ~ r2_hidden(sK8,k5_partfun1(sK5,sK6,sK7))
    | sK4(X0,X1,X2,sK8) = sK8 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_7551,plain,
    ( ~ sP0(sK7,sK5,sK6,k5_partfun1(sK5,sK6,sK7))
    | ~ r2_hidden(sK8,k5_partfun1(sK5,sK6,sK7))
    | sK4(sK7,sK5,sK6,sK8) = sK8 ),
    inference(instantiation,[status(thm)],[c_7425])).

cnf(c_8142,plain,
    ( sK4(sK7,sK5,sK6,sK8) = sK8 ),
    inference(global_propositional_subsumption,[status(thm)],[c_7968,c_20,c_19,c_18,c_7504,c_7551])).

cnf(c_12,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | v1_partfun1(sK4(X0,X1,X2,X4),X1) ),
    inference(cnf_transformation,[],[f32])).

cnf(c_7233,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r2_hidden(X4,X3) != iProver_top
    | v1_partfun1(sK4(X0,X1,X2,X4),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_12])).

cnf(c_7911,plain,
    ( r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_partfun1(sK4(X3,X1,X2,X0),X1) = iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7225,c_7233])).

cnf(c_9213,plain,
    ( r2_hidden(sK8,k5_partfun1(sK5,sK6,sK7)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_partfun1(sK8,sK5) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8142,c_7911])).

cnf(c_14,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | m1_subset_1(sK4(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ),
    inference(cnf_transformation,[],[f30])).

cnf(c_7231,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r2_hidden(X4,X3) != iProver_top
    | m1_subset_1(sK4(X0,X1,X2,X4),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_14])).

cnf(c_7909,plain,
    ( r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | m1_subset_1(sK4(X3,X1,X2,X0),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) = iProver_top
    | v1_funct_1(X3) != iProver_top ),
    inference(superposition,[status(thm)],[c_7225,c_7231])).

cnf(c_9144,plain,
    ( r2_hidden(sK8,k5_partfun1(sK5,sK6,sK7)) != iProver_top
    | m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_8142,c_7909])).

cnf(c_15,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r2_hidden(X4,X3)
    | v1_funct_1(sK4(X0,X1,X2,X4)) ),
    inference(cnf_transformation,[],[f29])).

cnf(c_7230,plain,
    ( sP0(X0,X1,X2,X3) != iProver_top
    | r2_hidden(X4,X3) != iProver_top
    | v1_funct_1(sK4(X0,X1,X2,X4)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_15])).

cnf(c_7912,plain,
    ( r2_hidden(X0,k5_partfun1(X1,X2,X3)) != iProver_top
    | m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_funct_1(X3) != iProver_top
    | v1_funct_1(sK4(X3,X1,X2,X0)) = iProver_top ),
    inference(superposition,[status(thm)],[c_7225,c_7230])).

cnf(c_8153,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK4(sK7,sK5,sK6,sK8)) = iProver_top
    | v1_funct_1(sK7) != iProver_top ),
    inference(superposition,[status(thm)],[c_7229,c_7912])).

cnf(c_8157,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_funct_1(sK7) != iProver_top
    | v1_funct_1(sK8) = iProver_top ),
    inference(light_normalisation,[status(thm)],[c_8153,c_8142])).

cnf(c_0,plain,
    ( v1_funct_2(X0,X1,X2)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0) ),
    inference(cnf_transformation,[],[f26])).

cnf(c_17,negated_conjecture,
    ( ~ v1_funct_2(sK8,sK5,sK6)
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_funct_1(sK8) ),
    inference(cnf_transformation,[],[f45])).

cnf(c_230,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_partfun1(X0,X1)
    | ~ v1_funct_1(X0)
    | ~ v1_funct_1(sK8)
    | sK6 != X2
    | sK5 != X1
    | sK8 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_0,c_17])).

cnf(c_231,plain,
    ( ~ m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6)))
    | ~ v1_partfun1(sK8,sK5)
    | ~ v1_funct_1(sK8) ),
    inference(unflattening,[status(thm)],[c_230])).

cnf(c_232,plain,
    ( m1_subset_1(sK8,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) != iProver_top
    | v1_partfun1(sK8,sK5) != iProver_top
    | v1_funct_1(sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_231])).

cnf(c_23,plain,
    ( r2_hidden(sK8,k5_partfun1(sK5,sK6,sK7)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_22,plain,
    ( m1_subset_1(sK7,k1_zfmisc_1(k2_zfmisc_1(sK5,sK6))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_19])).

cnf(c_21,plain,
    ( v1_funct_1(sK7) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_20])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_9213,c_9144,c_8157,c_232,c_23,c_22,c_21])).


%------------------------------------------------------------------------------
