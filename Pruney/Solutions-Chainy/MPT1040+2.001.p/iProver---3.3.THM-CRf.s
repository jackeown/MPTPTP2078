%------------------------------------------------------------------------------
% File       : iProver---3.3
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : iproveropt_run.sh %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:08:44 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :  140 ( 231 expanded)
%              Number of clauses        :   65 (  70 expanded)
%              Number of leaves         :   26 (  62 expanded)
%              Depth                    :   15
%              Number of atoms          :  565 (1438 expanded)
%              Number of equality atoms :  122 ( 322 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal clause size      :   26 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f4])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f63,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK4(X0,X1),X1)
        & r2_hidden(sK4(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK4(X0,X1),X1)
          & r2_hidden(sK4(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f63])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | ~ r2_hidden(X2,X1)
      | ~ r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f50,plain,(
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

fof(f77,plain,(
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
    inference(nnf_transformation,[],[f50])).

fof(f78,plain,(
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
    inference(rectify,[],[f77])).

fof(f81,plain,(
    ! [X7,X2,X1,X0] :
      ( ? [X9] :
          ( r1_partfun1(X0,X9)
          & v1_partfun1(X9,X1)
          & X7 = X9
          & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X9) )
     => ( r1_partfun1(X0,sK12(X0,X1,X2,X7))
        & v1_partfun1(sK12(X0,X1,X2,X7),X1)
        & sK12(X0,X1,X2,X7) = X7
        & m1_subset_1(sK12(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK12(X0,X1,X2,X7)) ) ) ),
    introduced(choice_axiom,[])).

fof(f80,plain,(
    ! [X4,X3,X2,X1,X0] :
      ( ? [X6] :
          ( r1_partfun1(X0,X6)
          & v1_partfun1(X6,X1)
          & X4 = X6
          & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_1(X6) )
     => ( r1_partfun1(X0,sK11(X0,X1,X2,X3))
        & v1_partfun1(sK11(X0,X1,X2,X3),X1)
        & sK11(X0,X1,X2,X3) = X4
        & m1_subset_1(sK11(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
        & v1_funct_1(sK11(X0,X1,X2,X3)) ) ) ),
    introduced(choice_axiom,[])).

fof(f79,plain,(
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
              | sK10(X0,X1,X2,X3) != X5
              | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              | ~ v1_funct_1(X5) )
          | ~ r2_hidden(sK10(X0,X1,X2,X3),X3) )
        & ( ? [X6] :
              ( r1_partfun1(X0,X6)
              & v1_partfun1(X6,X1)
              & sK10(X0,X1,X2,X3) = X6
              & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(X6) )
          | r2_hidden(sK10(X0,X1,X2,X3),X3) ) ) ) ),
    introduced(choice_axiom,[])).

fof(f82,plain,(
    ! [X0,X1,X2,X3] :
      ( ( sP0(X0,X1,X2,X3)
        | ( ( ! [X5] :
                ( ~ r1_partfun1(X0,X5)
                | ~ v1_partfun1(X5,X1)
                | sK10(X0,X1,X2,X3) != X5
                | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                | ~ v1_funct_1(X5) )
            | ~ r2_hidden(sK10(X0,X1,X2,X3),X3) )
          & ( ( r1_partfun1(X0,sK11(X0,X1,X2,X3))
              & v1_partfun1(sK11(X0,X1,X2,X3),X1)
              & sK10(X0,X1,X2,X3) = sK11(X0,X1,X2,X3)
              & m1_subset_1(sK11(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_1(sK11(X0,X1,X2,X3)) )
            | r2_hidden(sK10(X0,X1,X2,X3),X3) ) ) )
      & ( ! [X7] :
            ( ( r2_hidden(X7,X3)
              | ! [X8] :
                  ( ~ r1_partfun1(X0,X8)
                  | ~ v1_partfun1(X8,X1)
                  | X7 != X8
                  | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  | ~ v1_funct_1(X8) ) )
            & ( ( r1_partfun1(X0,sK12(X0,X1,X2,X7))
                & v1_partfun1(sK12(X0,X1,X2,X7),X1)
                & sK12(X0,X1,X2,X7) = X7
                & m1_subset_1(sK12(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                & v1_funct_1(sK12(X0,X1,X2,X7)) )
              | ~ r2_hidden(X7,X3) ) )
        | ~ sP0(X0,X1,X2,X3) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f78,f81,f80,f79])).

fof(f135,plain,(
    ! [X2,X0,X8,X7,X3,X1] :
      ( r2_hidden(X7,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | X7 != X8
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f82])).

fof(f161,plain,(
    ! [X2,X0,X8,X3,X1] :
      ( r2_hidden(X8,X3)
      | ~ r1_partfun1(X0,X8)
      | ~ v1_partfun1(X8,X1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X8)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(equality_resolution,[],[f135])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f27,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f99,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f23,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
         => ( r1_partfun1(X2,X3)
           => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
              | ( k1_xboole_0 != X0
                & k1_xboole_0 = X1 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f24,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
           => ( r1_partfun1(X2,X3)
             => ( r2_hidden(X3,k5_partfun1(X0,X1,X2))
                | ( k1_xboole_0 != X0
                  & k1_xboole_0 = X1 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f23])).

fof(f48,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f49,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
          & ( k1_xboole_0 = X0
            | k1_xboole_0 != X1 )
          & r1_partfun1(X2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
     => ( ~ r2_hidden(sK16,k5_partfun1(X0,X1,X2))
        & ( k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & r1_partfun1(X2,sK16)
        & m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(sK16,X0,X1)
        & v1_funct_1(sK16) ) ) ),
    introduced(choice_axiom,[])).

fof(f83,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ~ r2_hidden(X3,k5_partfun1(X0,X1,X2))
            & ( k1_xboole_0 = X0
              | k1_xboole_0 != X1 )
            & r1_partfun1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
            & v1_funct_2(X3,X0,X1)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ~ r2_hidden(X3,k5_partfun1(sK13,sK14,sK15))
          & ( k1_xboole_0 = sK13
            | k1_xboole_0 != sK14 )
          & r1_partfun1(sK15,X3)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
          & v1_funct_2(X3,sK13,sK14)
          & v1_funct_1(X3) )
      & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
      & v1_funct_1(sK15) ) ),
    introduced(choice_axiom,[])).

fof(f85,plain,
    ( ~ r2_hidden(sK16,k5_partfun1(sK13,sK14,sK15))
    & ( k1_xboole_0 = sK13
      | k1_xboole_0 != sK14 )
    & r1_partfun1(sK15,sK16)
    & m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    & v1_funct_2(sK16,sK13,sK14)
    & v1_funct_1(sK16)
    & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    & v1_funct_1(sK15) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15,sK16])],[f49,f84,f83])).

fof(f147,plain,(
    m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) ),
    inference(cnf_transformation,[],[f85])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f109,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f32,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f104,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k7_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f31,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f103,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k7_relat_1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f33,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f108,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0))
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f10,axiom,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f105,plain,(
    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f10])).

fof(f11,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f106,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f11])).

fof(f51,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( k5_partfun1(X0,X1,X2) = X3
        <=> sP0(X2,X0,X1,X3) )
      | ~ sP1(X1,X0,X2) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f75,plain,(
    ! [X1,X0,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X0,X1,X2) = X3
            | ~ sP0(X2,X0,X1,X3) )
          & ( sP0(X2,X0,X1,X3)
            | k5_partfun1(X0,X1,X2) != X3 ) )
      | ~ sP1(X1,X0,X2) ) ),
    inference(nnf_transformation,[],[f51])).

fof(f76,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k5_partfun1(X1,X0,X2) = X3
            | ~ sP0(X2,X1,X0,X3) )
          & ( sP0(X2,X1,X0,X3)
            | k5_partfun1(X1,X0,X2) != X3 ) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f75])).

fof(f128,plain,(
    ! [X2,X0,X3,X1] :
      ( sP0(X2,X1,X0,X3)
      | k5_partfun1(X1,X0,X2) != X3
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f76])).

fof(f159,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0,k5_partfun1(X1,X0,X2))
      | ~ sP1(X0,X1,X2) ) ),
    inference(equality_resolution,[],[f128])).

fof(f22,axiom,(
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

fof(f46,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f47,plain,(
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
    inference(flattening,[],[f46])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(definition_folding,[],[f47,f51,f50])).

fof(f142,plain,(
    ! [X2,X0,X1] :
      ( sP1(X1,X0,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f19,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => v1_partfun1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( v1_partfun1(X2,X0)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f119,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f20,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f42])).

fof(f121,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f146,plain,(
    v1_funct_2(sK16,sK13,sK14) ),
    inference(cnf_transformation,[],[f85])).

fof(f145,plain,(
    v1_funct_1(sK16) ),
    inference(cnf_transformation,[],[f85])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f53,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f54,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f53])).

fof(f55,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK2(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f56,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK2(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).

fof(f87,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f62,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f95,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f62])).

fof(f150,plain,(
    ~ r2_hidden(sK16,k5_partfun1(sK13,sK14,sK15)) ),
    inference(cnf_transformation,[],[f85])).

fof(f149,plain,
    ( k1_xboole_0 = sK13
    | k1_xboole_0 != sK14 ),
    inference(cnf_transformation,[],[f85])).

fof(f148,plain,(
    r1_partfun1(sK15,sK16) ),
    inference(cnf_transformation,[],[f85])).

fof(f144,plain,(
    m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) ),
    inference(cnf_transformation,[],[f85])).

fof(f143,plain,(
    v1_funct_1(sK15) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_10,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(X2,X0)
    | ~ r2_hidden(X2,X1) ),
    inference(cnf_transformation,[],[f98])).

cnf(c_13522,plain,
    ( ~ r1_xboole_0(X0,X1)
    | ~ r2_hidden(sK2(X0),X0)
    | ~ r2_hidden(sK2(X0),X1) ),
    inference(instantiation,[status(thm)],[c_10])).

cnf(c_13524,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_13522])).

cnf(c_50,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_partfun1(X0,X4)
    | ~ v1_partfun1(X4,X1)
    | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(X4,X3)
    | ~ v1_funct_1(X4) ),
    inference(cnf_transformation,[],[f161])).

cnf(c_8894,plain,
    ( ~ sP0(X0,X1,X2,X3)
    | ~ r1_partfun1(X0,sK16)
    | ~ v1_partfun1(sK16,X1)
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | r2_hidden(sK16,X3)
    | ~ v1_funct_1(sK16) ),
    inference(instantiation,[status(thm)],[c_50])).

cnf(c_9297,plain,
    ( ~ sP0(sK15,X0,X1,X2)
    | ~ r1_partfun1(sK15,sK16)
    | ~ v1_partfun1(sK16,X0)
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | r2_hidden(sK16,X2)
    | ~ v1_funct_1(sK16) ),
    inference(instantiation,[status(thm)],[c_8894])).

cnf(c_10214,plain,
    ( ~ sP0(sK15,sK13,X0,X1)
    | ~ r1_partfun1(sK15,sK16)
    | ~ v1_partfun1(sK16,sK13)
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,X0)))
    | r2_hidden(sK16,X1)
    | ~ v1_funct_1(sK16) ),
    inference(instantiation,[status(thm)],[c_9297])).

cnf(c_11283,plain,
    ( ~ sP0(sK15,sK13,sK14,X0)
    | ~ r1_partfun1(sK15,sK16)
    | ~ v1_partfun1(sK16,sK13)
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    | r2_hidden(sK16,X0)
    | ~ v1_funct_1(sK16) ),
    inference(instantiation,[status(thm)],[c_10214])).

cnf(c_12892,plain,
    ( ~ sP0(sK15,sK13,sK14,k5_partfun1(sK13,sK14,sK15))
    | ~ r1_partfun1(sK15,sK16)
    | ~ v1_partfun1(sK16,sK13)
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    | r2_hidden(sK16,k5_partfun1(sK13,sK14,sK15))
    | ~ v1_funct_1(sK16) ),
    inference(instantiation,[status(thm)],[c_11283])).

cnf(c_13,plain,
    ( ~ v1_xboole_0(X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_10350,plain,
    ( ~ v1_xboole_0(sK14)
    | k1_xboole_0 = sK14 ),
    inference(instantiation,[status(thm)],[c_13])).

cnf(c_60,negated_conjecture,
    ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) ),
    inference(cnf_transformation,[],[f147])).

cnf(c_8285,plain,
    ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | v1_relat_1(X0) ),
    inference(cnf_transformation,[],[f109])).

cnf(c_8310,plain,
    ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
    | v1_relat_1(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_9525,plain,
    ( v1_relat_1(sK16) = iProver_top ),
    inference(superposition,[status(thm)],[c_8285,c_8310])).

cnf(c_18,plain,
    ( ~ v1_relat_1(X0)
    | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f104])).

cnf(c_8312,plain,
    ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_18])).

cnf(c_9626,plain,
    ( k7_relat_1(sK16,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_9525,c_8312])).

cnf(c_17,plain,
    ( ~ v1_relat_1(X0)
    | v1_relat_1(k7_relat_1(X0,X1)) ),
    inference(cnf_transformation,[],[f103])).

cnf(c_8313,plain,
    ( v1_relat_1(X0) != iProver_top
    | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_17])).

cnf(c_9649,plain,
    ( v1_relat_1(sK16) != iProver_top
    | v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(superposition,[status(thm)],[c_9626,c_8313])).

cnf(c_69,plain,
    ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_60])).

cnf(c_8790,plain,
    ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    | v1_relat_1(sK16) ),
    inference(instantiation,[status(thm)],[c_23])).

cnf(c_8791,plain,
    ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) != iProver_top
    | v1_relat_1(sK16) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_8790])).

cnf(c_9754,plain,
    ( v1_relat_1(k1_xboole_0) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_9649,c_69,c_8791])).

cnf(c_22,plain,
    ( ~ v1_relat_1(X0)
    | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
    inference(cnf_transformation,[],[f108])).

cnf(c_8311,plain,
    ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
    | v1_relat_1(X0) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_22])).

cnf(c_10170,plain,
    ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(k1_relat_1(k1_xboole_0),X0) ),
    inference(superposition,[status(thm)],[c_9754,c_8311])).

cnf(c_19,plain,
    ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f105])).

cnf(c_21,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f106])).

cnf(c_10178,plain,
    ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
    inference(light_normalisation,[status(thm)],[c_10170,c_19,c_21])).

cnf(c_10189,plain,
    ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_10178])).

cnf(c_7014,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(X1)
    | X1 != X0 ),
    theory(equality)).

cnf(c_9614,plain,
    ( ~ v1_xboole_0(X0)
    | v1_xboole_0(sK13)
    | sK13 != X0 ),
    inference(instantiation,[status(thm)],[c_7014])).

cnf(c_9616,plain,
    ( v1_xboole_0(sK13)
    | ~ v1_xboole_0(k1_xboole_0)
    | sK13 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_9614])).

cnf(c_7012,plain,
    ( X0 = X0 ),
    theory(equality)).

cnf(c_9421,plain,
    ( sK13 = sK13 ),
    inference(instantiation,[status(thm)],[c_7012])).

cnf(c_7013,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_8820,plain,
    ( sK13 != X0
    | sK13 = k1_xboole_0
    | k1_xboole_0 != X0 ),
    inference(instantiation,[status(thm)],[c_7013])).

cnf(c_9420,plain,
    ( sK13 != sK13
    | sK13 = k1_xboole_0
    | k1_xboole_0 != sK13 ),
    inference(instantiation,[status(thm)],[c_8820])).

cnf(c_43,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ sP1(X2,X1,X0) ),
    inference(cnf_transformation,[],[f159])).

cnf(c_56,plain,
    ( sP1(X0,X1,X2)
    | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
    | ~ v1_funct_1(X2) ),
    inference(cnf_transformation,[],[f142])).

cnf(c_789,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
    | ~ v1_funct_1(X3)
    | X4 != X1
    | X3 != X0
    | X5 != X2 ),
    inference(resolution_lifted,[status(thm)],[c_43,c_56])).

cnf(c_790,plain,
    ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0) ),
    inference(unflattening,[status(thm)],[c_789])).

cnf(c_8867,plain,
    ( sP0(sK15,X0,X1,k5_partfun1(X0,X1,sK15))
    | ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | ~ v1_funct_1(sK15) ),
    inference(instantiation,[status(thm)],[c_790])).

cnf(c_9284,plain,
    ( sP0(sK15,sK13,sK14,k5_partfun1(sK13,sK14,sK15))
    | ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    | ~ v1_funct_1(sK15) ),
    inference(instantiation,[status(thm)],[c_8867])).

cnf(c_33,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f119])).

cnf(c_8814,plain,
    ( v1_partfun1(sK16,sK13)
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    | ~ v1_xboole_0(sK13) ),
    inference(instantiation,[status(thm)],[c_33])).

cnf(c_34,plain,
    ( ~ v1_funct_2(X0,X1,X2)
    | v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2) ),
    inference(cnf_transformation,[],[f121])).

cnf(c_61,negated_conjecture,
    ( v1_funct_2(sK16,sK13,sK14) ),
    inference(cnf_transformation,[],[f146])).

cnf(c_1471,plain,
    ( v1_partfun1(X0,X1)
    | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
    | ~ v1_funct_1(X0)
    | v1_xboole_0(X2)
    | sK14 != X2
    | sK13 != X1
    | sK16 != X0 ),
    inference(resolution_lifted,[status(thm)],[c_34,c_61])).

cnf(c_1472,plain,
    ( v1_partfun1(sK16,sK13)
    | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
    | ~ v1_funct_1(sK16)
    | v1_xboole_0(sK14) ),
    inference(unflattening,[status(thm)],[c_1471])).

cnf(c_62,negated_conjecture,
    ( v1_funct_1(sK16) ),
    inference(cnf_transformation,[],[f145])).

cnf(c_1474,plain,
    ( v1_partfun1(sK16,sK13)
    | v1_xboole_0(sK14) ),
    inference(global_propositional_subsumption,[status(thm)],[c_1472,c_62,c_60])).

cnf(c_0,plain,
    ( r2_hidden(sK2(X0),X0)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f87])).

cnf(c_219,plain,
    ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
    | v1_xboole_0(k1_xboole_0) ),
    inference(instantiation,[status(thm)],[c_0])).

cnf(c_8,plain,
    ( r1_xboole_0(X0,X1)
    | k3_xboole_0(X0,X1) != k1_xboole_0 ),
    inference(cnf_transformation,[],[f95])).

cnf(c_201,plain,
    ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
    | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_8])).

cnf(c_57,negated_conjecture,
    ( ~ r2_hidden(sK16,k5_partfun1(sK13,sK14,sK15)) ),
    inference(cnf_transformation,[],[f150])).

cnf(c_58,negated_conjecture,
    ( k1_xboole_0 != sK14
    | k1_xboole_0 = sK13 ),
    inference(cnf_transformation,[],[f149])).

cnf(c_59,negated_conjecture,
    ( r1_partfun1(sK15,sK16) ),
    inference(cnf_transformation,[],[f148])).

cnf(c_63,negated_conjecture,
    ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) ),
    inference(cnf_transformation,[],[f144])).

cnf(c_64,negated_conjecture,
    ( v1_funct_1(sK15) ),
    inference(cnf_transformation,[],[f143])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_13524,c_12892,c_10350,c_10189,c_9616,c_9421,c_9420,c_9284,c_8814,c_1474,c_219,c_201,c_57,c_58,c_59,c_60,c_62,c_63,c_64])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : iproveropt_run.sh %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 20:08:45 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  % Running in FOF mode
% 2.58/1.00  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 2.58/1.00  
% 2.58/1.00  ------  iProver source info
% 2.58/1.00  
% 2.58/1.00  git: date: 2020-06-30 10:37:57 +0100
% 2.58/1.00  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 2.58/1.00  git: non_committed_changes: false
% 2.58/1.00  git: last_make_outside_of_git: false
% 2.58/1.00  
% 2.58/1.00  ------ 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options
% 2.58/1.00  
% 2.58/1.00  --out_options                           all
% 2.58/1.00  --tptp_safe_out                         true
% 2.58/1.00  --problem_path                          ""
% 2.58/1.00  --include_path                          ""
% 2.58/1.00  --clausifier                            res/vclausify_rel
% 2.58/1.00  --clausifier_options                    --mode clausify
% 2.58/1.00  --stdin                                 false
% 2.58/1.00  --stats_out                             all
% 2.58/1.00  
% 2.58/1.00  ------ General Options
% 2.58/1.00  
% 2.58/1.00  --fof                                   false
% 2.58/1.00  --time_out_real                         305.
% 2.58/1.00  --time_out_virtual                      -1.
% 2.58/1.00  --symbol_type_check                     false
% 2.58/1.00  --clausify_out                          false
% 2.58/1.00  --sig_cnt_out                           false
% 2.58/1.00  --trig_cnt_out                          false
% 2.58/1.00  --trig_cnt_out_tolerance                1.
% 2.58/1.00  --trig_cnt_out_sk_spl                   false
% 2.58/1.00  --abstr_cl_out                          false
% 2.58/1.00  
% 2.58/1.00  ------ Global Options
% 2.58/1.00  
% 2.58/1.00  --schedule                              default
% 2.58/1.00  --add_important_lit                     false
% 2.58/1.00  --prop_solver_per_cl                    1000
% 2.58/1.00  --min_unsat_core                        false
% 2.58/1.00  --soft_assumptions                      false
% 2.58/1.00  --soft_lemma_size                       3
% 2.58/1.00  --prop_impl_unit_size                   0
% 2.58/1.00  --prop_impl_unit                        []
% 2.58/1.00  --share_sel_clauses                     true
% 2.58/1.00  --reset_solvers                         false
% 2.58/1.00  --bc_imp_inh                            [conj_cone]
% 2.58/1.00  --conj_cone_tolerance                   3.
% 2.58/1.00  --extra_neg_conj                        none
% 2.58/1.00  --large_theory_mode                     true
% 2.58/1.00  --prolific_symb_bound                   200
% 2.58/1.00  --lt_threshold                          2000
% 2.58/1.00  --clause_weak_htbl                      true
% 2.58/1.00  --gc_record_bc_elim                     false
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing Options
% 2.58/1.00  
% 2.58/1.00  --preprocessing_flag                    true
% 2.58/1.00  --time_out_prep_mult                    0.1
% 2.58/1.00  --splitting_mode                        input
% 2.58/1.00  --splitting_grd                         true
% 2.58/1.00  --splitting_cvd                         false
% 2.58/1.00  --splitting_cvd_svl                     false
% 2.58/1.00  --splitting_nvd                         32
% 2.58/1.00  --sub_typing                            true
% 2.58/1.00  --prep_gs_sim                           true
% 2.58/1.00  --prep_unflatten                        true
% 2.58/1.00  --prep_res_sim                          true
% 2.58/1.00  --prep_upred                            true
% 2.58/1.00  --prep_sem_filter                       exhaustive
% 2.58/1.00  --prep_sem_filter_out                   false
% 2.58/1.00  --pred_elim                             true
% 2.58/1.00  --res_sim_input                         true
% 2.58/1.00  --eq_ax_congr_red                       true
% 2.58/1.00  --pure_diseq_elim                       true
% 2.58/1.00  --brand_transform                       false
% 2.58/1.00  --non_eq_to_eq                          false
% 2.58/1.00  --prep_def_merge                        true
% 2.58/1.00  --prep_def_merge_prop_impl              false
% 2.58/1.00  --prep_def_merge_mbd                    true
% 2.58/1.00  --prep_def_merge_tr_red                 false
% 2.58/1.00  --prep_def_merge_tr_cl                  false
% 2.58/1.00  --smt_preprocessing                     true
% 2.58/1.00  --smt_ac_axioms                         fast
% 2.58/1.00  --preprocessed_out                      false
% 2.58/1.00  --preprocessed_stats                    false
% 2.58/1.00  
% 2.58/1.00  ------ Abstraction refinement Options
% 2.58/1.00  
% 2.58/1.00  --abstr_ref                             []
% 2.58/1.00  --abstr_ref_prep                        false
% 2.58/1.00  --abstr_ref_until_sat                   false
% 2.58/1.00  --abstr_ref_sig_restrict                funpre
% 2.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/1.00  --abstr_ref_under                       []
% 2.58/1.00  
% 2.58/1.00  ------ SAT Options
% 2.58/1.00  
% 2.58/1.00  --sat_mode                              false
% 2.58/1.00  --sat_fm_restart_options                ""
% 2.58/1.00  --sat_gr_def                            false
% 2.58/1.00  --sat_epr_types                         true
% 2.58/1.00  --sat_non_cyclic_types                  false
% 2.58/1.00  --sat_finite_models                     false
% 2.58/1.00  --sat_fm_lemmas                         false
% 2.58/1.00  --sat_fm_prep                           false
% 2.58/1.00  --sat_fm_uc_incr                        true
% 2.58/1.00  --sat_out_model                         small
% 2.58/1.00  --sat_out_clauses                       false
% 2.58/1.00  
% 2.58/1.00  ------ QBF Options
% 2.58/1.00  
% 2.58/1.00  --qbf_mode                              false
% 2.58/1.00  --qbf_elim_univ                         false
% 2.58/1.00  --qbf_dom_inst                          none
% 2.58/1.00  --qbf_dom_pre_inst                      false
% 2.58/1.00  --qbf_sk_in                             false
% 2.58/1.00  --qbf_pred_elim                         true
% 2.58/1.00  --qbf_split                             512
% 2.58/1.00  
% 2.58/1.00  ------ BMC1 Options
% 2.58/1.00  
% 2.58/1.00  --bmc1_incremental                      false
% 2.58/1.00  --bmc1_axioms                           reachable_all
% 2.58/1.00  --bmc1_min_bound                        0
% 2.58/1.00  --bmc1_max_bound                        -1
% 2.58/1.00  --bmc1_max_bound_default                -1
% 2.58/1.00  --bmc1_symbol_reachability              true
% 2.58/1.00  --bmc1_property_lemmas                  false
% 2.58/1.00  --bmc1_k_induction                      false
% 2.58/1.00  --bmc1_non_equiv_states                 false
% 2.58/1.00  --bmc1_deadlock                         false
% 2.58/1.00  --bmc1_ucm                              false
% 2.58/1.00  --bmc1_add_unsat_core                   none
% 2.58/1.00  --bmc1_unsat_core_children              false
% 2.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/1.00  --bmc1_out_stat                         full
% 2.58/1.00  --bmc1_ground_init                      false
% 2.58/1.00  --bmc1_pre_inst_next_state              false
% 2.58/1.00  --bmc1_pre_inst_state                   false
% 2.58/1.00  --bmc1_pre_inst_reach_state             false
% 2.58/1.00  --bmc1_out_unsat_core                   false
% 2.58/1.00  --bmc1_aig_witness_out                  false
% 2.58/1.00  --bmc1_verbose                          false
% 2.58/1.00  --bmc1_dump_clauses_tptp                false
% 2.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.58/1.00  --bmc1_dump_file                        -
% 2.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.58/1.00  --bmc1_ucm_extend_mode                  1
% 2.58/1.00  --bmc1_ucm_init_mode                    2
% 2.58/1.00  --bmc1_ucm_cone_mode                    none
% 2.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.58/1.00  --bmc1_ucm_relax_model                  4
% 2.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/1.00  --bmc1_ucm_layered_model                none
% 2.58/1.00  --bmc1_ucm_max_lemma_size               10
% 2.58/1.00  
% 2.58/1.00  ------ AIG Options
% 2.58/1.00  
% 2.58/1.00  --aig_mode                              false
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation Options
% 2.58/1.00  
% 2.58/1.00  --instantiation_flag                    true
% 2.58/1.00  --inst_sos_flag                         false
% 2.58/1.00  --inst_sos_phase                        true
% 2.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel_side                     num_symb
% 2.58/1.00  --inst_solver_per_active                1400
% 2.58/1.00  --inst_solver_calls_frac                1.
% 2.58/1.00  --inst_passive_queue_type               priority_queues
% 2.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/1.00  --inst_passive_queues_freq              [25;2]
% 2.58/1.00  --inst_dismatching                      true
% 2.58/1.00  --inst_eager_unprocessed_to_passive     true
% 2.58/1.00  --inst_prop_sim_given                   true
% 2.58/1.00  --inst_prop_sim_new                     false
% 2.58/1.00  --inst_subs_new                         false
% 2.58/1.00  --inst_eq_res_simp                      false
% 2.58/1.00  --inst_subs_given                       false
% 2.58/1.00  --inst_orphan_elimination               true
% 2.58/1.00  --inst_learning_loop_flag               true
% 2.58/1.00  --inst_learning_start                   3000
% 2.58/1.00  --inst_learning_factor                  2
% 2.58/1.00  --inst_start_prop_sim_after_learn       3
% 2.58/1.00  --inst_sel_renew                        solver
% 2.58/1.00  --inst_lit_activity_flag                true
% 2.58/1.00  --inst_restr_to_given                   false
% 2.58/1.00  --inst_activity_threshold               500
% 2.58/1.00  --inst_out_proof                        true
% 2.58/1.00  
% 2.58/1.00  ------ Resolution Options
% 2.58/1.00  
% 2.58/1.00  --resolution_flag                       true
% 2.58/1.00  --res_lit_sel                           adaptive
% 2.58/1.00  --res_lit_sel_side                      none
% 2.58/1.00  --res_ordering                          kbo
% 2.58/1.00  --res_to_prop_solver                    active
% 2.58/1.00  --res_prop_simpl_new                    false
% 2.58/1.00  --res_prop_simpl_given                  true
% 2.58/1.00  --res_passive_queue_type                priority_queues
% 2.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/1.00  --res_passive_queues_freq               [15;5]
% 2.58/1.00  --res_forward_subs                      full
% 2.58/1.00  --res_backward_subs                     full
% 2.58/1.00  --res_forward_subs_resolution           true
% 2.58/1.00  --res_backward_subs_resolution          true
% 2.58/1.00  --res_orphan_elimination                true
% 2.58/1.00  --res_time_limit                        2.
% 2.58/1.00  --res_out_proof                         true
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Options
% 2.58/1.00  
% 2.58/1.00  --superposition_flag                    true
% 2.58/1.00  --sup_passive_queue_type                priority_queues
% 2.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.58/1.00  --demod_completeness_check              fast
% 2.58/1.00  --demod_use_ground                      true
% 2.58/1.00  --sup_to_prop_solver                    passive
% 2.58/1.00  --sup_prop_simpl_new                    true
% 2.58/1.00  --sup_prop_simpl_given                  true
% 2.58/1.00  --sup_fun_splitting                     false
% 2.58/1.00  --sup_smt_interval                      50000
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Simplification Setup
% 2.58/1.00  
% 2.58/1.00  --sup_indices_passive                   []
% 2.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_full_bw                           [BwDemod]
% 2.58/1.00  --sup_immed_triv                        [TrivRules]
% 2.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_immed_bw_main                     []
% 2.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  
% 2.58/1.00  ------ Combination Options
% 2.58/1.00  
% 2.58/1.00  --comb_res_mult                         3
% 2.58/1.00  --comb_sup_mult                         2
% 2.58/1.00  --comb_inst_mult                        10
% 2.58/1.00  
% 2.58/1.00  ------ Debug Options
% 2.58/1.00  
% 2.58/1.00  --dbg_backtrace                         false
% 2.58/1.00  --dbg_dump_prop_clauses                 false
% 2.58/1.00  --dbg_dump_prop_clauses_file            -
% 2.58/1.00  --dbg_out_stat                          false
% 2.58/1.00  ------ Parsing...
% 2.58/1.00  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe:2:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... gs_s  sp: 1 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 2.58/1.00  ------ Proving...
% 2.58/1.00  ------ Problem Properties 
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  clauses                                 62
% 2.58/1.00  conjectures                             7
% 2.58/1.00  EPR                                     9
% 2.58/1.00  Horn                                    42
% 2.58/1.00  unary                                   9
% 2.58/1.00  binary                                  18
% 2.58/1.00  lits                                    165
% 2.58/1.00  lits eq                                 35
% 2.58/1.00  fd_pure                                 0
% 2.58/1.00  fd_pseudo                               0
% 2.58/1.00  fd_cond                                 5
% 2.58/1.00  fd_pseudo_cond                          4
% 2.58/1.00  AC symbols                              0
% 2.58/1.00  
% 2.58/1.00  ------ Schedule dynamic 5 is on 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  ------ 
% 2.58/1.00  Current options:
% 2.58/1.00  ------ 
% 2.58/1.00  
% 2.58/1.00  ------ Input Options
% 2.58/1.00  
% 2.58/1.00  --out_options                           all
% 2.58/1.00  --tptp_safe_out                         true
% 2.58/1.00  --problem_path                          ""
% 2.58/1.00  --include_path                          ""
% 2.58/1.00  --clausifier                            res/vclausify_rel
% 2.58/1.00  --clausifier_options                    --mode clausify
% 2.58/1.00  --stdin                                 false
% 2.58/1.00  --stats_out                             all
% 2.58/1.00  
% 2.58/1.00  ------ General Options
% 2.58/1.00  
% 2.58/1.00  --fof                                   false
% 2.58/1.00  --time_out_real                         305.
% 2.58/1.00  --time_out_virtual                      -1.
% 2.58/1.00  --symbol_type_check                     false
% 2.58/1.00  --clausify_out                          false
% 2.58/1.00  --sig_cnt_out                           false
% 2.58/1.00  --trig_cnt_out                          false
% 2.58/1.00  --trig_cnt_out_tolerance                1.
% 2.58/1.00  --trig_cnt_out_sk_spl                   false
% 2.58/1.00  --abstr_cl_out                          false
% 2.58/1.00  
% 2.58/1.00  ------ Global Options
% 2.58/1.00  
% 2.58/1.00  --schedule                              default
% 2.58/1.00  --add_important_lit                     false
% 2.58/1.00  --prop_solver_per_cl                    1000
% 2.58/1.00  --min_unsat_core                        false
% 2.58/1.00  --soft_assumptions                      false
% 2.58/1.00  --soft_lemma_size                       3
% 2.58/1.00  --prop_impl_unit_size                   0
% 2.58/1.00  --prop_impl_unit                        []
% 2.58/1.00  --share_sel_clauses                     true
% 2.58/1.00  --reset_solvers                         false
% 2.58/1.00  --bc_imp_inh                            [conj_cone]
% 2.58/1.00  --conj_cone_tolerance                   3.
% 2.58/1.00  --extra_neg_conj                        none
% 2.58/1.00  --large_theory_mode                     true
% 2.58/1.00  --prolific_symb_bound                   200
% 2.58/1.00  --lt_threshold                          2000
% 2.58/1.00  --clause_weak_htbl                      true
% 2.58/1.00  --gc_record_bc_elim                     false
% 2.58/1.00  
% 2.58/1.00  ------ Preprocessing Options
% 2.58/1.00  
% 2.58/1.00  --preprocessing_flag                    true
% 2.58/1.00  --time_out_prep_mult                    0.1
% 2.58/1.00  --splitting_mode                        input
% 2.58/1.00  --splitting_grd                         true
% 2.58/1.00  --splitting_cvd                         false
% 2.58/1.00  --splitting_cvd_svl                     false
% 2.58/1.00  --splitting_nvd                         32
% 2.58/1.00  --sub_typing                            true
% 2.58/1.00  --prep_gs_sim                           true
% 2.58/1.00  --prep_unflatten                        true
% 2.58/1.00  --prep_res_sim                          true
% 2.58/1.00  --prep_upred                            true
% 2.58/1.00  --prep_sem_filter                       exhaustive
% 2.58/1.00  --prep_sem_filter_out                   false
% 2.58/1.00  --pred_elim                             true
% 2.58/1.00  --res_sim_input                         true
% 2.58/1.00  --eq_ax_congr_red                       true
% 2.58/1.00  --pure_diseq_elim                       true
% 2.58/1.00  --brand_transform                       false
% 2.58/1.00  --non_eq_to_eq                          false
% 2.58/1.00  --prep_def_merge                        true
% 2.58/1.00  --prep_def_merge_prop_impl              false
% 2.58/1.00  --prep_def_merge_mbd                    true
% 2.58/1.00  --prep_def_merge_tr_red                 false
% 2.58/1.00  --prep_def_merge_tr_cl                  false
% 2.58/1.00  --smt_preprocessing                     true
% 2.58/1.00  --smt_ac_axioms                         fast
% 2.58/1.00  --preprocessed_out                      false
% 2.58/1.00  --preprocessed_stats                    false
% 2.58/1.00  
% 2.58/1.00  ------ Abstraction refinement Options
% 2.58/1.00  
% 2.58/1.00  --abstr_ref                             []
% 2.58/1.00  --abstr_ref_prep                        false
% 2.58/1.00  --abstr_ref_until_sat                   false
% 2.58/1.00  --abstr_ref_sig_restrict                funpre
% 2.58/1.00  --abstr_ref_af_restrict_to_split_sk     false
% 2.58/1.00  --abstr_ref_under                       []
% 2.58/1.00  
% 2.58/1.00  ------ SAT Options
% 2.58/1.00  
% 2.58/1.00  --sat_mode                              false
% 2.58/1.00  --sat_fm_restart_options                ""
% 2.58/1.00  --sat_gr_def                            false
% 2.58/1.00  --sat_epr_types                         true
% 2.58/1.00  --sat_non_cyclic_types                  false
% 2.58/1.00  --sat_finite_models                     false
% 2.58/1.00  --sat_fm_lemmas                         false
% 2.58/1.00  --sat_fm_prep                           false
% 2.58/1.00  --sat_fm_uc_incr                        true
% 2.58/1.00  --sat_out_model                         small
% 2.58/1.00  --sat_out_clauses                       false
% 2.58/1.00  
% 2.58/1.00  ------ QBF Options
% 2.58/1.00  
% 2.58/1.00  --qbf_mode                              false
% 2.58/1.00  --qbf_elim_univ                         false
% 2.58/1.00  --qbf_dom_inst                          none
% 2.58/1.00  --qbf_dom_pre_inst                      false
% 2.58/1.00  --qbf_sk_in                             false
% 2.58/1.00  --qbf_pred_elim                         true
% 2.58/1.00  --qbf_split                             512
% 2.58/1.00  
% 2.58/1.00  ------ BMC1 Options
% 2.58/1.00  
% 2.58/1.00  --bmc1_incremental                      false
% 2.58/1.00  --bmc1_axioms                           reachable_all
% 2.58/1.00  --bmc1_min_bound                        0
% 2.58/1.00  --bmc1_max_bound                        -1
% 2.58/1.00  --bmc1_max_bound_default                -1
% 2.58/1.00  --bmc1_symbol_reachability              true
% 2.58/1.00  --bmc1_property_lemmas                  false
% 2.58/1.00  --bmc1_k_induction                      false
% 2.58/1.00  --bmc1_non_equiv_states                 false
% 2.58/1.00  --bmc1_deadlock                         false
% 2.58/1.00  --bmc1_ucm                              false
% 2.58/1.00  --bmc1_add_unsat_core                   none
% 2.58/1.00  --bmc1_unsat_core_children              false
% 2.58/1.00  --bmc1_unsat_core_extrapolate_axioms    false
% 2.58/1.00  --bmc1_out_stat                         full
% 2.58/1.00  --bmc1_ground_init                      false
% 2.58/1.00  --bmc1_pre_inst_next_state              false
% 2.58/1.00  --bmc1_pre_inst_state                   false
% 2.58/1.00  --bmc1_pre_inst_reach_state             false
% 2.58/1.00  --bmc1_out_unsat_core                   false
% 2.58/1.00  --bmc1_aig_witness_out                  false
% 2.58/1.00  --bmc1_verbose                          false
% 2.58/1.00  --bmc1_dump_clauses_tptp                false
% 2.58/1.00  --bmc1_dump_unsat_core_tptp             false
% 2.58/1.00  --bmc1_dump_file                        -
% 2.58/1.00  --bmc1_ucm_expand_uc_limit              128
% 2.58/1.00  --bmc1_ucm_n_expand_iterations          6
% 2.58/1.00  --bmc1_ucm_extend_mode                  1
% 2.58/1.00  --bmc1_ucm_init_mode                    2
% 2.58/1.00  --bmc1_ucm_cone_mode                    none
% 2.58/1.00  --bmc1_ucm_reduced_relation_type        0
% 2.58/1.00  --bmc1_ucm_relax_model                  4
% 2.58/1.00  --bmc1_ucm_full_tr_after_sat            true
% 2.58/1.00  --bmc1_ucm_expand_neg_assumptions       false
% 2.58/1.00  --bmc1_ucm_layered_model                none
% 2.58/1.00  --bmc1_ucm_max_lemma_size               10
% 2.58/1.00  
% 2.58/1.00  ------ AIG Options
% 2.58/1.00  
% 2.58/1.00  --aig_mode                              false
% 2.58/1.00  
% 2.58/1.00  ------ Instantiation Options
% 2.58/1.00  
% 2.58/1.00  --instantiation_flag                    true
% 2.58/1.00  --inst_sos_flag                         false
% 2.58/1.00  --inst_sos_phase                        true
% 2.58/1.00  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 2.58/1.00  --inst_lit_sel_side                     none
% 2.58/1.00  --inst_solver_per_active                1400
% 2.58/1.00  --inst_solver_calls_frac                1.
% 2.58/1.00  --inst_passive_queue_type               priority_queues
% 2.58/1.00  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 2.58/1.00  --inst_passive_queues_freq              [25;2]
% 2.58/1.00  --inst_dismatching                      true
% 2.58/1.00  --inst_eager_unprocessed_to_passive     true
% 2.58/1.00  --inst_prop_sim_given                   true
% 2.58/1.00  --inst_prop_sim_new                     false
% 2.58/1.00  --inst_subs_new                         false
% 2.58/1.00  --inst_eq_res_simp                      false
% 2.58/1.00  --inst_subs_given                       false
% 2.58/1.00  --inst_orphan_elimination               true
% 2.58/1.00  --inst_learning_loop_flag               true
% 2.58/1.00  --inst_learning_start                   3000
% 2.58/1.00  --inst_learning_factor                  2
% 2.58/1.00  --inst_start_prop_sim_after_learn       3
% 2.58/1.00  --inst_sel_renew                        solver
% 2.58/1.00  --inst_lit_activity_flag                true
% 2.58/1.00  --inst_restr_to_given                   false
% 2.58/1.00  --inst_activity_threshold               500
% 2.58/1.00  --inst_out_proof                        true
% 2.58/1.00  
% 2.58/1.00  ------ Resolution Options
% 2.58/1.00  
% 2.58/1.00  --resolution_flag                       false
% 2.58/1.00  --res_lit_sel                           adaptive
% 2.58/1.00  --res_lit_sel_side                      none
% 2.58/1.00  --res_ordering                          kbo
% 2.58/1.00  --res_to_prop_solver                    active
% 2.58/1.00  --res_prop_simpl_new                    false
% 2.58/1.00  --res_prop_simpl_given                  true
% 2.58/1.00  --res_passive_queue_type                priority_queues
% 2.58/1.00  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 2.58/1.00  --res_passive_queues_freq               [15;5]
% 2.58/1.00  --res_forward_subs                      full
% 2.58/1.00  --res_backward_subs                     full
% 2.58/1.00  --res_forward_subs_resolution           true
% 2.58/1.00  --res_backward_subs_resolution          true
% 2.58/1.00  --res_orphan_elimination                true
% 2.58/1.00  --res_time_limit                        2.
% 2.58/1.00  --res_out_proof                         true
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Options
% 2.58/1.00  
% 2.58/1.00  --superposition_flag                    true
% 2.58/1.00  --sup_passive_queue_type                priority_queues
% 2.58/1.00  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 2.58/1.00  --sup_passive_queues_freq               [8;1;4]
% 2.58/1.00  --demod_completeness_check              fast
% 2.58/1.00  --demod_use_ground                      true
% 2.58/1.00  --sup_to_prop_solver                    passive
% 2.58/1.00  --sup_prop_simpl_new                    true
% 2.58/1.00  --sup_prop_simpl_given                  true
% 2.58/1.00  --sup_fun_splitting                     false
% 2.58/1.00  --sup_smt_interval                      50000
% 2.58/1.00  
% 2.58/1.00  ------ Superposition Simplification Setup
% 2.58/1.00  
% 2.58/1.00  --sup_indices_passive                   []
% 2.58/1.00  --sup_indices_active                    [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_immed                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex;BwDemodIndex]
% 2.58/1.00  --sup_full_triv                         [TrivRules;PropSubs]
% 2.58/1.00  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_full_bw                           [BwDemod]
% 2.58/1.00  --sup_immed_triv                        [TrivRules]
% 2.58/1.00  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 2.58/1.00  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_immed_bw_main                     []
% 2.58/1.00  --sup_immed_bw_immed                    [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  --sup_input_triv                        [Unflattening;TrivRules]
% 2.58/1.00  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption;FwSubsumptionRes]
% 2.58/1.00  --sup_input_bw                          [BwDemod;BwSubsumption;BwSubsumptionRes]
% 2.58/1.00  
% 2.58/1.00  ------ Combination Options
% 2.58/1.00  
% 2.58/1.00  --comb_res_mult                         3
% 2.58/1.00  --comb_sup_mult                         2
% 2.58/1.00  --comb_inst_mult                        10
% 2.58/1.00  
% 2.58/1.00  ------ Debug Options
% 2.58/1.00  
% 2.58/1.00  --dbg_backtrace                         false
% 2.58/1.00  --dbg_dump_prop_clauses                 false
% 2.58/1.00  --dbg_dump_prop_clauses_file            -
% 2.58/1.00  --dbg_out_stat                          false
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  ------ Proving...
% 2.58/1.00  
% 2.58/1.00  
% 2.58/1.00  % SZS status Theorem for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  % SZS output start CNFRefutation for theBenchmark.p
% 2.58/1.00  
% 2.58/1.00  fof(f4,axiom,(
% 2.58/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f25,plain,(
% 2.58/1.00    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 2.58/1.00    inference(rectify,[],[f4])).
% 2.58/1.00  
% 2.58/1.00  fof(f26,plain,(
% 2.58/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 2.58/1.00    inference(ennf_transformation,[],[f25])).
% 2.58/1.00  
% 2.58/1.00  fof(f63,plain,(
% 2.58/1.00    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)))),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f64,plain,(
% 2.58/1.00    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK4(X0,X1),X1) & r2_hidden(sK4(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 2.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4])],[f26,f63])).
% 2.58/1.00  
% 2.58/1.00  fof(f98,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,X1) | ~r2_hidden(X2,X1) | ~r2_hidden(X2,X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f64])).
% 2.58/1.00  
% 2.58/1.00  fof(f50,plain,(
% 2.58/1.00    ! [X2,X0,X1,X3] : (sP0(X2,X0,X1,X3) <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5))))),
% 2.58/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 2.58/1.00  
% 2.58/1.00  fof(f77,plain,(
% 2.58/1.00    ! [X2,X0,X1,X3] : ((sP0(X2,X0,X1,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | r2_hidden(X4,X3)))) & (! [X4] : ((r2_hidden(X4,X3) | ! [X5] : (~r1_partfun1(X2,X5) | ~v1_partfun1(X5,X0) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5))) & (? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)) | ~r2_hidden(X4,X3))) | ~sP0(X2,X0,X1,X3)))),
% 2.58/1.00    inference(nnf_transformation,[],[f50])).
% 2.58/1.00  
% 2.58/1.00  fof(f78,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.58/1.00    inference(rectify,[],[f77])).
% 2.58/1.00  
% 2.58/1.00  fof(f81,plain,(
% 2.58/1.00    ! [X7,X2,X1,X0] : (? [X9] : (r1_partfun1(X0,X9) & v1_partfun1(X9,X1) & X7 = X9 & m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X9)) => (r1_partfun1(X0,sK12(X0,X1,X2,X7)) & v1_partfun1(sK12(X0,X1,X2,X7),X1) & sK12(X0,X1,X2,X7) = X7 & m1_subset_1(sK12(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK12(X0,X1,X2,X7))))),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f80,plain,(
% 2.58/1.00    ( ! [X4] : (! [X3,X2,X1,X0] : (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) => (r1_partfun1(X0,sK11(X0,X1,X2,X3)) & v1_partfun1(sK11(X0,X1,X2,X3),X1) & sK11(X0,X1,X2,X3) = X4 & m1_subset_1(sK11(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK11(X0,X1,X2,X3))))) )),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f79,plain,(
% 2.58/1.00    ! [X3,X2,X1,X0] : (? [X4] : ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | X4 != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(X4,X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & X4 = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(X4,X3))) => ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK10(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK10(X0,X1,X2,X3),X3)) & (? [X6] : (r1_partfun1(X0,X6) & v1_partfun1(X6,X1) & sK10(X0,X1,X2,X3) = X6 & m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(X6)) | r2_hidden(sK10(X0,X1,X2,X3),X3))))),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f82,plain,(
% 2.58/1.00    ! [X0,X1,X2,X3] : ((sP0(X0,X1,X2,X3) | ((! [X5] : (~r1_partfun1(X0,X5) | ~v1_partfun1(X5,X1) | sK10(X0,X1,X2,X3) != X5 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X5)) | ~r2_hidden(sK10(X0,X1,X2,X3),X3)) & ((r1_partfun1(X0,sK11(X0,X1,X2,X3)) & v1_partfun1(sK11(X0,X1,X2,X3),X1) & sK10(X0,X1,X2,X3) = sK11(X0,X1,X2,X3) & m1_subset_1(sK11(X0,X1,X2,X3),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK11(X0,X1,X2,X3))) | r2_hidden(sK10(X0,X1,X2,X3),X3)))) & (! [X7] : ((r2_hidden(X7,X3) | ! [X8] : (~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8))) & ((r1_partfun1(X0,sK12(X0,X1,X2,X7)) & v1_partfun1(sK12(X0,X1,X2,X7),X1) & sK12(X0,X1,X2,X7) = X7 & m1_subset_1(sK12(X0,X1,X2,X7),k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_1(sK12(X0,X1,X2,X7))) | ~r2_hidden(X7,X3))) | ~sP0(X0,X1,X2,X3)))),
% 2.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK10,sK11,sK12])],[f78,f81,f80,f79])).
% 2.58/1.00  
% 2.58/1.00  fof(f135,plain,(
% 2.58/1.00    ( ! [X2,X0,X8,X7,X3,X1] : (r2_hidden(X7,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | X7 != X8 | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f82])).
% 2.58/1.00  
% 2.58/1.00  fof(f161,plain,(
% 2.58/1.00    ( ! [X2,X0,X8,X3,X1] : (r2_hidden(X8,X3) | ~r1_partfun1(X0,X8) | ~v1_partfun1(X8,X1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X8) | ~sP0(X0,X1,X2,X3)) )),
% 2.58/1.00    inference(equality_resolution,[],[f135])).
% 2.58/1.00  
% 2.58/1.00  fof(f5,axiom,(
% 2.58/1.00    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f27,plain,(
% 2.58/1.00    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 2.58/1.00    inference(ennf_transformation,[],[f5])).
% 2.58/1.00  
% 2.58/1.00  fof(f99,plain,(
% 2.58/1.00    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f27])).
% 2.58/1.00  
% 2.58/1.00  fof(f23,conjecture,(
% 2.58/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f24,negated_conjecture,(
% 2.58/1.00    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (r1_partfun1(X2,X3) => (r2_hidden(X3,k5_partfun1(X0,X1,X2)) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)))))),
% 2.58/1.00    inference(negated_conjecture,[],[f23])).
% 2.58/1.00  
% 2.58/1.00  fof(f48,plain,(
% 2.58/1.00    ? [X0,X1,X2] : (? [X3] : (((~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1)) & r1_partfun1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)))),
% 2.58/1.00    inference(ennf_transformation,[],[f24])).
% 2.58/1.00  
% 2.58/1.00  fof(f49,plain,(
% 2.58/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2))),
% 2.58/1.00    inference(flattening,[],[f48])).
% 2.58/1.00  
% 2.58/1.00  fof(f84,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => (~r2_hidden(sK16,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,sK16) & m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(sK16,X0,X1) & v1_funct_1(sK16))) )),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f83,plain,(
% 2.58/1.00    ? [X0,X1,X2] : (? [X3] : (~r2_hidden(X3,k5_partfun1(X0,X1,X2)) & (k1_xboole_0 = X0 | k1_xboole_0 != X1) & r1_partfun1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => (? [X3] : (~r2_hidden(X3,k5_partfun1(sK13,sK14,sK15)) & (k1_xboole_0 = sK13 | k1_xboole_0 != sK14) & r1_partfun1(sK15,X3) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) & v1_funct_2(X3,sK13,sK14) & v1_funct_1(X3)) & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) & v1_funct_1(sK15))),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f85,plain,(
% 2.58/1.00    (~r2_hidden(sK16,k5_partfun1(sK13,sK14,sK15)) & (k1_xboole_0 = sK13 | k1_xboole_0 != sK14) & r1_partfun1(sK15,sK16) & m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) & v1_funct_2(sK16,sK13,sK14) & v1_funct_1(sK16)) & m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) & v1_funct_1(sK15)),
% 2.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK13,sK14,sK15,sK16])],[f49,f84,f83])).
% 2.58/1.00  
% 2.58/1.00  fof(f147,plain,(
% 2.58/1.00    m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))),
% 2.58/1.00    inference(cnf_transformation,[],[f85])).
% 2.58/1.00  
% 2.58/1.00  fof(f13,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f34,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.58/1.00    inference(ennf_transformation,[],[f13])).
% 2.58/1.00  
% 2.58/1.00  fof(f109,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.58/1.00    inference(cnf_transformation,[],[f34])).
% 2.58/1.00  
% 2.58/1.00  fof(f9,axiom,(
% 2.58/1.00    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k7_relat_1(X0,k1_xboole_0))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f32,plain,(
% 2.58/1.00    ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 2.58/1.00    inference(ennf_transformation,[],[f9])).
% 2.58/1.00  
% 2.58/1.00  fof(f104,plain,(
% 2.58/1.00    ( ! [X0] : (k1_xboole_0 = k7_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f32])).
% 2.58/1.00  
% 2.58/1.00  fof(f8,axiom,(
% 2.58/1.00    ! [X0,X1] : (v1_relat_1(X0) => v1_relat_1(k7_relat_1(X0,X1)))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f31,plain,(
% 2.58/1.00    ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0))),
% 2.58/1.00    inference(ennf_transformation,[],[f8])).
% 2.58/1.00  
% 2.58/1.00  fof(f103,plain,(
% 2.58/1.00    ( ! [X0,X1] : (v1_relat_1(k7_relat_1(X0,X1)) | ~v1_relat_1(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f31])).
% 2.58/1.00  
% 2.58/1.00  fof(f12,axiom,(
% 2.58/1.00    ! [X0,X1] : (v1_relat_1(X1) => k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f33,plain,(
% 2.58/1.00    ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1))),
% 2.58/1.00    inference(ennf_transformation,[],[f12])).
% 2.58/1.00  
% 2.58/1.00  fof(f108,plain,(
% 2.58/1.00    ( ! [X0,X1] : (k3_xboole_0(k1_relat_1(X1),X0) = k1_relat_1(k7_relat_1(X1,X0)) | ~v1_relat_1(X1)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f33])).
% 2.58/1.00  
% 2.58/1.00  fof(f10,axiom,(
% 2.58/1.00    ! [X0] : k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f105,plain,(
% 2.58/1.00    ( ! [X0] : (k1_xboole_0 = k7_relat_1(k1_xboole_0,X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f10])).
% 2.58/1.00  
% 2.58/1.00  fof(f11,axiom,(
% 2.58/1.00    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f106,plain,(
% 2.58/1.00    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 2.58/1.00    inference(cnf_transformation,[],[f11])).
% 2.58/1.00  
% 2.58/1.00  fof(f51,plain,(
% 2.58/1.00    ! [X1,X0,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> sP0(X2,X0,X1,X3)) | ~sP1(X1,X0,X2))),
% 2.58/1.00    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 2.58/1.00  
% 2.58/1.00  fof(f75,plain,(
% 2.58/1.00    ! [X1,X0,X2] : (! [X3] : ((k5_partfun1(X0,X1,X2) = X3 | ~sP0(X2,X0,X1,X3)) & (sP0(X2,X0,X1,X3) | k5_partfun1(X0,X1,X2) != X3)) | ~sP1(X1,X0,X2))),
% 2.58/1.00    inference(nnf_transformation,[],[f51])).
% 2.58/1.00  
% 2.58/1.00  fof(f76,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (! [X3] : ((k5_partfun1(X1,X0,X2) = X3 | ~sP0(X2,X1,X0,X3)) & (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3)) | ~sP1(X0,X1,X2))),
% 2.58/1.00    inference(rectify,[],[f75])).
% 2.58/1.00  
% 2.58/1.00  fof(f128,plain,(
% 2.58/1.00    ( ! [X2,X0,X3,X1] : (sP0(X2,X1,X0,X3) | k5_partfun1(X1,X0,X2) != X3 | ~sP1(X0,X1,X2)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f76])).
% 2.58/1.00  
% 2.58/1.00  fof(f159,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (sP0(X2,X1,X0,k5_partfun1(X1,X0,X2)) | ~sP1(X0,X1,X2)) )),
% 2.58/1.00    inference(equality_resolution,[],[f128])).
% 2.58/1.00  
% 2.58/1.00  fof(f22,axiom,(
% 2.58/1.00    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f46,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 2.58/1.00    inference(ennf_transformation,[],[f22])).
% 2.58/1.00  
% 2.58/1.00  fof(f47,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (! [X3] : (k5_partfun1(X0,X1,X2) = X3 <=> ! [X4] : (r2_hidden(X4,X3) <=> ? [X5] : (r1_partfun1(X2,X5) & v1_partfun1(X5,X0) & X4 = X5 & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X5)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.58/1.00    inference(flattening,[],[f46])).
% 2.58/1.00  
% 2.58/1.00  fof(f52,plain,(
% 2.58/1.00    ! [X0,X1,X2] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 2.58/1.00    inference(definition_folding,[],[f47,f51,f50])).
% 2.58/1.00  
% 2.58/1.00  fof(f142,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (sP1(X1,X0,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f52])).
% 2.58/1.00  
% 2.58/1.00  fof(f19,axiom,(
% 2.58/1.00    ! [X0,X1] : (v1_xboole_0(X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_partfun1(X2,X0)))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f41,plain,(
% 2.58/1.00    ! [X0,X1] : (! [X2] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | ~v1_xboole_0(X0))),
% 2.58/1.00    inference(ennf_transformation,[],[f19])).
% 2.58/1.00  
% 2.58/1.00  fof(f119,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_xboole_0(X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f41])).
% 2.58/1.00  
% 2.58/1.00  fof(f20,axiom,(
% 2.58/1.00    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f42,plain,(
% 2.58/1.00    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.58/1.00    inference(ennf_transformation,[],[f20])).
% 2.58/1.00  
% 2.58/1.00  fof(f43,plain,(
% 2.58/1.00    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 2.58/1.00    inference(flattening,[],[f42])).
% 2.58/1.00  
% 2.58/1.00  fof(f121,plain,(
% 2.58/1.00    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f43])).
% 2.58/1.00  
% 2.58/1.00  fof(f146,plain,(
% 2.58/1.00    v1_funct_2(sK16,sK13,sK14)),
% 2.58/1.00    inference(cnf_transformation,[],[f85])).
% 2.58/1.00  
% 2.58/1.00  fof(f145,plain,(
% 2.58/1.00    v1_funct_1(sK16)),
% 2.58/1.00    inference(cnf_transformation,[],[f85])).
% 2.58/1.00  
% 2.58/1.00  fof(f1,axiom,(
% 2.58/1.00    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f53,plain,(
% 2.58/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 2.58/1.00    inference(nnf_transformation,[],[f1])).
% 2.58/1.00  
% 2.58/1.00  fof(f54,plain,(
% 2.58/1.00    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.58/1.00    inference(rectify,[],[f53])).
% 2.58/1.00  
% 2.58/1.00  fof(f55,plain,(
% 2.58/1.00    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK2(X0),X0))),
% 2.58/1.00    introduced(choice_axiom,[])).
% 2.58/1.00  
% 2.58/1.00  fof(f56,plain,(
% 2.58/1.00    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 2.58/1.00    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f54,f55])).
% 2.58/1.00  
% 2.58/1.00  fof(f87,plain,(
% 2.58/1.00    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0)) )),
% 2.58/1.00    inference(cnf_transformation,[],[f56])).
% 2.58/1.00  
% 2.58/1.00  fof(f3,axiom,(
% 2.58/1.00    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 2.58/1.00    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 2.58/1.00  
% 2.58/1.00  fof(f62,plain,(
% 2.58/1.00    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 2.58/1.00    inference(nnf_transformation,[],[f3])).
% 2.58/1.00  
% 2.58/1.00  fof(f95,plain,(
% 2.58/1.00    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 2.58/1.00    inference(cnf_transformation,[],[f62])).
% 2.58/1.00  
% 2.58/1.00  fof(f150,plain,(
% 2.58/1.00    ~r2_hidden(sK16,k5_partfun1(sK13,sK14,sK15))),
% 2.58/1.00    inference(cnf_transformation,[],[f85])).
% 2.58/1.00  
% 2.58/1.00  fof(f149,plain,(
% 2.58/1.00    k1_xboole_0 = sK13 | k1_xboole_0 != sK14),
% 2.58/1.00    inference(cnf_transformation,[],[f85])).
% 2.58/1.00  
% 2.58/1.00  fof(f148,plain,(
% 2.58/1.00    r1_partfun1(sK15,sK16)),
% 2.58/1.00    inference(cnf_transformation,[],[f85])).
% 2.58/1.00  
% 2.58/1.00  fof(f144,plain,(
% 2.58/1.00    m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))),
% 2.58/1.00    inference(cnf_transformation,[],[f85])).
% 2.58/1.00  
% 2.58/1.00  fof(f143,plain,(
% 2.58/1.00    v1_funct_1(sK15)),
% 2.58/1.00    inference(cnf_transformation,[],[f85])).
% 2.58/1.00  
% 2.58/1.00  cnf(c_10,plain,
% 2.58/1.00      ( ~ r1_xboole_0(X0,X1) | ~ r2_hidden(X2,X0) | ~ r2_hidden(X2,X1) ),
% 2.58/1.00      inference(cnf_transformation,[],[f98]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_13522,plain,
% 2.58/1.00      ( ~ r1_xboole_0(X0,X1)
% 2.58/1.00      | ~ r2_hidden(sK2(X0),X0)
% 2.58/1.00      | ~ r2_hidden(sK2(X0),X1) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_10]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_13524,plain,
% 2.58/1.00      ( ~ r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.58/1.00      | ~ r2_hidden(sK2(k1_xboole_0),k1_xboole_0) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_13522]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_50,plain,
% 2.58/1.00      ( ~ sP0(X0,X1,X2,X3)
% 2.58/1.00      | ~ r1_partfun1(X0,X4)
% 2.58/1.00      | ~ v1_partfun1(X4,X1)
% 2.58/1.00      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.00      | r2_hidden(X4,X3)
% 2.58/1.00      | ~ v1_funct_1(X4) ),
% 2.58/1.00      inference(cnf_transformation,[],[f161]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_8894,plain,
% 2.58/1.00      ( ~ sP0(X0,X1,X2,X3)
% 2.58/1.00      | ~ r1_partfun1(X0,sK16)
% 2.58/1.00      | ~ v1_partfun1(sK16,X1)
% 2.58/1.00      | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.00      | r2_hidden(sK16,X3)
% 2.58/1.00      | ~ v1_funct_1(sK16) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_50]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_9297,plain,
% 2.58/1.00      ( ~ sP0(sK15,X0,X1,X2)
% 2.58/1.00      | ~ r1_partfun1(sK15,sK16)
% 2.58/1.00      | ~ v1_partfun1(sK16,X0)
% 2.58/1.00      | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.58/1.00      | r2_hidden(sK16,X2)
% 2.58/1.00      | ~ v1_funct_1(sK16) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_8894]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_10214,plain,
% 2.58/1.00      ( ~ sP0(sK15,sK13,X0,X1)
% 2.58/1.00      | ~ r1_partfun1(sK15,sK16)
% 2.58/1.00      | ~ v1_partfun1(sK16,sK13)
% 2.58/1.00      | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,X0)))
% 2.58/1.00      | r2_hidden(sK16,X1)
% 2.58/1.00      | ~ v1_funct_1(sK16) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_9297]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_11283,plain,
% 2.58/1.00      ( ~ sP0(sK15,sK13,sK14,X0)
% 2.58/1.00      | ~ r1_partfun1(sK15,sK16)
% 2.58/1.00      | ~ v1_partfun1(sK16,sK13)
% 2.58/1.00      | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
% 2.58/1.00      | r2_hidden(sK16,X0)
% 2.58/1.00      | ~ v1_funct_1(sK16) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_10214]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_12892,plain,
% 2.58/1.00      ( ~ sP0(sK15,sK13,sK14,k5_partfun1(sK13,sK14,sK15))
% 2.58/1.00      | ~ r1_partfun1(sK15,sK16)
% 2.58/1.00      | ~ v1_partfun1(sK16,sK13)
% 2.58/1.00      | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
% 2.58/1.00      | r2_hidden(sK16,k5_partfun1(sK13,sK14,sK15))
% 2.58/1.00      | ~ v1_funct_1(sK16) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_11283]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_13,plain,
% 2.58/1.00      ( ~ v1_xboole_0(X0) | k1_xboole_0 = X0 ),
% 2.58/1.00      inference(cnf_transformation,[],[f99]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_10350,plain,
% 2.58/1.00      ( ~ v1_xboole_0(sK14) | k1_xboole_0 = sK14 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_13]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_60,negated_conjecture,
% 2.58/1.00      ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) ),
% 2.58/1.00      inference(cnf_transformation,[],[f147]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_8285,plain,
% 2.58/1.00      ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_23,plain,
% 2.58/1.00      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.00      | v1_relat_1(X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f109]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_8310,plain,
% 2.58/1.00      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) != iProver_top
% 2.58/1.00      | v1_relat_1(X0) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_9525,plain,
% 2.58/1.00      ( v1_relat_1(sK16) = iProver_top ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_8285,c_8310]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_18,plain,
% 2.58/1.00      ( ~ v1_relat_1(X0) | k7_relat_1(X0,k1_xboole_0) = k1_xboole_0 ),
% 2.58/1.00      inference(cnf_transformation,[],[f104]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_8312,plain,
% 2.58/1.00      ( k7_relat_1(X0,k1_xboole_0) = k1_xboole_0
% 2.58/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_18]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_9626,plain,
% 2.58/1.00      ( k7_relat_1(sK16,k1_xboole_0) = k1_xboole_0 ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_9525,c_8312]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_17,plain,
% 2.58/1.00      ( ~ v1_relat_1(X0) | v1_relat_1(k7_relat_1(X0,X1)) ),
% 2.58/1.00      inference(cnf_transformation,[],[f103]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_8313,plain,
% 2.58/1.00      ( v1_relat_1(X0) != iProver_top
% 2.58/1.00      | v1_relat_1(k7_relat_1(X0,X1)) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_17]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_9649,plain,
% 2.58/1.00      ( v1_relat_1(sK16) != iProver_top
% 2.58/1.00      | v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_9626,c_8313]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_69,plain,
% 2.58/1.00      ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_60]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_8790,plain,
% 2.58/1.00      ( ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
% 2.58/1.00      | v1_relat_1(sK16) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_23]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_8791,plain,
% 2.58/1.00      ( m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) != iProver_top
% 2.58/1.00      | v1_relat_1(sK16) = iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_8790]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_9754,plain,
% 2.58/1.00      ( v1_relat_1(k1_xboole_0) = iProver_top ),
% 2.58/1.00      inference(global_propositional_subsumption,
% 2.58/1.00                [status(thm)],
% 2.58/1.00                [c_9649,c_69,c_8791]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_22,plain,
% 2.58/1.00      ( ~ v1_relat_1(X0)
% 2.58/1.00      | k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1) ),
% 2.58/1.00      inference(cnf_transformation,[],[f108]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_8311,plain,
% 2.58/1.00      ( k1_relat_1(k7_relat_1(X0,X1)) = k3_xboole_0(k1_relat_1(X0),X1)
% 2.58/1.00      | v1_relat_1(X0) != iProver_top ),
% 2.58/1.00      inference(predicate_to_equality,[status(thm)],[c_22]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_10170,plain,
% 2.58/1.00      ( k1_relat_1(k7_relat_1(k1_xboole_0,X0)) = k3_xboole_0(k1_relat_1(k1_xboole_0),X0) ),
% 2.58/1.00      inference(superposition,[status(thm)],[c_9754,c_8311]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_19,plain,
% 2.58/1.00      ( k7_relat_1(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.58/1.00      inference(cnf_transformation,[],[f105]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_21,plain,
% 2.58/1.00      ( k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
% 2.58/1.00      inference(cnf_transformation,[],[f106]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_10178,plain,
% 2.58/1.00      ( k3_xboole_0(k1_xboole_0,X0) = k1_xboole_0 ),
% 2.58/1.00      inference(light_normalisation,[status(thm)],[c_10170,c_19,c_21]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_10189,plain,
% 2.58/1.00      ( k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_10178]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_7014,plain,
% 2.58/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(X1) | X1 != X0 ),
% 2.58/1.00      theory(equality) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_9614,plain,
% 2.58/1.00      ( ~ v1_xboole_0(X0) | v1_xboole_0(sK13) | sK13 != X0 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_7014]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_9616,plain,
% 2.58/1.00      ( v1_xboole_0(sK13)
% 2.58/1.00      | ~ v1_xboole_0(k1_xboole_0)
% 2.58/1.00      | sK13 != k1_xboole_0 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_9614]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_7012,plain,( X0 = X0 ),theory(equality) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_9421,plain,
% 2.58/1.00      ( sK13 = sK13 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_7012]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_7013,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_8820,plain,
% 2.58/1.00      ( sK13 != X0 | sK13 = k1_xboole_0 | k1_xboole_0 != X0 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_7013]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_9420,plain,
% 2.58/1.00      ( sK13 != sK13 | sK13 = k1_xboole_0 | k1_xboole_0 != sK13 ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_8820]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_43,plain,
% 2.58/1.00      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0)) | ~ sP1(X2,X1,X0) ),
% 2.58/1.00      inference(cnf_transformation,[],[f159]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_56,plain,
% 2.58/1.00      ( sP1(X0,X1,X2)
% 2.58/1.00      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
% 2.58/1.00      | ~ v1_funct_1(X2) ),
% 2.58/1.00      inference(cnf_transformation,[],[f142]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_789,plain,
% 2.58/1.00      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 2.58/1.00      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
% 2.58/1.00      | ~ v1_funct_1(X3)
% 2.58/1.00      | X4 != X1
% 2.58/1.00      | X3 != X0
% 2.58/1.00      | X5 != X2 ),
% 2.58/1.00      inference(resolution_lifted,[status(thm)],[c_43,c_56]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_790,plain,
% 2.58/1.00      ( sP0(X0,X1,X2,k5_partfun1(X1,X2,X0))
% 2.58/1.00      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.00      | ~ v1_funct_1(X0) ),
% 2.58/1.00      inference(unflattening,[status(thm)],[c_789]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_8867,plain,
% 2.58/1.00      ( sP0(sK15,X0,X1,k5_partfun1(X0,X1,sK15))
% 2.58/1.00      | ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
% 2.58/1.00      | ~ v1_funct_1(sK15) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_790]) ).
% 2.58/1.00  
% 2.58/1.00  cnf(c_9284,plain,
% 2.58/1.00      ( sP0(sK15,sK13,sK14,k5_partfun1(sK13,sK14,sK15))
% 2.58/1.00      | ~ m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
% 2.58/1.00      | ~ v1_funct_1(sK15) ),
% 2.58/1.00      inference(instantiation,[status(thm)],[c_8867]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_33,plain,
% 2.58/1.01      ( v1_partfun1(X0,X1)
% 2.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.01      | ~ v1_xboole_0(X1) ),
% 2.58/1.01      inference(cnf_transformation,[],[f119]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_8814,plain,
% 2.58/1.01      ( v1_partfun1(sK16,sK13)
% 2.58/1.01      | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
% 2.58/1.01      | ~ v1_xboole_0(sK13) ),
% 2.58/1.01      inference(instantiation,[status(thm)],[c_33]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_34,plain,
% 2.58/1.01      ( ~ v1_funct_2(X0,X1,X2)
% 2.58/1.01      | v1_partfun1(X0,X1)
% 2.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.01      | ~ v1_funct_1(X0)
% 2.58/1.01      | v1_xboole_0(X2) ),
% 2.58/1.01      inference(cnf_transformation,[],[f121]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_61,negated_conjecture,
% 2.58/1.01      ( v1_funct_2(sK16,sK13,sK14) ),
% 2.58/1.01      inference(cnf_transformation,[],[f146]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1471,plain,
% 2.58/1.01      ( v1_partfun1(X0,X1)
% 2.58/1.01      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
% 2.58/1.01      | ~ v1_funct_1(X0)
% 2.58/1.01      | v1_xboole_0(X2)
% 2.58/1.01      | sK14 != X2
% 2.58/1.01      | sK13 != X1
% 2.58/1.01      | sK16 != X0 ),
% 2.58/1.01      inference(resolution_lifted,[status(thm)],[c_34,c_61]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1472,plain,
% 2.58/1.01      ( v1_partfun1(sK16,sK13)
% 2.58/1.01      | ~ m1_subset_1(sK16,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14)))
% 2.58/1.01      | ~ v1_funct_1(sK16)
% 2.58/1.01      | v1_xboole_0(sK14) ),
% 2.58/1.01      inference(unflattening,[status(thm)],[c_1471]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_62,negated_conjecture,
% 2.58/1.01      ( v1_funct_1(sK16) ),
% 2.58/1.01      inference(cnf_transformation,[],[f145]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_1474,plain,
% 2.58/1.01      ( v1_partfun1(sK16,sK13) | v1_xboole_0(sK14) ),
% 2.58/1.01      inference(global_propositional_subsumption,
% 2.58/1.01                [status(thm)],
% 2.58/1.01                [c_1472,c_62,c_60]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_0,plain,
% 2.58/1.01      ( r2_hidden(sK2(X0),X0) | v1_xboole_0(X0) ),
% 2.58/1.01      inference(cnf_transformation,[],[f87]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_219,plain,
% 2.58/1.01      ( r2_hidden(sK2(k1_xboole_0),k1_xboole_0)
% 2.58/1.01      | v1_xboole_0(k1_xboole_0) ),
% 2.58/1.01      inference(instantiation,[status(thm)],[c_0]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_8,plain,
% 2.58/1.01      ( r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0 ),
% 2.58/1.01      inference(cnf_transformation,[],[f95]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_201,plain,
% 2.58/1.01      ( r1_xboole_0(k1_xboole_0,k1_xboole_0)
% 2.58/1.01      | k3_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
% 2.58/1.01      inference(instantiation,[status(thm)],[c_8]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_57,negated_conjecture,
% 2.58/1.01      ( ~ r2_hidden(sK16,k5_partfun1(sK13,sK14,sK15)) ),
% 2.58/1.01      inference(cnf_transformation,[],[f150]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_58,negated_conjecture,
% 2.58/1.01      ( k1_xboole_0 != sK14 | k1_xboole_0 = sK13 ),
% 2.58/1.01      inference(cnf_transformation,[],[f149]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_59,negated_conjecture,
% 2.58/1.01      ( r1_partfun1(sK15,sK16) ),
% 2.58/1.01      inference(cnf_transformation,[],[f148]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_63,negated_conjecture,
% 2.58/1.01      ( m1_subset_1(sK15,k1_zfmisc_1(k2_zfmisc_1(sK13,sK14))) ),
% 2.58/1.01      inference(cnf_transformation,[],[f144]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(c_64,negated_conjecture,
% 2.58/1.01      ( v1_funct_1(sK15) ),
% 2.58/1.01      inference(cnf_transformation,[],[f143]) ).
% 2.58/1.01  
% 2.58/1.01  cnf(contradiction,plain,
% 2.58/1.01      ( $false ),
% 2.58/1.01      inference(minisat,
% 2.58/1.01                [status(thm)],
% 2.58/1.01                [c_13524,c_12892,c_10350,c_10189,c_9616,c_9421,c_9420,
% 2.58/1.01                 c_9284,c_8814,c_1474,c_219,c_201,c_57,c_58,c_59,c_60,
% 2.58/1.01                 c_62,c_63,c_64]) ).
% 2.58/1.01  
% 2.58/1.01  
% 2.58/1.01  % SZS output end CNFRefutation for theBenchmark.p
% 2.58/1.01  
% 2.58/1.01  ------                               Statistics
% 2.58/1.01  
% 2.58/1.01  ------ General
% 2.58/1.01  
% 2.58/1.01  abstr_ref_over_cycles:                  0
% 2.58/1.01  abstr_ref_under_cycles:                 0
% 2.58/1.01  gc_basic_clause_elim:                   0
% 2.58/1.01  forced_gc_time:                         0
% 2.58/1.01  parsing_time:                           0.01
% 2.58/1.01  unif_index_cands_time:                  0.
% 2.58/1.01  unif_index_add_time:                    0.
% 2.58/1.01  orderings_time:                         0.
% 2.58/1.01  out_proof_time:                         0.013
% 2.58/1.01  total_time:                             0.316
% 2.58/1.01  num_of_symbols:                         69
% 2.58/1.01  num_of_terms:                           8154
% 2.58/1.01  
% 2.58/1.01  ------ Preprocessing
% 2.58/1.01  
% 2.58/1.01  num_of_splits:                          1
% 2.58/1.01  num_of_split_atoms:                     1
% 2.58/1.01  num_of_reused_defs:                     0
% 2.58/1.01  num_eq_ax_congr_red:                    124
% 2.58/1.01  num_of_sem_filtered_clauses:            1
% 2.58/1.01  num_of_subtypes:                        0
% 2.58/1.01  monotx_restored_types:                  0
% 2.58/1.01  sat_num_of_epr_types:                   0
% 2.58/1.01  sat_num_of_non_cyclic_types:            0
% 2.58/1.01  sat_guarded_non_collapsed_types:        0
% 2.58/1.01  num_pure_diseq_elim:                    0
% 2.58/1.01  simp_replaced_by:                       0
% 2.58/1.01  res_preprocessed:                       287
% 2.58/1.01  prep_upred:                             0
% 2.58/1.01  prep_unflattend:                        218
% 2.58/1.01  smt_new_axioms:                         0
% 2.58/1.01  pred_elim_cands:                        9
% 2.58/1.01  pred_elim:                              2
% 2.58/1.01  pred_elim_cl:                           2
% 2.58/1.01  pred_elim_cycles:                       13
% 2.58/1.01  merged_defs:                            8
% 2.58/1.01  merged_defs_ncl:                        0
% 2.58/1.01  bin_hyper_res:                          8
% 2.58/1.01  prep_cycles:                            4
% 2.58/1.01  pred_elim_time:                         0.089
% 2.58/1.01  splitting_time:                         0.
% 2.58/1.01  sem_filter_time:                        0.
% 2.58/1.01  monotx_time:                            0.
% 2.58/1.01  subtype_inf_time:                       0.
% 2.58/1.01  
% 2.58/1.01  ------ Problem properties
% 2.58/1.01  
% 2.58/1.01  clauses:                                62
% 2.58/1.01  conjectures:                            7
% 2.58/1.01  epr:                                    9
% 2.58/1.01  horn:                                   42
% 2.58/1.01  ground:                                 14
% 2.58/1.01  unary:                                  9
% 2.58/1.01  binary:                                 18
% 2.58/1.01  lits:                                   165
% 2.58/1.01  lits_eq:                                35
% 2.58/1.01  fd_pure:                                0
% 2.58/1.01  fd_pseudo:                              0
% 2.58/1.01  fd_cond:                                5
% 2.58/1.01  fd_pseudo_cond:                         4
% 2.58/1.01  ac_symbols:                             0
% 2.58/1.01  
% 2.58/1.01  ------ Propositional Solver
% 2.58/1.01  
% 2.58/1.01  prop_solver_calls:                      27
% 2.58/1.01  prop_fast_solver_calls:                 3001
% 2.58/1.01  smt_solver_calls:                       0
% 2.58/1.01  smt_fast_solver_calls:                  0
% 2.58/1.01  prop_num_of_clauses:                    2990
% 2.58/1.01  prop_preprocess_simplified:             11779
% 2.58/1.01  prop_fo_subsumed:                       23
% 2.58/1.01  prop_solver_time:                       0.
% 2.58/1.01  smt_solver_time:                        0.
% 2.58/1.01  smt_fast_solver_time:                   0.
% 2.58/1.01  prop_fast_solver_time:                  0.
% 2.58/1.01  prop_unsat_core_time:                   0.
% 2.58/1.01  
% 2.58/1.01  ------ QBF
% 2.58/1.01  
% 2.58/1.01  qbf_q_res:                              0
% 2.58/1.01  qbf_num_tautologies:                    0
% 2.58/1.01  qbf_prep_cycles:                        0
% 2.58/1.01  
% 2.58/1.01  ------ BMC1
% 2.58/1.01  
% 2.58/1.01  bmc1_current_bound:                     -1
% 2.58/1.01  bmc1_last_solved_bound:                 -1
% 2.58/1.01  bmc1_unsat_core_size:                   -1
% 2.58/1.01  bmc1_unsat_core_parents_size:           -1
% 2.58/1.01  bmc1_merge_next_fun:                    0
% 2.58/1.01  bmc1_unsat_core_clauses_time:           0.
% 2.58/1.01  
% 2.58/1.01  ------ Instantiation
% 2.58/1.01  
% 2.58/1.01  inst_num_of_clauses:                    649
% 2.58/1.01  inst_num_in_passive:                    216
% 2.58/1.01  inst_num_in_active:                     333
% 2.58/1.01  inst_num_in_unprocessed:                99
% 2.58/1.01  inst_num_of_loops:                      434
% 2.58/1.01  inst_num_of_learning_restarts:          0
% 2.58/1.01  inst_num_moves_active_passive:          97
% 2.58/1.01  inst_lit_activity:                      0
% 2.58/1.01  inst_lit_activity_moves:                0
% 2.58/1.01  inst_num_tautologies:                   0
% 2.58/1.01  inst_num_prop_implied:                  0
% 2.58/1.01  inst_num_existing_simplified:           0
% 2.58/1.01  inst_num_eq_res_simplified:             0
% 2.58/1.01  inst_num_child_elim:                    0
% 2.58/1.01  inst_num_of_dismatching_blockings:      95
% 2.58/1.01  inst_num_of_non_proper_insts:           386
% 2.58/1.01  inst_num_of_duplicates:                 0
% 2.58/1.01  inst_inst_num_from_inst_to_res:         0
% 2.58/1.01  inst_dismatching_checking_time:         0.
% 2.58/1.01  
% 2.58/1.01  ------ Resolution
% 2.58/1.01  
% 2.58/1.01  res_num_of_clauses:                     0
% 2.58/1.01  res_num_in_passive:                     0
% 2.58/1.01  res_num_in_active:                      0
% 2.58/1.01  res_num_of_loops:                       291
% 2.58/1.01  res_forward_subset_subsumed:            17
% 2.58/1.01  res_backward_subset_subsumed:           0
% 2.58/1.01  res_forward_subsumed:                   0
% 2.58/1.01  res_backward_subsumed:                  0
% 2.58/1.01  res_forward_subsumption_resolution:     5
% 2.58/1.01  res_backward_subsumption_resolution:    0
% 2.58/1.01  res_clause_to_clause_subsumption:       841
% 2.58/1.01  res_orphan_elimination:                 0
% 2.58/1.01  res_tautology_del:                      42
% 2.58/1.01  res_num_eq_res_simplified:              0
% 2.58/1.01  res_num_sel_changes:                    0
% 2.58/1.01  res_moves_from_active_to_pass:          0
% 2.58/1.01  
% 2.58/1.01  ------ Superposition
% 2.58/1.01  
% 2.58/1.01  sup_time_total:                         0.
% 2.58/1.01  sup_time_generating:                    0.
% 2.58/1.01  sup_time_sim_full:                      0.
% 2.58/1.01  sup_time_sim_immed:                     0.
% 2.58/1.01  
% 2.58/1.01  sup_num_of_clauses:                     205
% 2.58/1.01  sup_num_in_active:                      86
% 2.58/1.01  sup_num_in_passive:                     119
% 2.58/1.01  sup_num_of_loops:                       86
% 2.58/1.01  sup_fw_superposition:                   75
% 2.58/1.01  sup_bw_superposition:                   105
% 2.58/1.01  sup_immediate_simplified:               20
% 2.58/1.01  sup_given_eliminated:                   0
% 2.58/1.01  comparisons_done:                       0
% 2.58/1.01  comparisons_avoided:                    6
% 2.58/1.01  
% 2.58/1.01  ------ Simplifications
% 2.58/1.01  
% 2.58/1.01  
% 2.58/1.01  sim_fw_subset_subsumed:                 4
% 2.58/1.01  sim_bw_subset_subsumed:                 0
% 2.58/1.01  sim_fw_subsumed:                        6
% 2.58/1.01  sim_bw_subsumed:                        0
% 2.58/1.01  sim_fw_subsumption_res:                 0
% 2.58/1.01  sim_bw_subsumption_res:                 0
% 2.58/1.01  sim_tautology_del:                      17
% 2.58/1.01  sim_eq_tautology_del:                   2
% 2.58/1.01  sim_eq_res_simp:                        4
% 2.58/1.01  sim_fw_demodulated:                     0
% 2.58/1.01  sim_bw_demodulated:                     0
% 2.58/1.01  sim_light_normalised:                   13
% 2.58/1.01  sim_joinable_taut:                      0
% 2.58/1.01  sim_joinable_simp:                      0
% 2.58/1.01  sim_ac_normalised:                      0
% 2.58/1.01  sim_smt_subsumption:                    0
% 2.58/1.01  
%------------------------------------------------------------------------------
