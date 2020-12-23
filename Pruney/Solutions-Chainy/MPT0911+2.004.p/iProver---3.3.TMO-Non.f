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
% DateTime   : Thu Dec  3 11:59:01 EST 2020

% Result     : Timeout 59.43s
% Output     : None 
% Verified   : 
% Statistics : Number of formulae       :  136 ( 822 expanded)
%              Number of clauses        :   79 ( 258 expanded)
%              Number of leaves         :   15 ( 172 expanded)
%              Depth                    :   17
%              Number of atoms          :  423 (4277 expanded)
%              Number of equality atoms :  267 (2265 expanded)
%              Maximal formula depth    :   20 (   5 average)
%              Maximal clause size      :   20 (   2 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f19,conjecture,(
    ! [X0,X1,X2,X3,X4] :
      ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
     => ( ! [X5] :
            ( m1_subset_1(X5,X0)
           => ! [X6] :
                ( m1_subset_1(X6,X1)
               => ! [X7] :
                    ( m1_subset_1(X7,X2)
                   => ( k3_mcart_1(X5,X6,X7) = X4
                     => X3 = X7 ) ) ) )
       => ( k7_mcart_1(X0,X1,X2,X4) = X3
          | k1_xboole_0 = X2
          | k1_xboole_0 = X1
          | k1_xboole_0 = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f20,negated_conjecture,(
    ~ ! [X0,X1,X2,X3,X4] :
        ( m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))
       => ( ! [X5] :
              ( m1_subset_1(X5,X0)
             => ! [X6] :
                  ( m1_subset_1(X6,X1)
                 => ! [X7] :
                      ( m1_subset_1(X7,X2)
                     => ( k3_mcart_1(X5,X6,X7) = X4
                       => X3 = X7 ) ) ) )
         => ( k7_mcart_1(X0,X1,X2,X4) = X3
            | k1_xboole_0 = X2
            | k1_xboole_0 = X1
            | k1_xboole_0 = X0 ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f27,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f28,plain,(
    ? [X0,X1,X2,X3,X4] :
      ( k7_mcart_1(X0,X1,X2,X4) != X3
      & k1_xboole_0 != X2
      & k1_xboole_0 != X1
      & k1_xboole_0 != X0
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( X3 = X7
                  | k3_mcart_1(X5,X6,X7) != X4
                  | ~ m1_subset_1(X7,X2) )
              | ~ m1_subset_1(X6,X1) )
          | ~ m1_subset_1(X5,X0) )
      & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) ) ),
    inference(flattening,[],[f27])).

fof(f51,plain,
    ( ? [X0,X1,X2,X3,X4] :
        ( k7_mcart_1(X0,X1,X2,X4) != X3
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0
        & ! [X5] :
            ( ! [X6] :
                ( ! [X7] :
                    ( X3 = X7
                    | k3_mcart_1(X5,X6,X7) != X4
                    | ~ m1_subset_1(X7,X2) )
                | ~ m1_subset_1(X6,X1) )
            | ~ m1_subset_1(X5,X0) )
        & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) )
   => ( k7_mcart_1(sK8,sK9,sK10,sK12) != sK11
      & k1_xboole_0 != sK10
      & k1_xboole_0 != sK9
      & k1_xboole_0 != sK8
      & ! [X5] :
          ( ! [X6] :
              ( ! [X7] :
                  ( sK11 = X7
                  | k3_mcart_1(X5,X6,X7) != sK12
                  | ~ m1_subset_1(X7,sK10) )
              | ~ m1_subset_1(X6,sK9) )
          | ~ m1_subset_1(X5,sK8) )
      & m1_subset_1(sK12,k3_zfmisc_1(sK8,sK9,sK10)) ) ),
    introduced(choice_axiom,[])).

fof(f52,plain,
    ( k7_mcart_1(sK8,sK9,sK10,sK12) != sK11
    & k1_xboole_0 != sK10
    & k1_xboole_0 != sK9
    & k1_xboole_0 != sK8
    & ! [X5] :
        ( ! [X6] :
            ( ! [X7] :
                ( sK11 = X7
                | k3_mcart_1(X5,X6,X7) != sK12
                | ~ m1_subset_1(X7,sK10) )
            | ~ m1_subset_1(X6,sK9) )
        | ~ m1_subset_1(X5,sK8) )
    & m1_subset_1(sK12,k3_zfmisc_1(sK8,sK9,sK10)) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12])],[f28,f51])).

fof(f97,plain,(
    m1_subset_1(sK12,k3_zfmisc_1(sK8,sK9,sK10)) ),
    inference(cnf_transformation,[],[f52])).

fof(f13,axiom,(
    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f83,plain,(
    ! [X2,X0,X1] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f13])).

fof(f122,plain,(
    m1_subset_1(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) ),
    inference(definition_unfolding,[],[f97,f83])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) ) )
      & ( ~ v1_xboole_0(X0)
       => ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( ( m1_subset_1(X1,X0)
        <=> v1_xboole_0(X1) )
        | ~ v1_xboole_0(X0) )
      & ( ( m1_subset_1(X1,X0)
        <=> r2_hidden(X1,X0) )
        | v1_xboole_0(X0) ) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f46,plain,(
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
    inference(nnf_transformation,[],[f21])).

fof(f77,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f11,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f81,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f11])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( r2_hidden(X0,X1)
       => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f23,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f86,plain,(
    ! [X0,X1] :
      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f99,plain,(
    k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f52])).

fof(f100,plain,(
    k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,(
    k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f52])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 )
    <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( ( k1_xboole_0 != X2
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0 )
        | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) )
      & ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
        | k1_xboole_0 = X2
        | k1_xboole_0 = X1
        | k1_xboole_0 = X0 ) ) ),
    inference(flattening,[],[f49])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k3_zfmisc_1(X0,X1,X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f50])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f90,f83])).

fof(f16,axiom,(
    ! [X0] :
      ~ ( ! [X1] :
            ~ ( ! [X2,X3,X4,X5] :
                  ~ ( k4_mcart_1(X2,X3,X4,X5) = X1
                    & ( r2_hidden(X3,X0)
                      | r2_hidden(X2,X0) ) )
              & r2_hidden(X1,X0) )
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f25,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f16])).

fof(f47,plain,(
    ! [X0] :
      ( ? [X1] :
          ( ! [X2,X3,X4,X5] :
              ( k4_mcart_1(X2,X3,X4,X5) != X1
              | ( ~ r2_hidden(X3,X0)
                & ~ r2_hidden(X2,X0) ) )
          & r2_hidden(X1,X0) )
     => ( ! [X5,X4,X3,X2] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK7(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK7(X0),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f48,plain,(
    ! [X0] :
      ( ( ! [X2,X3,X4,X5] :
            ( k4_mcart_1(X2,X3,X4,X5) != sK7(X0)
            | ( ~ r2_hidden(X3,X0)
              & ~ r2_hidden(X2,X0) ) )
        & r2_hidden(sK7(X0),X0) )
      | k1_xboole_0 = X0 ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f25,f47])).

fof(f87,plain,(
    ! [X0] :
      ( r2_hidden(sK7(X0),X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f48])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X1] : ~ r2_hidden(X1,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | ? [X1] : r2_hidden(X1,X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(rectify,[],[f29])).

fof(f31,plain,(
    ! [X0] :
      ( ? [X1] : r2_hidden(X1,X0)
     => r2_hidden(sK0(X0),X0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_xboole_0(X0)
        | r2_hidden(sK0(X0),X0) )
      & ( ! [X2] : ~ r2_hidden(X2,X0)
        | ~ v1_xboole_0(X0) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).

fof(f53,plain,(
    ! [X2,X0] :
      ( ~ r2_hidden(X2,X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( r2_hidden(X0,k2_zfmisc_1(X1,X2))
     => ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(k2_mcart_1(X0),X2)
        & r2_hidden(k1_mcart_1(X0),X1) )
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k1_mcart_1(X0),X1)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f98,plain,(
    ! [X6,X7,X5] :
      ( sK11 = X7
      | k3_mcart_1(X5,X6,X7) != sK12
      | ~ m1_subset_1(X7,sK10)
      | ~ m1_subset_1(X6,sK9)
      | ~ m1_subset_1(X5,sK8) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f12,axiom,(
    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f82,plain,(
    ! [X2,X0,X1] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2) ),
    inference(cnf_transformation,[],[f12])).

fof(f121,plain,(
    ! [X6,X7,X5] :
      ( sK11 = X7
      | k4_tarski(k4_tarski(X5,X6),X7) != sK12
      | ~ m1_subset_1(X7,sK10)
      | ~ m1_subset_1(X6,sK9)
      | ~ m1_subset_1(X5,sK8) ) ),
    inference(definition_unfolding,[],[f98,f82])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(k2_mcart_1(X0),X2)
      | ~ r2_hidden(X0,k2_zfmisc_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f78,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X1,X0)
      | ~ r2_hidden(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ~ ( ~ ! [X3] :
              ( m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
             => ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
                & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
                & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) ) )
        & k1_xboole_0 != X2
        & k1_xboole_0 != X1
        & k1_xboole_0 != X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
            & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3)
            & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3) )
          | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) )
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(ennf_transformation,[],[f18])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3)
      | ~ m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2))
      | k1_xboole_0 = X2
      | k1_xboole_0 = X1
      | k1_xboole_0 = X0 ) ),
    inference(definition_unfolding,[],[f96,f83])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 != X0
      | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) ) ),
    inference(definition_unfolding,[],[f91,f83])).

fof(f135,plain,(
    ! [X2,X1] : k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2) ),
    inference(equality_resolution,[],[f116])).

fof(f102,plain,(
    k7_mcart_1(sK8,sK9,sK10,sK12) != sK11 ),
    inference(cnf_transformation,[],[f52])).

cnf(c_45,negated_conjecture,
    ( m1_subset_1(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) ),
    inference(cnf_transformation,[],[f122])).

cnf(c_1183,plain,
    ( m1_subset_1(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_45])).

cnf(c_25,plain,
    ( ~ m1_subset_1(X0,X1)
    | r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f77])).

cnf(c_1193,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | r2_hidden(X0,X1) = iProver_top
    | v1_xboole_0(X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_25])).

cnf(c_3788,plain,
    ( r2_hidden(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1193])).

cnf(c_26,plain,
    ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f81])).

cnf(c_29,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_relat_1(X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f86])).

cnf(c_420,plain,
    ( ~ r2_hidden(X0,X1)
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | k2_zfmisc_1(X2,X3) != X1 ),
    inference(resolution_lifted,[status(thm)],[c_26,c_29])).

cnf(c_421,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
    inference(unflattening,[status(thm)],[c_420])).

cnf(c_1181,plain,
    ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
    | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_421])).

cnf(c_3915,plain,
    ( k4_tarski(k1_mcart_1(sK12),k2_mcart_1(sK12)) = sK12
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3788,c_1181])).

cnf(c_23,plain,
    ( ~ m1_subset_1(X0,X1)
    | ~ v1_xboole_0(X1)
    | v1_xboole_0(X0) ),
    inference(cnf_transformation,[],[f79])).

cnf(c_1194,plain,
    ( m1_subset_1(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top
    | v1_xboole_0(X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_23])).

cnf(c_3794,plain,
    ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) != iProver_top
    | v1_xboole_0(sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_1183,c_1194])).

cnf(c_4059,plain,
    ( k4_tarski(k1_mcart_1(sK12),k2_mcart_1(sK12)) = sK12
    | v1_xboole_0(sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_3915,c_3794])).

cnf(c_43,negated_conjecture,
    ( k1_xboole_0 != sK8 ),
    inference(cnf_transformation,[],[f99])).

cnf(c_42,negated_conjecture,
    ( k1_xboole_0 != sK9 ),
    inference(cnf_transformation,[],[f100])).

cnf(c_41,negated_conjecture,
    ( k1_xboole_0 != sK10 ),
    inference(cnf_transformation,[],[f101])).

cnf(c_36,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X2
    | k1_xboole_0 = X1 ),
    inference(cnf_transformation,[],[f117])).

cnf(c_1321,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK8,X0),X1) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_1627,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),X0) != k1_xboole_0
    | k1_xboole_0 = X0
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_1321])).

cnf(c_2145,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) != k1_xboole_0
    | k1_xboole_0 = sK10
    | k1_xboole_0 = sK9
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_1627])).

cnf(c_32,plain,
    ( r2_hidden(sK7(X0),X0)
    | k1_xboole_0 = X0 ),
    inference(cnf_transformation,[],[f87])).

cnf(c_1188,plain,
    ( k1_xboole_0 = X0
    | r2_hidden(sK7(X0),X0) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_32])).

cnf(c_1,plain,
    ( ~ r2_hidden(X0,X1)
    | ~ v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f53])).

cnf(c_1213,plain,
    ( r2_hidden(X0,X1) != iProver_top
    | v1_xboole_0(X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_1])).

cnf(c_3256,plain,
    ( k1_xboole_0 = X0
    | v1_xboole_0(X0) != iProver_top ),
    inference(superposition,[status(thm)],[c_1188,c_1213])).

cnf(c_4058,plain,
    ( k4_tarski(k1_mcart_1(sK12),k2_mcart_1(sK12)) = sK12
    | k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_3915,c_3256])).

cnf(c_4150,plain,
    ( k4_tarski(k1_mcart_1(sK12),k2_mcart_1(sK12)) = sK12 ),
    inference(global_propositional_subsumption,[status(thm)],[c_4059,c_43,c_42,c_41,c_2145,c_4058])).

cnf(c_28,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k1_mcart_1(X0),X1) ),
    inference(cnf_transformation,[],[f84])).

cnf(c_1191,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_28])).

cnf(c_3914,plain,
    ( r2_hidden(k1_mcart_1(sK12),k2_zfmisc_1(sK8,sK9)) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3788,c_1191])).

cnf(c_4799,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK12)),k2_mcart_1(k1_mcart_1(sK12))) = k1_mcart_1(sK12)
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3914,c_1181])).

cnf(c_120524,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK12)),k2_mcart_1(k1_mcart_1(sK12))) = k1_mcart_1(sK12)
    | v1_xboole_0(sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_4799,c_3794])).

cnf(c_120521,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK12)),k2_mcart_1(k1_mcart_1(sK12))) = k1_mcart_1(sK12)
    | k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_4799,c_3256])).

cnf(c_122143,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1(sK12)),k2_mcart_1(k1_mcart_1(sK12))) = k1_mcart_1(sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_120524,c_43,c_42,c_41,c_2145,c_120521])).

cnf(c_44,negated_conjecture,
    ( ~ m1_subset_1(X0,sK10)
    | ~ m1_subset_1(X1,sK9)
    | ~ m1_subset_1(X2,sK8)
    | k4_tarski(k4_tarski(X2,X1),X0) != sK12
    | sK11 = X0 ),
    inference(cnf_transformation,[],[f121])).

cnf(c_1184,plain,
    ( k4_tarski(k4_tarski(X0,X1),X2) != sK12
    | sK11 = X2
    | m1_subset_1(X2,sK10) != iProver_top
    | m1_subset_1(X1,sK9) != iProver_top
    | m1_subset_1(X0,sK8) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_44])).

cnf(c_122148,plain,
    ( k4_tarski(k1_mcart_1(sK12),X0) != sK12
    | sK11 = X0
    | m1_subset_1(X0,sK10) != iProver_top
    | m1_subset_1(k1_mcart_1(k1_mcart_1(sK12)),sK8) != iProver_top
    | m1_subset_1(k2_mcart_1(k1_mcart_1(sK12)),sK9) != iProver_top ),
    inference(superposition,[status(thm)],[c_122143,c_1184])).

cnf(c_27,plain,
    ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
    | r2_hidden(k2_mcart_1(X0),X2) ),
    inference(cnf_transformation,[],[f85])).

cnf(c_1192,plain,
    ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
    | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_27])).

cnf(c_4797,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK12)),sK9) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3914,c_1192])).

cnf(c_5454,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK12)),sK9) = iProver_top
    | v1_xboole_0(sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_4797,c_3794])).

cnf(c_5453,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0
    | r2_hidden(k2_mcart_1(k1_mcart_1(sK12)),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_4797,c_3256])).

cnf(c_5458,plain,
    ( r2_hidden(k2_mcart_1(k1_mcart_1(sK12)),sK9) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_5454,c_43,c_42,c_41,c_2145,c_5453])).

cnf(c_24,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1)
    | v1_xboole_0(X1) ),
    inference(cnf_transformation,[],[f78])).

cnf(c_228,plain,
    ( ~ r2_hidden(X0,X1)
    | m1_subset_1(X0,X1) ),
    inference(global_propositional_subsumption,[status(thm)],[c_24,c_1])).

cnf(c_229,plain,
    ( m1_subset_1(X0,X1)
    | ~ r2_hidden(X0,X1) ),
    inference(renaming,[status(thm)],[c_228])).

cnf(c_1182,plain,
    ( m1_subset_1(X0,X1) = iProver_top
    | r2_hidden(X0,X1) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_229])).

cnf(c_5463,plain,
    ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK12)),sK9) = iProver_top ),
    inference(superposition,[status(thm)],[c_5458,c_1182])).

cnf(c_4798,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK12)),sK8) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3914,c_1191])).

cnf(c_117066,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK12)),sK8) = iProver_top
    | v1_xboole_0(sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_4798,c_3794])).

cnf(c_117063,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0
    | r2_hidden(k1_mcart_1(k1_mcart_1(sK12)),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_4798,c_3256])).

cnf(c_118362,plain,
    ( r2_hidden(k1_mcart_1(k1_mcart_1(sK12)),sK8) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_117066,c_43,c_42,c_41,c_2145,c_117063])).

cnf(c_118367,plain,
    ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK12)),sK8) = iProver_top ),
    inference(superposition,[status(thm)],[c_118362,c_1182])).

cnf(c_122158,plain,
    ( k4_tarski(k1_mcart_1(sK12),X0) != sK12
    | sK11 = X0
    | m1_subset_1(X0,sK10) != iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_122148,c_5463,c_118367])).

cnf(c_122164,plain,
    ( k2_mcart_1(sK12) = sK11
    | m1_subset_1(k2_mcart_1(sK12),sK10) != iProver_top ),
    inference(superposition,[status(thm)],[c_4150,c_122158])).

cnf(c_37,plain,
    ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
    | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
    | k1_xboole_0 = X1
    | k1_xboole_0 = X3
    | k1_xboole_0 = X2 ),
    inference(cnf_transformation,[],[f118])).

cnf(c_1187,plain,
    ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
    | k1_xboole_0 = X0
    | k1_xboole_0 = X1
    | k1_xboole_0 = X2
    | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
    inference(predicate_to_equality,[status(thm)],[c_37])).

cnf(c_4293,plain,
    ( k7_mcart_1(sK8,sK9,sK10,sK12) = k2_mcart_1(sK12)
    | sK10 = k1_xboole_0
    | sK9 = k1_xboole_0
    | sK8 = k1_xboole_0 ),
    inference(superposition,[status(thm)],[c_1183,c_1187])).

cnf(c_59,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != k1_xboole_0
    | k1_xboole_0 = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_36])).

cnf(c_35,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) = k1_xboole_0 ),
    inference(cnf_transformation,[],[f135])).

cnf(c_60,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_35])).

cnf(c_666,plain,
    ( X0 != X1
    | X2 != X1
    | X2 = X0 ),
    theory(equality)).

cnf(c_1282,plain,
    ( sK10 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK10 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_1283,plain,
    ( sK10 != k1_xboole_0
    | k1_xboole_0 = sK10
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1282])).

cnf(c_1316,plain,
    ( sK9 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK9 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_1317,plain,
    ( sK9 != k1_xboole_0
    | k1_xboole_0 = sK9
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1316])).

cnf(c_1342,plain,
    ( sK8 != X0
    | k1_xboole_0 != X0
    | k1_xboole_0 = sK8 ),
    inference(instantiation,[status(thm)],[c_666])).

cnf(c_1343,plain,
    ( sK8 != k1_xboole_0
    | k1_xboole_0 = sK8
    | k1_xboole_0 != k1_xboole_0 ),
    inference(instantiation,[status(thm)],[c_1342])).

cnf(c_4743,plain,
    ( k7_mcart_1(sK8,sK9,sK10,sK12) = k2_mcart_1(sK12) ),
    inference(global_propositional_subsumption,[status(thm)],[c_4293,c_43,c_42,c_41,c_59,c_60,c_1283,c_1317,c_1343])).

cnf(c_40,negated_conjecture,
    ( k7_mcart_1(sK8,sK9,sK10,sK12) != sK11 ),
    inference(cnf_transformation,[],[f102])).

cnf(c_4745,plain,
    ( k2_mcart_1(sK12) != sK11 ),
    inference(demodulation,[status(thm)],[c_4743,c_40])).

cnf(c_3913,plain,
    ( r2_hidden(k2_mcart_1(sK12),sK10) = iProver_top
    | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
    inference(superposition,[status(thm)],[c_3788,c_1192])).

cnf(c_3983,plain,
    ( r2_hidden(k2_mcart_1(sK12),sK10) = iProver_top
    | v1_xboole_0(sK12) = iProver_top ),
    inference(superposition,[status(thm)],[c_3913,c_3794])).

cnf(c_3982,plain,
    ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0
    | r2_hidden(k2_mcart_1(sK12),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_3913,c_3256])).

cnf(c_4049,plain,
    ( r2_hidden(k2_mcart_1(sK12),sK10) = iProver_top ),
    inference(global_propositional_subsumption,[status(thm)],[c_3983,c_43,c_42,c_41,c_2145,c_3982])).

cnf(c_4054,plain,
    ( m1_subset_1(k2_mcart_1(sK12),sK10) = iProver_top ),
    inference(superposition,[status(thm)],[c_4049,c_1182])).

cnf(contradiction,plain,
    ( $false ),
    inference(minisat,[status(thm)],[c_122164,c_4745,c_4054])).

%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.11  % Command    : iproveropt_run.sh %d %s
% 0.10/0.30  % Computer   : n022.cluster.edu
% 0.10/0.30  % Model      : x86_64 x86_64
% 0.10/0.30  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.30  % Memory     : 8042.1875MB
% 0.10/0.30  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.30  % CPULimit   : 60
% 0.10/0.30  % WCLimit    : 600
% 0.10/0.30  % DateTime   : Tue Dec  1 12:21:11 EST 2020
% 0.10/0.30  % CPUTime    : 
% 0.10/0.31  % Running in FOF mode
% 59.43/7.97  % SZS status Started for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 59.43/7.97  
% 59.43/7.97  %---------------- iProver v3.3 (CASC-J10 2020) ----------------%
% 59.43/7.97  
% 59.43/7.97  ------  iProver source info
% 59.43/7.97  
% 59.43/7.97  git: date: 2020-06-30 10:37:57 +0100
% 59.43/7.97  git: sha1: e3013b43002810b07ddde22341e87fe21d0d6388
% 59.43/7.97  git: non_committed_changes: false
% 59.43/7.97  git: last_make_outside_of_git: false
% 59.43/7.97  
% 59.43/7.97  ------ 
% 59.43/7.97  
% 59.43/7.97  ------ Input Options
% 59.43/7.97  
% 59.43/7.97  --out_options                           all
% 59.43/7.97  --tptp_safe_out                         true
% 59.43/7.97  --problem_path                          ""
% 59.43/7.97  --include_path                          ""
% 59.43/7.97  --clausifier                            res/vclausify_rel
% 59.43/7.97  --clausifier_options                    ""
% 59.43/7.97  --stdin                                 false
% 59.43/7.97  --stats_out                             all
% 59.43/7.97  
% 59.43/7.97  ------ General Options
% 59.43/7.97  
% 59.43/7.97  --fof                                   false
% 59.43/7.97  --time_out_real                         305.
% 59.43/7.97  --time_out_virtual                      -1.
% 59.43/7.97  --symbol_type_check                     false
% 59.43/7.97  --clausify_out                          false
% 59.43/7.97  --sig_cnt_out                           false
% 59.43/7.97  --trig_cnt_out                          false
% 59.43/7.97  --trig_cnt_out_tolerance                1.
% 59.43/7.97  --trig_cnt_out_sk_spl                   false
% 59.43/7.97  --abstr_cl_out                          false
% 59.43/7.97  
% 59.43/7.97  ------ Global Options
% 59.43/7.97  
% 59.43/7.97  --schedule                              default
% 59.43/7.97  --add_important_lit                     false
% 59.43/7.97  --prop_solver_per_cl                    1000
% 59.43/7.97  --min_unsat_core                        false
% 59.43/7.97  --soft_assumptions                      false
% 59.43/7.97  --soft_lemma_size                       3
% 59.43/7.97  --prop_impl_unit_size                   0
% 59.43/7.97  --prop_impl_unit                        []
% 59.43/7.97  --share_sel_clauses                     true
% 59.43/7.97  --reset_solvers                         false
% 59.43/7.97  --bc_imp_inh                            [conj_cone]
% 59.43/7.97  --conj_cone_tolerance                   3.
% 59.43/7.97  --extra_neg_conj                        none
% 59.43/7.97  --large_theory_mode                     true
% 59.43/7.97  --prolific_symb_bound                   200
% 59.43/7.97  --lt_threshold                          2000
% 59.43/7.97  --clause_weak_htbl                      true
% 59.43/7.97  --gc_record_bc_elim                     false
% 59.43/7.97  
% 59.43/7.97  ------ Preprocessing Options
% 59.43/7.97  
% 59.43/7.97  --preprocessing_flag                    true
% 59.43/7.97  --time_out_prep_mult                    0.1
% 59.43/7.97  --splitting_mode                        input
% 59.43/7.97  --splitting_grd                         true
% 59.43/7.97  --splitting_cvd                         false
% 59.43/7.97  --splitting_cvd_svl                     false
% 59.43/7.97  --splitting_nvd                         32
% 59.43/7.97  --sub_typing                            true
% 59.43/7.97  --prep_gs_sim                           true
% 59.43/7.97  --prep_unflatten                        true
% 59.43/7.97  --prep_res_sim                          true
% 59.43/7.97  --prep_upred                            true
% 59.43/7.97  --prep_sem_filter                       exhaustive
% 59.43/7.97  --prep_sem_filter_out                   false
% 59.43/7.97  --pred_elim                             true
% 59.43/7.97  --res_sim_input                         true
% 59.43/7.97  --eq_ax_congr_red                       true
% 59.43/7.97  --pure_diseq_elim                       true
% 59.43/7.97  --brand_transform                       false
% 59.43/7.97  --non_eq_to_eq                          false
% 59.43/7.97  --prep_def_merge                        true
% 59.43/7.97  --prep_def_merge_prop_impl              false
% 59.43/7.97  --prep_def_merge_mbd                    true
% 59.43/7.97  --prep_def_merge_tr_red                 false
% 59.43/7.97  --prep_def_merge_tr_cl                  false
% 59.43/7.97  --smt_preprocessing                     true
% 59.43/7.97  --smt_ac_axioms                         fast
% 59.43/7.97  --preprocessed_out                      false
% 59.43/7.97  --preprocessed_stats                    false
% 59.43/7.97  
% 59.43/7.97  ------ Abstraction refinement Options
% 59.43/7.97  
% 59.43/7.97  --abstr_ref                             []
% 59.43/7.97  --abstr_ref_prep                        false
% 59.43/7.97  --abstr_ref_until_sat                   false
% 59.43/7.97  --abstr_ref_sig_restrict                funpre
% 59.43/7.97  --abstr_ref_af_restrict_to_split_sk     false
% 59.43/7.97  --abstr_ref_under                       []
% 59.43/7.97  
% 59.43/7.97  ------ SAT Options
% 59.43/7.97  
% 59.43/7.97  --sat_mode                              false
% 59.43/7.97  --sat_fm_restart_options                ""
% 59.43/7.97  --sat_gr_def                            false
% 59.43/7.97  --sat_epr_types                         true
% 59.43/7.97  --sat_non_cyclic_types                  false
% 59.43/7.97  --sat_finite_models                     false
% 59.43/7.97  --sat_fm_lemmas                         false
% 59.43/7.97  --sat_fm_prep                           false
% 59.43/7.97  --sat_fm_uc_incr                        true
% 59.43/7.97  --sat_out_model                         small
% 59.43/7.97  --sat_out_clauses                       false
% 59.43/7.97  
% 59.43/7.97  ------ QBF Options
% 59.43/7.97  
% 59.43/7.97  --qbf_mode                              false
% 59.43/7.97  --qbf_elim_univ                         false
% 59.43/7.97  --qbf_dom_inst                          none
% 59.43/7.97  --qbf_dom_pre_inst                      false
% 59.43/7.97  --qbf_sk_in                             false
% 59.43/7.97  --qbf_pred_elim                         true
% 59.43/7.97  --qbf_split                             512
% 59.43/7.97  
% 59.43/7.97  ------ BMC1 Options
% 59.43/7.97  
% 59.43/7.97  --bmc1_incremental                      false
% 59.43/7.97  --bmc1_axioms                           reachable_all
% 59.43/7.97  --bmc1_min_bound                        0
% 59.43/7.97  --bmc1_max_bound                        -1
% 59.43/7.97  --bmc1_max_bound_default                -1
% 59.43/7.97  --bmc1_symbol_reachability              true
% 59.43/7.97  --bmc1_property_lemmas                  false
% 59.43/7.97  --bmc1_k_induction                      false
% 59.43/7.97  --bmc1_non_equiv_states                 false
% 59.43/7.97  --bmc1_deadlock                         false
% 59.43/7.97  --bmc1_ucm                              false
% 59.43/7.97  --bmc1_add_unsat_core                   none
% 59.43/7.97  --bmc1_unsat_core_children              false
% 59.43/7.97  --bmc1_unsat_core_extrapolate_axioms    false
% 59.43/7.97  --bmc1_out_stat                         full
% 59.43/7.97  --bmc1_ground_init                      false
% 59.43/7.97  --bmc1_pre_inst_next_state              false
% 59.43/7.97  --bmc1_pre_inst_state                   false
% 59.43/7.97  --bmc1_pre_inst_reach_state             false
% 59.43/7.97  --bmc1_out_unsat_core                   false
% 59.43/7.97  --bmc1_aig_witness_out                  false
% 59.43/7.97  --bmc1_verbose                          false
% 59.43/7.97  --bmc1_dump_clauses_tptp                false
% 59.43/7.97  --bmc1_dump_unsat_core_tptp             false
% 59.43/7.97  --bmc1_dump_file                        -
% 59.43/7.97  --bmc1_ucm_expand_uc_limit              128
% 59.43/7.97  --bmc1_ucm_n_expand_iterations          6
% 59.43/7.97  --bmc1_ucm_extend_mode                  1
% 59.43/7.97  --bmc1_ucm_init_mode                    2
% 59.43/7.97  --bmc1_ucm_cone_mode                    none
% 59.43/7.97  --bmc1_ucm_reduced_relation_type        0
% 59.43/7.97  --bmc1_ucm_relax_model                  4
% 59.43/7.97  --bmc1_ucm_full_tr_after_sat            true
% 59.43/7.97  --bmc1_ucm_expand_neg_assumptions       false
% 59.43/7.97  --bmc1_ucm_layered_model                none
% 59.43/7.97  --bmc1_ucm_max_lemma_size               10
% 59.43/7.97  
% 59.43/7.97  ------ AIG Options
% 59.43/7.97  
% 59.43/7.97  --aig_mode                              false
% 59.43/7.97  
% 59.43/7.97  ------ Instantiation Options
% 59.43/7.97  
% 59.43/7.97  --instantiation_flag                    true
% 59.43/7.97  --inst_sos_flag                         true
% 59.43/7.97  --inst_sos_phase                        true
% 59.43/7.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.43/7.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.43/7.97  --inst_lit_sel_side                     num_symb
% 59.43/7.97  --inst_solver_per_active                1400
% 59.43/7.97  --inst_solver_calls_frac                1.
% 59.43/7.97  --inst_passive_queue_type               priority_queues
% 59.43/7.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.43/7.97  --inst_passive_queues_freq              [25;2]
% 59.43/7.97  --inst_dismatching                      true
% 59.43/7.97  --inst_eager_unprocessed_to_passive     true
% 59.43/7.97  --inst_prop_sim_given                   true
% 59.43/7.97  --inst_prop_sim_new                     false
% 59.43/7.97  --inst_subs_new                         false
% 59.43/7.97  --inst_eq_res_simp                      false
% 59.43/7.97  --inst_subs_given                       false
% 59.43/7.97  --inst_orphan_elimination               true
% 59.43/7.97  --inst_learning_loop_flag               true
% 59.43/7.97  --inst_learning_start                   3000
% 59.43/7.97  --inst_learning_factor                  2
% 59.43/7.97  --inst_start_prop_sim_after_learn       3
% 59.43/7.97  --inst_sel_renew                        solver
% 59.43/7.97  --inst_lit_activity_flag                true
% 59.43/7.97  --inst_restr_to_given                   false
% 59.43/7.97  --inst_activity_threshold               500
% 59.43/7.97  --inst_out_proof                        true
% 59.43/7.97  
% 59.43/7.97  ------ Resolution Options
% 59.43/7.97  
% 59.43/7.97  --resolution_flag                       true
% 59.43/7.97  --res_lit_sel                           adaptive
% 59.43/7.97  --res_lit_sel_side                      none
% 59.43/7.97  --res_ordering                          kbo
% 59.43/7.97  --res_to_prop_solver                    active
% 59.43/7.97  --res_prop_simpl_new                    false
% 59.43/7.97  --res_prop_simpl_given                  true
% 59.43/7.97  --res_passive_queue_type                priority_queues
% 59.43/7.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.43/7.97  --res_passive_queues_freq               [15;5]
% 59.43/7.97  --res_forward_subs                      full
% 59.43/7.97  --res_backward_subs                     full
% 59.43/7.97  --res_forward_subs_resolution           true
% 59.43/7.97  --res_backward_subs_resolution          true
% 59.43/7.97  --res_orphan_elimination                true
% 59.43/7.97  --res_time_limit                        2.
% 59.43/7.97  --res_out_proof                         true
% 59.43/7.97  
% 59.43/7.97  ------ Superposition Options
% 59.43/7.97  
% 59.43/7.97  --superposition_flag                    true
% 59.43/7.97  --sup_passive_queue_type                priority_queues
% 59.43/7.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.43/7.97  --sup_passive_queues_freq               [8;1;4]
% 59.43/7.97  --demod_completeness_check              fast
% 59.43/7.97  --demod_use_ground                      true
% 59.43/7.97  --sup_to_prop_solver                    passive
% 59.43/7.97  --sup_prop_simpl_new                    true
% 59.43/7.97  --sup_prop_simpl_given                  true
% 59.43/7.97  --sup_fun_splitting                     true
% 59.43/7.97  --sup_smt_interval                      50000
% 59.43/7.97  
% 59.43/7.97  ------ Superposition Simplification Setup
% 59.43/7.97  
% 59.43/7.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.43/7.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.43/7.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.43/7.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.43/7.97  --sup_full_triv                         [TrivRules;PropSubs]
% 59.43/7.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.43/7.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.43/7.97  --sup_immed_triv                        [TrivRules]
% 59.43/7.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.43/7.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.43/7.97  --sup_immed_bw_main                     []
% 59.43/7.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.43/7.97  --sup_input_triv                        [Unflattening;TrivRules]
% 59.43/7.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.43/7.97  --sup_input_bw                          []
% 59.43/7.97  
% 59.43/7.97  ------ Combination Options
% 59.43/7.97  
% 59.43/7.97  --comb_res_mult                         3
% 59.43/7.97  --comb_sup_mult                         2
% 59.43/7.97  --comb_inst_mult                        10
% 59.43/7.97  
% 59.43/7.97  ------ Debug Options
% 59.43/7.97  
% 59.43/7.97  --dbg_backtrace                         false
% 59.43/7.97  --dbg_dump_prop_clauses                 false
% 59.43/7.97  --dbg_dump_prop_clauses_file            -
% 59.43/7.97  --dbg_out_stat                          false
% 59.43/7.97  ------ Parsing...
% 59.43/7.97  ------ Clausification by vclausify_rel  & Parsing by iProver...
% 59.43/7.97  
% 59.43/7.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  pe_s  pe:1:0s pe_e  sf_s  rm: 2 0s  sf_e  pe_s  pe_e 
% 59.43/7.97  
% 59.43/7.97  ------ Preprocessing... gs_s  sp: 0 0s  gs_e  snvd_s sp: 0 0s snvd_e 
% 59.43/7.97  
% 59.43/7.97  ------ Preprocessing... sf_s  rm: 1 0s  sf_e  sf_s  rm: 0 0s  sf_e 
% 59.43/7.97  ------ Proving...
% 59.43/7.97  ------ Problem Properties 
% 59.43/7.97  
% 59.43/7.97  
% 59.43/7.97  clauses                                 45
% 59.43/7.97  conjectures                             6
% 59.43/7.97  EPR                                     8
% 59.43/7.97  Horn                                    32
% 59.43/7.97  unary                                   13
% 59.43/7.97  binary                                  12
% 59.43/7.97  lits                                    109
% 59.43/7.97  lits eq                                 53
% 59.43/7.97  fd_pure                                 0
% 59.43/7.97  fd_pseudo                               0
% 59.43/7.97  fd_cond                                 8
% 59.43/7.97  fd_pseudo_cond                          7
% 59.43/7.97  AC symbols                              0
% 59.43/7.97  
% 59.43/7.97  ------ Schedule dynamic 5 is on 
% 59.43/7.97  
% 59.43/7.97  ------ Input Options "--resolution_flag false --inst_lit_sel_side none" Time Limit: 10.
% 59.43/7.97  
% 59.43/7.97  
% 59.43/7.97  ------ 
% 59.43/7.97  Current options:
% 59.43/7.97  ------ 
% 59.43/7.97  
% 59.43/7.97  ------ Input Options
% 59.43/7.97  
% 59.43/7.97  --out_options                           all
% 59.43/7.97  --tptp_safe_out                         true
% 59.43/7.97  --problem_path                          ""
% 59.43/7.97  --include_path                          ""
% 59.43/7.97  --clausifier                            res/vclausify_rel
% 59.43/7.97  --clausifier_options                    ""
% 59.43/7.97  --stdin                                 false
% 59.43/7.97  --stats_out                             all
% 59.43/7.97  
% 59.43/7.97  ------ General Options
% 59.43/7.97  
% 59.43/7.97  --fof                                   false
% 59.43/7.97  --time_out_real                         305.
% 59.43/7.97  --time_out_virtual                      -1.
% 59.43/7.97  --symbol_type_check                     false
% 59.43/7.97  --clausify_out                          false
% 59.43/7.97  --sig_cnt_out                           false
% 59.43/7.97  --trig_cnt_out                          false
% 59.43/7.97  --trig_cnt_out_tolerance                1.
% 59.43/7.97  --trig_cnt_out_sk_spl                   false
% 59.43/7.97  --abstr_cl_out                          false
% 59.43/7.97  
% 59.43/7.97  ------ Global Options
% 59.43/7.97  
% 59.43/7.97  --schedule                              default
% 59.43/7.97  --add_important_lit                     false
% 59.43/7.97  --prop_solver_per_cl                    1000
% 59.43/7.97  --min_unsat_core                        false
% 59.43/7.97  --soft_assumptions                      false
% 59.43/7.97  --soft_lemma_size                       3
% 59.43/7.97  --prop_impl_unit_size                   0
% 59.43/7.97  --prop_impl_unit                        []
% 59.43/7.97  --share_sel_clauses                     true
% 59.43/7.97  --reset_solvers                         false
% 59.43/7.97  --bc_imp_inh                            [conj_cone]
% 59.43/7.97  --conj_cone_tolerance                   3.
% 59.43/7.97  --extra_neg_conj                        none
% 59.43/7.97  --large_theory_mode                     true
% 59.43/7.97  --prolific_symb_bound                   200
% 59.43/7.97  --lt_threshold                          2000
% 59.43/7.97  --clause_weak_htbl                      true
% 59.43/7.97  --gc_record_bc_elim                     false
% 59.43/7.97  
% 59.43/7.97  ------ Preprocessing Options
% 59.43/7.97  
% 59.43/7.97  --preprocessing_flag                    true
% 59.43/7.97  --time_out_prep_mult                    0.1
% 59.43/7.97  --splitting_mode                        input
% 59.43/7.97  --splitting_grd                         true
% 59.43/7.97  --splitting_cvd                         false
% 59.43/7.97  --splitting_cvd_svl                     false
% 59.43/7.97  --splitting_nvd                         32
% 59.43/7.97  --sub_typing                            true
% 59.43/7.97  --prep_gs_sim                           true
% 59.43/7.97  --prep_unflatten                        true
% 59.43/7.97  --prep_res_sim                          true
% 59.43/7.97  --prep_upred                            true
% 59.43/7.97  --prep_sem_filter                       exhaustive
% 59.43/7.97  --prep_sem_filter_out                   false
% 59.43/7.97  --pred_elim                             true
% 59.43/7.97  --res_sim_input                         true
% 59.43/7.97  --eq_ax_congr_red                       true
% 59.43/7.97  --pure_diseq_elim                       true
% 59.43/7.97  --brand_transform                       false
% 59.43/7.97  --non_eq_to_eq                          false
% 59.43/7.97  --prep_def_merge                        true
% 59.43/7.97  --prep_def_merge_prop_impl              false
% 59.43/7.97  --prep_def_merge_mbd                    true
% 59.43/7.97  --prep_def_merge_tr_red                 false
% 59.43/7.97  --prep_def_merge_tr_cl                  false
% 59.43/7.97  --smt_preprocessing                     true
% 59.43/7.97  --smt_ac_axioms                         fast
% 59.43/7.97  --preprocessed_out                      false
% 59.43/7.97  --preprocessed_stats                    false
% 59.43/7.97  
% 59.43/7.97  ------ Abstraction refinement Options
% 59.43/7.97  
% 59.43/7.97  --abstr_ref                             []
% 59.43/7.97  --abstr_ref_prep                        false
% 59.43/7.97  --abstr_ref_until_sat                   false
% 59.43/7.97  --abstr_ref_sig_restrict                funpre
% 59.43/7.97  --abstr_ref_af_restrict_to_split_sk     false
% 59.43/7.97  --abstr_ref_under                       []
% 59.43/7.97  
% 59.43/7.97  ------ SAT Options
% 59.43/7.97  
% 59.43/7.97  --sat_mode                              false
% 59.43/7.97  --sat_fm_restart_options                ""
% 59.43/7.97  --sat_gr_def                            false
% 59.43/7.97  --sat_epr_types                         true
% 59.43/7.97  --sat_non_cyclic_types                  false
% 59.43/7.97  --sat_finite_models                     false
% 59.43/7.97  --sat_fm_lemmas                         false
% 59.43/7.97  --sat_fm_prep                           false
% 59.43/7.97  --sat_fm_uc_incr                        true
% 59.43/7.97  --sat_out_model                         small
% 59.43/7.97  --sat_out_clauses                       false
% 59.43/7.97  
% 59.43/7.97  ------ QBF Options
% 59.43/7.97  
% 59.43/7.97  --qbf_mode                              false
% 59.43/7.97  --qbf_elim_univ                         false
% 59.43/7.97  --qbf_dom_inst                          none
% 59.43/7.97  --qbf_dom_pre_inst                      false
% 59.43/7.97  --qbf_sk_in                             false
% 59.43/7.97  --qbf_pred_elim                         true
% 59.43/7.97  --qbf_split                             512
% 59.43/7.97  
% 59.43/7.97  ------ BMC1 Options
% 59.43/7.97  
% 59.43/7.97  --bmc1_incremental                      false
% 59.43/7.97  --bmc1_axioms                           reachable_all
% 59.43/7.97  --bmc1_min_bound                        0
% 59.43/7.97  --bmc1_max_bound                        -1
% 59.43/7.97  --bmc1_max_bound_default                -1
% 59.43/7.97  --bmc1_symbol_reachability              true
% 59.43/7.97  --bmc1_property_lemmas                  false
% 59.43/7.97  --bmc1_k_induction                      false
% 59.43/7.97  --bmc1_non_equiv_states                 false
% 59.43/7.97  --bmc1_deadlock                         false
% 59.43/7.97  --bmc1_ucm                              false
% 59.43/7.97  --bmc1_add_unsat_core                   none
% 59.43/7.97  --bmc1_unsat_core_children              false
% 59.43/7.97  --bmc1_unsat_core_extrapolate_axioms    false
% 59.43/7.97  --bmc1_out_stat                         full
% 59.43/7.97  --bmc1_ground_init                      false
% 59.43/7.97  --bmc1_pre_inst_next_state              false
% 59.43/7.97  --bmc1_pre_inst_state                   false
% 59.43/7.97  --bmc1_pre_inst_reach_state             false
% 59.43/7.97  --bmc1_out_unsat_core                   false
% 59.43/7.97  --bmc1_aig_witness_out                  false
% 59.43/7.97  --bmc1_verbose                          false
% 59.43/7.97  --bmc1_dump_clauses_tptp                false
% 59.43/7.97  --bmc1_dump_unsat_core_tptp             false
% 59.43/7.97  --bmc1_dump_file                        -
% 59.43/7.97  --bmc1_ucm_expand_uc_limit              128
% 59.43/7.97  --bmc1_ucm_n_expand_iterations          6
% 59.43/7.97  --bmc1_ucm_extend_mode                  1
% 59.43/7.97  --bmc1_ucm_init_mode                    2
% 59.43/7.97  --bmc1_ucm_cone_mode                    none
% 59.43/7.97  --bmc1_ucm_reduced_relation_type        0
% 59.43/7.97  --bmc1_ucm_relax_model                  4
% 59.43/7.97  --bmc1_ucm_full_tr_after_sat            true
% 59.43/7.97  --bmc1_ucm_expand_neg_assumptions       false
% 59.43/7.97  --bmc1_ucm_layered_model                none
% 59.43/7.97  --bmc1_ucm_max_lemma_size               10
% 59.43/7.97  
% 59.43/7.97  ------ AIG Options
% 59.43/7.97  
% 59.43/7.97  --aig_mode                              false
% 59.43/7.97  
% 59.43/7.97  ------ Instantiation Options
% 59.43/7.97  
% 59.43/7.97  --instantiation_flag                    true
% 59.43/7.97  --inst_sos_flag                         true
% 59.43/7.97  --inst_sos_phase                        true
% 59.43/7.97  --inst_sos_sth_lit_sel                  [+prop;+non_prol_conj_symb;-eq;+ground;-num_var;-num_symb]
% 59.43/7.97  --inst_lit_sel                          [+prop;+sign;+ground;-num_var;-num_symb]
% 59.43/7.97  --inst_lit_sel_side                     none
% 59.43/7.97  --inst_solver_per_active                1400
% 59.43/7.97  --inst_solver_calls_frac                1.
% 59.43/7.97  --inst_passive_queue_type               priority_queues
% 59.43/7.97  --inst_passive_queues                   [[-conj_dist;+conj_symb;-num_var];[+age;-num_symb]]
% 59.43/7.97  --inst_passive_queues_freq              [25;2]
% 59.43/7.97  --inst_dismatching                      true
% 59.43/7.97  --inst_eager_unprocessed_to_passive     true
% 59.43/7.97  --inst_prop_sim_given                   true
% 59.43/7.97  --inst_prop_sim_new                     false
% 59.43/7.97  --inst_subs_new                         false
% 59.43/7.97  --inst_eq_res_simp                      false
% 59.43/7.97  --inst_subs_given                       false
% 59.43/7.97  --inst_orphan_elimination               true
% 59.43/7.97  --inst_learning_loop_flag               true
% 59.43/7.97  --inst_learning_start                   3000
% 59.43/7.97  --inst_learning_factor                  2
% 59.43/7.97  --inst_start_prop_sim_after_learn       3
% 59.43/7.97  --inst_sel_renew                        solver
% 59.43/7.97  --inst_lit_activity_flag                true
% 59.43/7.97  --inst_restr_to_given                   false
% 59.43/7.97  --inst_activity_threshold               500
% 59.43/7.97  --inst_out_proof                        true
% 59.43/7.97  
% 59.43/7.97  ------ Resolution Options
% 59.43/7.97  
% 59.43/7.97  --resolution_flag                       false
% 59.43/7.97  --res_lit_sel                           adaptive
% 59.43/7.97  --res_lit_sel_side                      none
% 59.43/7.97  --res_ordering                          kbo
% 59.43/7.97  --res_to_prop_solver                    active
% 59.43/7.97  --res_prop_simpl_new                    false
% 59.43/7.97  --res_prop_simpl_given                  true
% 59.43/7.97  --res_passive_queue_type                priority_queues
% 59.43/7.97  --res_passive_queues                    [[-conj_dist;+conj_symb;-num_symb];[+age;-num_symb]]
% 59.43/7.97  --res_passive_queues_freq               [15;5]
% 59.43/7.97  --res_forward_subs                      full
% 59.43/7.97  --res_backward_subs                     full
% 59.43/7.97  --res_forward_subs_resolution           true
% 59.43/7.97  --res_backward_subs_resolution          true
% 59.43/7.97  --res_orphan_elimination                true
% 59.43/7.97  --res_time_limit                        2.
% 59.43/7.97  --res_out_proof                         true
% 59.43/7.97  
% 59.43/7.97  ------ Superposition Options
% 59.43/7.97  
% 59.43/7.97  --superposition_flag                    true
% 59.43/7.97  --sup_passive_queue_type                priority_queues
% 59.43/7.97  --sup_passive_queues                    [[-conj_dist;+horn;-num_symb];[+min_def_symb;-max_atom_input_occur;+conj_non_prolific_symb];[+age;-num_symb]]
% 59.43/7.97  --sup_passive_queues_freq               [8;1;4]
% 59.43/7.97  --demod_completeness_check              fast
% 59.43/7.97  --demod_use_ground                      true
% 59.43/7.97  --sup_to_prop_solver                    passive
% 59.43/7.97  --sup_prop_simpl_new                    true
% 59.43/7.97  --sup_prop_simpl_given                  true
% 59.43/7.97  --sup_fun_splitting                     true
% 59.43/7.97  --sup_smt_interval                      50000
% 59.43/7.97  
% 59.43/7.97  ------ Superposition Simplification Setup
% 59.43/7.97  
% 59.43/7.97  --sup_indices_passive                   [LightNormIndex;FwDemodIndex]
% 59.43/7.97  --sup_indices_active                    [SubsumptionIndex;BwDemodIndex]
% 59.43/7.97  --sup_indices_immed                     [SubsumptionIndex;FwDemodIndex;BwDemodIndex]
% 59.43/7.97  --sup_indices_input                     [SubsumptionIndex;LightNormIndex;FwDemodIndex]
% 59.43/7.97  --sup_full_triv                         [TrivRules;PropSubs]
% 59.43/7.97  --sup_full_fw                           [FwDemodLightNormLoopTriv;FwSubsumption;Joinability]
% 59.43/7.97  --sup_full_bw                           [BwDemod;BwSubsumption]
% 59.43/7.97  --sup_immed_triv                        [TrivRules]
% 59.43/7.97  --sup_immed_fw_main                     [Joinability;FwDemodLightNormLoopTriv;FwSubsumption]
% 59.43/7.97  --sup_immed_fw_immed                    [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.43/7.97  --sup_immed_bw_main                     []
% 59.43/7.97  --sup_immed_bw_immed                    [BwDemod;BwSubsumption]
% 59.43/7.97  --sup_input_triv                        [Unflattening;TrivRules]
% 59.43/7.97  --sup_input_fw                          [FwDemodLightNormLoopTriv;FwSubsumption]
% 59.43/7.97  --sup_input_bw                          []
% 59.43/7.97  
% 59.43/7.97  ------ Combination Options
% 59.43/7.97  
% 59.43/7.97  --comb_res_mult                         3
% 59.43/7.97  --comb_sup_mult                         2
% 59.43/7.97  --comb_inst_mult                        10
% 59.43/7.97  
% 59.43/7.97  ------ Debug Options
% 59.43/7.97  
% 59.43/7.97  --dbg_backtrace                         false
% 59.43/7.97  --dbg_dump_prop_clauses                 false
% 59.43/7.97  --dbg_dump_prop_clauses_file            -
% 59.43/7.97  --dbg_out_stat                          false
% 59.43/7.97  
% 59.43/7.97  
% 59.43/7.97  
% 59.43/7.97  
% 59.43/7.97  ------ Proving...
% 59.43/7.97  
% 59.43/7.97  
% 59.43/7.97  % SZS status Theorem for theBenchmark.p
% 59.43/7.97  
% 59.43/7.97  % SZS output start CNFRefutation for theBenchmark.p
% 59.43/7.97  
% 59.43/7.97  fof(f19,conjecture,(
% 59.43/7.97    ! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 59.43/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.43/7.97  
% 59.43/7.97  fof(f20,negated_conjecture,(
% 59.43/7.97    ~! [X0,X1,X2,X3,X4] : (m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)) => (! [X5] : (m1_subset_1(X5,X0) => ! [X6] : (m1_subset_1(X6,X1) => ! [X7] : (m1_subset_1(X7,X2) => (k3_mcart_1(X5,X6,X7) = X4 => X3 = X7)))) => (k7_mcart_1(X0,X1,X2,X4) = X3 | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 59.43/7.97    inference(negated_conjecture,[],[f19])).
% 59.43/7.97  
% 59.43/7.97  fof(f27,plain,(
% 59.43/7.97    ? [X0,X1,X2,X3,X4] : (((k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & ! [X5] : (! [X6] : (! [X7] : ((X3 = X7 | k3_mcart_1(X5,X6,X7) != X4) | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0))) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 59.43/7.97    inference(ennf_transformation,[],[f20])).
% 59.43/7.97  
% 59.43/7.97  fof(f28,plain,(
% 59.43/7.97    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2)))),
% 59.43/7.97    inference(flattening,[],[f27])).
% 59.43/7.97  
% 59.43/7.97  fof(f51,plain,(
% 59.43/7.97    ? [X0,X1,X2,X3,X4] : (k7_mcart_1(X0,X1,X2,X4) != X3 & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & ! [X5] : (! [X6] : (! [X7] : (X3 = X7 | k3_mcart_1(X5,X6,X7) != X4 | ~m1_subset_1(X7,X2)) | ~m1_subset_1(X6,X1)) | ~m1_subset_1(X5,X0)) & m1_subset_1(X4,k3_zfmisc_1(X0,X1,X2))) => (k7_mcart_1(sK8,sK9,sK10,sK12) != sK11 & k1_xboole_0 != sK10 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X5] : (! [X6] : (! [X7] : (sK11 = X7 | k3_mcart_1(X5,X6,X7) != sK12 | ~m1_subset_1(X7,sK10)) | ~m1_subset_1(X6,sK9)) | ~m1_subset_1(X5,sK8)) & m1_subset_1(sK12,k3_zfmisc_1(sK8,sK9,sK10)))),
% 59.43/7.97    introduced(choice_axiom,[])).
% 59.43/7.97  
% 59.43/7.97  fof(f52,plain,(
% 59.43/7.97    k7_mcart_1(sK8,sK9,sK10,sK12) != sK11 & k1_xboole_0 != sK10 & k1_xboole_0 != sK9 & k1_xboole_0 != sK8 & ! [X5] : (! [X6] : (! [X7] : (sK11 = X7 | k3_mcart_1(X5,X6,X7) != sK12 | ~m1_subset_1(X7,sK10)) | ~m1_subset_1(X6,sK9)) | ~m1_subset_1(X5,sK8)) & m1_subset_1(sK12,k3_zfmisc_1(sK8,sK9,sK10))),
% 59.43/7.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK8,sK9,sK10,sK11,sK12])],[f28,f51])).
% 59.43/7.97  
% 59.43/7.97  fof(f97,plain,(
% 59.43/7.97    m1_subset_1(sK12,k3_zfmisc_1(sK8,sK9,sK10))),
% 59.43/7.97    inference(cnf_transformation,[],[f52])).
% 59.43/7.97  
% 59.43/7.97  fof(f13,axiom,(
% 59.43/7.97    ! [X0,X1,X2] : k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)),
% 59.43/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.43/7.97  
% 59.43/7.97  fof(f83,plain,(
% 59.43/7.97    ( ! [X2,X0,X1] : (k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) = k3_zfmisc_1(X0,X1,X2)) )),
% 59.43/7.97    inference(cnf_transformation,[],[f13])).
% 59.43/7.97  
% 59.43/7.97  fof(f122,plain,(
% 59.43/7.97    m1_subset_1(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10))),
% 59.43/7.97    inference(definition_unfolding,[],[f97,f83])).
% 59.43/7.97  
% 59.43/7.97  fof(f10,axiom,(
% 59.43/7.97    ! [X0,X1] : ((v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> v1_xboole_0(X1))) & (~v1_xboole_0(X0) => (m1_subset_1(X1,X0) <=> r2_hidden(X1,X0))))),
% 59.43/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.43/7.97  
% 59.43/7.97  fof(f21,plain,(
% 59.43/7.97    ! [X0,X1] : (((m1_subset_1(X1,X0) <=> v1_xboole_0(X1)) | ~v1_xboole_0(X0)) & ((m1_subset_1(X1,X0) <=> r2_hidden(X1,X0)) | v1_xboole_0(X0)))),
% 59.43/7.97    inference(ennf_transformation,[],[f10])).
% 59.43/7.97  
% 59.43/7.97  fof(f46,plain,(
% 59.43/7.97    ! [X0,X1] : ((((m1_subset_1(X1,X0) | ~v1_xboole_0(X1)) & (v1_xboole_0(X1) | ~m1_subset_1(X1,X0))) | ~v1_xboole_0(X0)) & (((m1_subset_1(X1,X0) | ~r2_hidden(X1,X0)) & (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0))) | v1_xboole_0(X0)))),
% 59.43/7.97    inference(nnf_transformation,[],[f21])).
% 59.43/7.97  
% 59.43/7.97  fof(f77,plain,(
% 59.43/7.97    ( ! [X0,X1] : (r2_hidden(X1,X0) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0)) )),
% 59.43/7.97    inference(cnf_transformation,[],[f46])).
% 59.43/7.97  
% 59.43/7.97  fof(f11,axiom,(
% 59.43/7.97    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 59.43/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.43/7.97  
% 59.43/7.97  fof(f81,plain,(
% 59.43/7.97    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 59.43/7.97    inference(cnf_transformation,[],[f11])).
% 59.43/7.97  
% 59.43/7.97  fof(f15,axiom,(
% 59.43/7.97    ! [X0,X1] : (v1_relat_1(X1) => (r2_hidden(X0,X1) => k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0))),
% 59.43/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.43/7.97  
% 59.43/7.97  fof(f23,plain,(
% 59.43/7.97    ! [X0,X1] : ((k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1)) | ~v1_relat_1(X1))),
% 59.43/7.97    inference(ennf_transformation,[],[f15])).
% 59.43/7.97  
% 59.43/7.97  fof(f24,plain,(
% 59.43/7.97    ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1))),
% 59.43/7.97    inference(flattening,[],[f23])).
% 59.43/7.97  
% 59.43/7.97  fof(f86,plain,(
% 59.43/7.97    ( ! [X0,X1] : (k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 | ~r2_hidden(X0,X1) | ~v1_relat_1(X1)) )),
% 59.43/7.97    inference(cnf_transformation,[],[f24])).
% 59.43/7.97  
% 59.43/7.97  fof(f79,plain,(
% 59.43/7.97    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,X0) | ~v1_xboole_0(X0)) )),
% 59.43/7.97    inference(cnf_transformation,[],[f46])).
% 59.43/7.97  
% 59.43/7.97  fof(f99,plain,(
% 59.43/7.97    k1_xboole_0 != sK8),
% 59.43/7.97    inference(cnf_transformation,[],[f52])).
% 59.43/7.97  
% 59.43/7.97  fof(f100,plain,(
% 59.43/7.97    k1_xboole_0 != sK9),
% 59.43/7.97    inference(cnf_transformation,[],[f52])).
% 59.43/7.97  
% 59.43/7.97  fof(f101,plain,(
% 59.43/7.97    k1_xboole_0 != sK10),
% 59.43/7.97    inference(cnf_transformation,[],[f52])).
% 59.43/7.97  
% 59.43/7.97  fof(f17,axiom,(
% 59.43/7.97    ! [X0,X1,X2] : ((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) <=> k1_xboole_0 != k3_zfmisc_1(X0,X1,X2))),
% 59.43/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.43/7.97  
% 59.43/7.97  fof(f49,plain,(
% 59.43/7.97    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | (k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)))),
% 59.43/7.97    inference(nnf_transformation,[],[f17])).
% 59.43/7.97  
% 59.43/7.97  fof(f50,plain,(
% 59.43/7.97    ! [X0,X1,X2] : (((k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0) | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) & (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0))),
% 59.43/7.97    inference(flattening,[],[f49])).
% 59.43/7.97  
% 59.43/7.97  fof(f90,plain,(
% 59.43/7.97    ( ! [X2,X0,X1] : (k1_xboole_0 != k3_zfmisc_1(X0,X1,X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 59.43/7.97    inference(cnf_transformation,[],[f50])).
% 59.43/7.97  
% 59.43/7.97  fof(f117,plain,(
% 59.43/7.97    ( ! [X2,X0,X1] : (k1_xboole_0 != k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 59.43/7.97    inference(definition_unfolding,[],[f90,f83])).
% 59.43/7.97  
% 59.43/7.97  fof(f16,axiom,(
% 59.43/7.97    ! [X0] : ~(! [X1] : ~(! [X2,X3,X4,X5] : ~(k4_mcart_1(X2,X3,X4,X5) = X1 & (r2_hidden(X3,X0) | r2_hidden(X2,X0))) & r2_hidden(X1,X0)) & k1_xboole_0 != X0)),
% 59.43/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.43/7.97  
% 59.43/7.97  fof(f25,plain,(
% 59.43/7.97    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) | k1_xboole_0 = X0)),
% 59.43/7.97    inference(ennf_transformation,[],[f16])).
% 59.43/7.97  
% 59.43/7.97  fof(f47,plain,(
% 59.43/7.97    ! [X0] : (? [X1] : (! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != X1 | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(X1,X0)) => (! [X5,X4,X3,X2] : (k4_mcart_1(X2,X3,X4,X5) != sK7(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK7(X0),X0)))),
% 59.43/7.97    introduced(choice_axiom,[])).
% 59.43/7.97  
% 59.43/7.97  fof(f48,plain,(
% 59.43/7.97    ! [X0] : ((! [X2,X3,X4,X5] : (k4_mcart_1(X2,X3,X4,X5) != sK7(X0) | (~r2_hidden(X3,X0) & ~r2_hidden(X2,X0))) & r2_hidden(sK7(X0),X0)) | k1_xboole_0 = X0)),
% 59.43/7.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK7])],[f25,f47])).
% 59.43/7.97  
% 59.43/7.97  fof(f87,plain,(
% 59.43/7.97    ( ! [X0] : (r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0) )),
% 59.43/7.97    inference(cnf_transformation,[],[f48])).
% 59.43/7.97  
% 59.43/7.97  fof(f1,axiom,(
% 59.43/7.97    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 59.43/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.43/7.97  
% 59.43/7.97  fof(f29,plain,(
% 59.43/7.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X1] : ~r2_hidden(X1,X0) | ~v1_xboole_0(X0)))),
% 59.43/7.97    inference(nnf_transformation,[],[f1])).
% 59.43/7.97  
% 59.43/7.97  fof(f30,plain,(
% 59.43/7.97    ! [X0] : ((v1_xboole_0(X0) | ? [X1] : r2_hidden(X1,X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 59.43/7.97    inference(rectify,[],[f29])).
% 59.43/7.97  
% 59.43/7.97  fof(f31,plain,(
% 59.43/7.97    ! [X0] : (? [X1] : r2_hidden(X1,X0) => r2_hidden(sK0(X0),X0))),
% 59.43/7.97    introduced(choice_axiom,[])).
% 59.43/7.97  
% 59.43/7.97  fof(f32,plain,(
% 59.43/7.97    ! [X0] : ((v1_xboole_0(X0) | r2_hidden(sK0(X0),X0)) & (! [X2] : ~r2_hidden(X2,X0) | ~v1_xboole_0(X0)))),
% 59.43/7.97    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f30,f31])).
% 59.43/7.97  
% 59.43/7.97  fof(f53,plain,(
% 59.43/7.97    ( ! [X2,X0] : (~r2_hidden(X2,X0) | ~v1_xboole_0(X0)) )),
% 59.43/7.97    inference(cnf_transformation,[],[f32])).
% 59.43/7.97  
% 59.43/7.97  fof(f14,axiom,(
% 59.43/7.97    ! [X0,X1,X2] : (r2_hidden(X0,k2_zfmisc_1(X1,X2)) => (r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)))),
% 59.43/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.43/7.97  
% 59.43/7.97  fof(f22,plain,(
% 59.43/7.97    ! [X0,X1,X2] : ((r2_hidden(k2_mcart_1(X0),X2) & r2_hidden(k1_mcart_1(X0),X1)) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2)))),
% 59.43/7.97    inference(ennf_transformation,[],[f14])).
% 59.43/7.97  
% 59.43/7.97  fof(f84,plain,(
% 59.43/7.97    ( ! [X2,X0,X1] : (r2_hidden(k1_mcart_1(X0),X1) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 59.43/7.97    inference(cnf_transformation,[],[f22])).
% 59.43/7.97  
% 59.43/7.97  fof(f98,plain,(
% 59.43/7.97    ( ! [X6,X7,X5] : (sK11 = X7 | k3_mcart_1(X5,X6,X7) != sK12 | ~m1_subset_1(X7,sK10) | ~m1_subset_1(X6,sK9) | ~m1_subset_1(X5,sK8)) )),
% 59.43/7.97    inference(cnf_transformation,[],[f52])).
% 59.43/7.97  
% 59.43/7.97  fof(f12,axiom,(
% 59.43/7.97    ! [X0,X1,X2] : k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)),
% 59.43/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.43/7.97  
% 59.43/7.97  fof(f82,plain,(
% 59.43/7.97    ( ! [X2,X0,X1] : (k4_tarski(k4_tarski(X0,X1),X2) = k3_mcart_1(X0,X1,X2)) )),
% 59.43/7.97    inference(cnf_transformation,[],[f12])).
% 59.43/7.97  
% 59.43/7.97  fof(f121,plain,(
% 59.43/7.97    ( ! [X6,X7,X5] : (sK11 = X7 | k4_tarski(k4_tarski(X5,X6),X7) != sK12 | ~m1_subset_1(X7,sK10) | ~m1_subset_1(X6,sK9) | ~m1_subset_1(X5,sK8)) )),
% 59.43/7.97    inference(definition_unfolding,[],[f98,f82])).
% 59.43/7.97  
% 59.43/7.97  fof(f85,plain,(
% 59.43/7.97    ( ! [X2,X0,X1] : (r2_hidden(k2_mcart_1(X0),X2) | ~r2_hidden(X0,k2_zfmisc_1(X1,X2))) )),
% 59.43/7.97    inference(cnf_transformation,[],[f22])).
% 59.43/7.97  
% 59.43/7.97  fof(f78,plain,(
% 59.43/7.97    ( ! [X0,X1] : (m1_subset_1(X1,X0) | ~r2_hidden(X1,X0) | v1_xboole_0(X0)) )),
% 59.43/7.97    inference(cnf_transformation,[],[f46])).
% 59.43/7.97  
% 59.43/7.97  fof(f18,axiom,(
% 59.43/7.97    ! [X0,X1,X2] : ~(~! [X3] : (m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) => (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3))) & k1_xboole_0 != X2 & k1_xboole_0 != X1 & k1_xboole_0 != X0)),
% 59.43/7.97    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',unknown)).
% 59.43/7.97  
% 59.43/7.97  fof(f26,plain,(
% 59.43/7.97    ! [X0,X1,X2] : (! [X3] : ((k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) & k2_mcart_1(k1_mcart_1(X3)) = k6_mcart_1(X0,X1,X2,X3) & k1_mcart_1(k1_mcart_1(X3)) = k5_mcart_1(X0,X1,X2,X3)) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2))) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0)),
% 59.43/7.97    inference(ennf_transformation,[],[f18])).
% 59.43/7.97  
% 59.43/7.97  fof(f96,plain,(
% 59.43/7.97    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k3_zfmisc_1(X0,X1,X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 59.43/7.97    inference(cnf_transformation,[],[f26])).
% 59.43/7.97  
% 59.43/7.97  fof(f118,plain,(
% 59.43/7.97    ( ! [X2,X0,X3,X1] : (k2_mcart_1(X3) = k7_mcart_1(X0,X1,X2,X3) | ~m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) | k1_xboole_0 = X2 | k1_xboole_0 = X1 | k1_xboole_0 = X0) )),
% 59.43/7.97    inference(definition_unfolding,[],[f96,f83])).
% 59.43/7.97  
% 59.43/7.97  fof(f91,plain,(
% 59.43/7.97    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k3_zfmisc_1(X0,X1,X2)) )),
% 59.43/7.97    inference(cnf_transformation,[],[f50])).
% 59.43/7.97  
% 59.43/7.97  fof(f116,plain,(
% 59.43/7.97    ( ! [X2,X0,X1] : (k1_xboole_0 != X0 | k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) )),
% 59.43/7.97    inference(definition_unfolding,[],[f91,f83])).
% 59.43/7.97  
% 59.43/7.97  fof(f135,plain,(
% 59.43/7.97    ( ! [X2,X1] : (k1_xboole_0 = k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1),X2)) )),
% 59.43/7.97    inference(equality_resolution,[],[f116])).
% 59.43/7.97  
% 59.43/7.97  fof(f102,plain,(
% 59.43/7.97    k7_mcart_1(sK8,sK9,sK10,sK12) != sK11),
% 59.43/7.97    inference(cnf_transformation,[],[f52])).
% 59.43/7.97  
% 59.43/7.97  cnf(c_45,negated_conjecture,
% 59.43/7.97      ( m1_subset_1(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) ),
% 59.43/7.97      inference(cnf_transformation,[],[f122]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1183,plain,
% 59.43/7.97      ( m1_subset_1(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 59.43/7.97      inference(predicate_to_equality,[status(thm)],[c_45]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_25,plain,
% 59.43/7.97      ( ~ m1_subset_1(X0,X1) | r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 59.43/7.97      inference(cnf_transformation,[],[f77]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1193,plain,
% 59.43/7.97      ( m1_subset_1(X0,X1) != iProver_top
% 59.43/7.97      | r2_hidden(X0,X1) = iProver_top
% 59.43/7.97      | v1_xboole_0(X1) = iProver_top ),
% 59.43/7.97      inference(predicate_to_equality,[status(thm)],[c_25]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_3788,plain,
% 59.43/7.97      ( r2_hidden(sK12,k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top
% 59.43/7.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_1183,c_1193]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_26,plain,
% 59.43/7.97      ( v1_relat_1(k2_zfmisc_1(X0,X1)) ),
% 59.43/7.97      inference(cnf_transformation,[],[f81]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_29,plain,
% 59.43/7.97      ( ~ r2_hidden(X0,X1)
% 59.43/7.97      | ~ v1_relat_1(X1)
% 59.43/7.97      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 59.43/7.97      inference(cnf_transformation,[],[f86]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_420,plain,
% 59.43/7.97      ( ~ r2_hidden(X0,X1)
% 59.43/7.97      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 59.43/7.97      | k2_zfmisc_1(X2,X3) != X1 ),
% 59.43/7.97      inference(resolution_lifted,[status(thm)],[c_26,c_29]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_421,plain,
% 59.43/7.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 59.43/7.97      | k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0 ),
% 59.43/7.97      inference(unflattening,[status(thm)],[c_420]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1181,plain,
% 59.43/7.97      ( k4_tarski(k1_mcart_1(X0),k2_mcart_1(X0)) = X0
% 59.43/7.97      | r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top ),
% 59.43/7.97      inference(predicate_to_equality,[status(thm)],[c_421]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_3915,plain,
% 59.43/7.97      ( k4_tarski(k1_mcart_1(sK12),k2_mcart_1(sK12)) = sK12
% 59.43/7.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_3788,c_1181]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_23,plain,
% 59.43/7.97      ( ~ m1_subset_1(X0,X1) | ~ v1_xboole_0(X1) | v1_xboole_0(X0) ),
% 59.43/7.97      inference(cnf_transformation,[],[f79]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1194,plain,
% 59.43/7.97      ( m1_subset_1(X0,X1) != iProver_top
% 59.43/7.97      | v1_xboole_0(X1) != iProver_top
% 59.43/7.97      | v1_xboole_0(X0) = iProver_top ),
% 59.43/7.97      inference(predicate_to_equality,[status(thm)],[c_23]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_3794,plain,
% 59.43/7.97      ( v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) != iProver_top
% 59.43/7.97      | v1_xboole_0(sK12) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_1183,c_1194]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_4059,plain,
% 59.43/7.97      ( k4_tarski(k1_mcart_1(sK12),k2_mcart_1(sK12)) = sK12
% 59.43/7.97      | v1_xboole_0(sK12) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_3915,c_3794]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_43,negated_conjecture,
% 59.43/7.97      ( k1_xboole_0 != sK8 ),
% 59.43/7.97      inference(cnf_transformation,[],[f99]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_42,negated_conjecture,
% 59.43/7.97      ( k1_xboole_0 != sK9 ),
% 59.43/7.97      inference(cnf_transformation,[],[f100]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_41,negated_conjecture,
% 59.43/7.97      ( k1_xboole_0 != sK10 ),
% 59.43/7.97      inference(cnf_transformation,[],[f101]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_36,plain,
% 59.43/7.97      ( k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2) != k1_xboole_0
% 59.43/7.97      | k1_xboole_0 = X0
% 59.43/7.97      | k1_xboole_0 = X2
% 59.43/7.97      | k1_xboole_0 = X1 ),
% 59.43/7.97      inference(cnf_transformation,[],[f117]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1321,plain,
% 59.43/7.97      ( k2_zfmisc_1(k2_zfmisc_1(sK8,X0),X1) != k1_xboole_0
% 59.43/7.97      | k1_xboole_0 = X0
% 59.43/7.97      | k1_xboole_0 = X1
% 59.43/7.97      | k1_xboole_0 = sK8 ),
% 59.43/7.97      inference(instantiation,[status(thm)],[c_36]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1627,plain,
% 59.43/7.97      ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),X0) != k1_xboole_0
% 59.43/7.97      | k1_xboole_0 = X0
% 59.43/7.97      | k1_xboole_0 = sK9
% 59.43/7.97      | k1_xboole_0 = sK8 ),
% 59.43/7.97      inference(instantiation,[status(thm)],[c_1321]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_2145,plain,
% 59.43/7.97      ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) != k1_xboole_0
% 59.43/7.97      | k1_xboole_0 = sK10
% 59.43/7.97      | k1_xboole_0 = sK9
% 59.43/7.97      | k1_xboole_0 = sK8 ),
% 59.43/7.97      inference(instantiation,[status(thm)],[c_1627]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_32,plain,
% 59.43/7.97      ( r2_hidden(sK7(X0),X0) | k1_xboole_0 = X0 ),
% 59.43/7.97      inference(cnf_transformation,[],[f87]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1188,plain,
% 59.43/7.97      ( k1_xboole_0 = X0 | r2_hidden(sK7(X0),X0) = iProver_top ),
% 59.43/7.97      inference(predicate_to_equality,[status(thm)],[c_32]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1,plain,
% 59.43/7.97      ( ~ r2_hidden(X0,X1) | ~ v1_xboole_0(X1) ),
% 59.43/7.97      inference(cnf_transformation,[],[f53]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1213,plain,
% 59.43/7.97      ( r2_hidden(X0,X1) != iProver_top
% 59.43/7.97      | v1_xboole_0(X1) != iProver_top ),
% 59.43/7.97      inference(predicate_to_equality,[status(thm)],[c_1]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_3256,plain,
% 59.43/7.97      ( k1_xboole_0 = X0 | v1_xboole_0(X0) != iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_1188,c_1213]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_4058,plain,
% 59.43/7.97      ( k4_tarski(k1_mcart_1(sK12),k2_mcart_1(sK12)) = sK12
% 59.43/7.97      | k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0 ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_3915,c_3256]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_4150,plain,
% 59.43/7.97      ( k4_tarski(k1_mcart_1(sK12),k2_mcart_1(sK12)) = sK12 ),
% 59.43/7.97      inference(global_propositional_subsumption,
% 59.43/7.97                [status(thm)],
% 59.43/7.97                [c_4059,c_43,c_42,c_41,c_2145,c_4058]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_28,plain,
% 59.43/7.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 59.43/7.97      | r2_hidden(k1_mcart_1(X0),X1) ),
% 59.43/7.97      inference(cnf_transformation,[],[f84]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1191,plain,
% 59.43/7.97      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 59.43/7.97      | r2_hidden(k1_mcart_1(X0),X1) = iProver_top ),
% 59.43/7.97      inference(predicate_to_equality,[status(thm)],[c_28]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_3914,plain,
% 59.43/7.97      ( r2_hidden(k1_mcart_1(sK12),k2_zfmisc_1(sK8,sK9)) = iProver_top
% 59.43/7.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_3788,c_1191]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_4799,plain,
% 59.43/7.97      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK12)),k2_mcart_1(k1_mcart_1(sK12))) = k1_mcart_1(sK12)
% 59.43/7.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_3914,c_1181]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_120524,plain,
% 59.43/7.97      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK12)),k2_mcart_1(k1_mcart_1(sK12))) = k1_mcart_1(sK12)
% 59.43/7.97      | v1_xboole_0(sK12) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_4799,c_3794]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_120521,plain,
% 59.43/7.97      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK12)),k2_mcart_1(k1_mcart_1(sK12))) = k1_mcart_1(sK12)
% 59.43/7.97      | k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0 ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_4799,c_3256]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_122143,plain,
% 59.43/7.97      ( k4_tarski(k1_mcart_1(k1_mcart_1(sK12)),k2_mcart_1(k1_mcart_1(sK12))) = k1_mcart_1(sK12) ),
% 59.43/7.97      inference(global_propositional_subsumption,
% 59.43/7.97                [status(thm)],
% 59.43/7.97                [c_120524,c_43,c_42,c_41,c_2145,c_120521]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_44,negated_conjecture,
% 59.43/7.97      ( ~ m1_subset_1(X0,sK10)
% 59.43/7.97      | ~ m1_subset_1(X1,sK9)
% 59.43/7.97      | ~ m1_subset_1(X2,sK8)
% 59.43/7.97      | k4_tarski(k4_tarski(X2,X1),X0) != sK12
% 59.43/7.97      | sK11 = X0 ),
% 59.43/7.97      inference(cnf_transformation,[],[f121]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1184,plain,
% 59.43/7.97      ( k4_tarski(k4_tarski(X0,X1),X2) != sK12
% 59.43/7.97      | sK11 = X2
% 59.43/7.97      | m1_subset_1(X2,sK10) != iProver_top
% 59.43/7.97      | m1_subset_1(X1,sK9) != iProver_top
% 59.43/7.97      | m1_subset_1(X0,sK8) != iProver_top ),
% 59.43/7.97      inference(predicate_to_equality,[status(thm)],[c_44]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_122148,plain,
% 59.43/7.97      ( k4_tarski(k1_mcart_1(sK12),X0) != sK12
% 59.43/7.97      | sK11 = X0
% 59.43/7.97      | m1_subset_1(X0,sK10) != iProver_top
% 59.43/7.97      | m1_subset_1(k1_mcart_1(k1_mcart_1(sK12)),sK8) != iProver_top
% 59.43/7.97      | m1_subset_1(k2_mcart_1(k1_mcart_1(sK12)),sK9) != iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_122143,c_1184]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_27,plain,
% 59.43/7.97      ( ~ r2_hidden(X0,k2_zfmisc_1(X1,X2))
% 59.43/7.97      | r2_hidden(k2_mcart_1(X0),X2) ),
% 59.43/7.97      inference(cnf_transformation,[],[f85]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1192,plain,
% 59.43/7.97      ( r2_hidden(X0,k2_zfmisc_1(X1,X2)) != iProver_top
% 59.43/7.97      | r2_hidden(k2_mcart_1(X0),X2) = iProver_top ),
% 59.43/7.97      inference(predicate_to_equality,[status(thm)],[c_27]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_4797,plain,
% 59.43/7.97      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK12)),sK9) = iProver_top
% 59.43/7.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_3914,c_1192]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_5454,plain,
% 59.43/7.97      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK12)),sK9) = iProver_top
% 59.43/7.97      | v1_xboole_0(sK12) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_4797,c_3794]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_5453,plain,
% 59.43/7.97      ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0
% 59.43/7.97      | r2_hidden(k2_mcart_1(k1_mcart_1(sK12)),sK9) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_4797,c_3256]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_5458,plain,
% 59.43/7.97      ( r2_hidden(k2_mcart_1(k1_mcart_1(sK12)),sK9) = iProver_top ),
% 59.43/7.97      inference(global_propositional_subsumption,
% 59.43/7.97                [status(thm)],
% 59.43/7.97                [c_5454,c_43,c_42,c_41,c_2145,c_5453]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_24,plain,
% 59.43/7.97      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) | v1_xboole_0(X1) ),
% 59.43/7.97      inference(cnf_transformation,[],[f78]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_228,plain,
% 59.43/7.97      ( ~ r2_hidden(X0,X1) | m1_subset_1(X0,X1) ),
% 59.43/7.97      inference(global_propositional_subsumption,
% 59.43/7.97                [status(thm)],
% 59.43/7.97                [c_24,c_1]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_229,plain,
% 59.43/7.97      ( m1_subset_1(X0,X1) | ~ r2_hidden(X0,X1) ),
% 59.43/7.97      inference(renaming,[status(thm)],[c_228]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1182,plain,
% 59.43/7.97      ( m1_subset_1(X0,X1) = iProver_top
% 59.43/7.97      | r2_hidden(X0,X1) != iProver_top ),
% 59.43/7.97      inference(predicate_to_equality,[status(thm)],[c_229]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_5463,plain,
% 59.43/7.97      ( m1_subset_1(k2_mcart_1(k1_mcart_1(sK12)),sK9) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_5458,c_1182]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_4798,plain,
% 59.43/7.97      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK12)),sK8) = iProver_top
% 59.43/7.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_3914,c_1191]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_117066,plain,
% 59.43/7.97      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK12)),sK8) = iProver_top
% 59.43/7.97      | v1_xboole_0(sK12) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_4798,c_3794]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_117063,plain,
% 59.43/7.97      ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0
% 59.43/7.97      | r2_hidden(k1_mcart_1(k1_mcart_1(sK12)),sK8) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_4798,c_3256]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_118362,plain,
% 59.43/7.97      ( r2_hidden(k1_mcart_1(k1_mcart_1(sK12)),sK8) = iProver_top ),
% 59.43/7.97      inference(global_propositional_subsumption,
% 59.43/7.97                [status(thm)],
% 59.43/7.97                [c_117066,c_43,c_42,c_41,c_2145,c_117063]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_118367,plain,
% 59.43/7.97      ( m1_subset_1(k1_mcart_1(k1_mcart_1(sK12)),sK8) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_118362,c_1182]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_122158,plain,
% 59.43/7.97      ( k4_tarski(k1_mcart_1(sK12),X0) != sK12
% 59.43/7.97      | sK11 = X0
% 59.43/7.97      | m1_subset_1(X0,sK10) != iProver_top ),
% 59.43/7.97      inference(global_propositional_subsumption,
% 59.43/7.97                [status(thm)],
% 59.43/7.97                [c_122148,c_5463,c_118367]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_122164,plain,
% 59.43/7.97      ( k2_mcart_1(sK12) = sK11
% 59.43/7.97      | m1_subset_1(k2_mcart_1(sK12),sK10) != iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_4150,c_122158]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_37,plain,
% 59.43/7.97      ( ~ m1_subset_1(X0,k2_zfmisc_1(k2_zfmisc_1(X1,X2),X3))
% 59.43/7.97      | k7_mcart_1(X1,X2,X3,X0) = k2_mcart_1(X0)
% 59.43/7.97      | k1_xboole_0 = X1
% 59.43/7.97      | k1_xboole_0 = X3
% 59.43/7.97      | k1_xboole_0 = X2 ),
% 59.43/7.97      inference(cnf_transformation,[],[f118]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1187,plain,
% 59.43/7.97      ( k7_mcart_1(X0,X1,X2,X3) = k2_mcart_1(X3)
% 59.43/7.97      | k1_xboole_0 = X0
% 59.43/7.97      | k1_xboole_0 = X1
% 59.43/7.97      | k1_xboole_0 = X2
% 59.43/7.97      | m1_subset_1(X3,k2_zfmisc_1(k2_zfmisc_1(X0,X1),X2)) != iProver_top ),
% 59.43/7.97      inference(predicate_to_equality,[status(thm)],[c_37]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_4293,plain,
% 59.43/7.97      ( k7_mcart_1(sK8,sK9,sK10,sK12) = k2_mcart_1(sK12)
% 59.43/7.97      | sK10 = k1_xboole_0
% 59.43/7.97      | sK9 = k1_xboole_0
% 59.43/7.97      | sK8 = k1_xboole_0 ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_1183,c_1187]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_59,plain,
% 59.43/7.97      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) != k1_xboole_0
% 59.43/7.97      | k1_xboole_0 = k1_xboole_0 ),
% 59.43/7.97      inference(instantiation,[status(thm)],[c_36]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_35,plain,
% 59.43/7.97      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X0),X1) = k1_xboole_0 ),
% 59.43/7.97      inference(cnf_transformation,[],[f135]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_60,plain,
% 59.43/7.97      ( k2_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0),k1_xboole_0) = k1_xboole_0 ),
% 59.43/7.97      inference(instantiation,[status(thm)],[c_35]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_666,plain,( X0 != X1 | X2 != X1 | X2 = X0 ),theory(equality) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1282,plain,
% 59.43/7.97      ( sK10 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK10 ),
% 59.43/7.97      inference(instantiation,[status(thm)],[c_666]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1283,plain,
% 59.43/7.97      ( sK10 != k1_xboole_0
% 59.43/7.97      | k1_xboole_0 = sK10
% 59.43/7.97      | k1_xboole_0 != k1_xboole_0 ),
% 59.43/7.97      inference(instantiation,[status(thm)],[c_1282]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1316,plain,
% 59.43/7.97      ( sK9 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK9 ),
% 59.43/7.97      inference(instantiation,[status(thm)],[c_666]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1317,plain,
% 59.43/7.97      ( sK9 != k1_xboole_0
% 59.43/7.97      | k1_xboole_0 = sK9
% 59.43/7.97      | k1_xboole_0 != k1_xboole_0 ),
% 59.43/7.97      inference(instantiation,[status(thm)],[c_1316]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1342,plain,
% 59.43/7.97      ( sK8 != X0 | k1_xboole_0 != X0 | k1_xboole_0 = sK8 ),
% 59.43/7.97      inference(instantiation,[status(thm)],[c_666]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_1343,plain,
% 59.43/7.97      ( sK8 != k1_xboole_0
% 59.43/7.97      | k1_xboole_0 = sK8
% 59.43/7.97      | k1_xboole_0 != k1_xboole_0 ),
% 59.43/7.97      inference(instantiation,[status(thm)],[c_1342]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_4743,plain,
% 59.43/7.97      ( k7_mcart_1(sK8,sK9,sK10,sK12) = k2_mcart_1(sK12) ),
% 59.43/7.97      inference(global_propositional_subsumption,
% 59.43/7.97                [status(thm)],
% 59.43/7.97                [c_4293,c_43,c_42,c_41,c_59,c_60,c_1283,c_1317,c_1343]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_40,negated_conjecture,
% 59.43/7.97      ( k7_mcart_1(sK8,sK9,sK10,sK12) != sK11 ),
% 59.43/7.97      inference(cnf_transformation,[],[f102]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_4745,plain,
% 59.43/7.97      ( k2_mcart_1(sK12) != sK11 ),
% 59.43/7.97      inference(demodulation,[status(thm)],[c_4743,c_40]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_3913,plain,
% 59.43/7.97      ( r2_hidden(k2_mcart_1(sK12),sK10) = iProver_top
% 59.43/7.97      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10)) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_3788,c_1192]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_3983,plain,
% 59.43/7.97      ( r2_hidden(k2_mcart_1(sK12),sK10) = iProver_top
% 59.43/7.97      | v1_xboole_0(sK12) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_3913,c_3794]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_3982,plain,
% 59.43/7.97      ( k2_zfmisc_1(k2_zfmisc_1(sK8,sK9),sK10) = k1_xboole_0
% 59.43/7.97      | r2_hidden(k2_mcart_1(sK12),sK10) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_3913,c_3256]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_4049,plain,
% 59.43/7.97      ( r2_hidden(k2_mcart_1(sK12),sK10) = iProver_top ),
% 59.43/7.97      inference(global_propositional_subsumption,
% 59.43/7.97                [status(thm)],
% 59.43/7.97                [c_3983,c_43,c_42,c_41,c_2145,c_3982]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(c_4054,plain,
% 59.43/7.97      ( m1_subset_1(k2_mcart_1(sK12),sK10) = iProver_top ),
% 59.43/7.97      inference(superposition,[status(thm)],[c_4049,c_1182]) ).
% 59.43/7.97  
% 59.43/7.97  cnf(contradiction,plain,
% 59.43/7.97      ( $false ),
% 59.43/7.97      inference(minisat,[status(thm)],[c_122164,c_4745,c_4054]) ).
% 59.43/7.97  
% 59.43/7.97  
% 59.43/7.97  % SZS output end CNFRefutation for theBenchmark.p
% 59.43/7.97  
% 59.43/7.97  ------                               Statistics
% 59.43/7.97  
% 59.43/7.97  ------ General
% 59.43/7.97  
% 59.43/7.97  abstr_ref_over_cycles:                  0
% 59.43/7.97  abstr_ref_under_cycles:                 0
% 59.43/7.97  gc_basic_clause_elim:                   0
% 59.43/7.97  forced_gc_time:                         0
% 59.43/7.97  parsing_time:                           0.019
% 59.43/7.97  unif_index_cands_time:                  0.
% 59.43/7.97  unif_index_add_time:                    0.
% 59.43/7.97  orderings_time:                         0.
% 59.43/7.97  out_proof_time:                         0.038
% 59.43/7.97  total_time:                             7.246
% 59.43/7.97  num_of_symbols:                         62
% 59.43/7.97  num_of_terms:                           357380
% 59.43/7.97  
% 59.43/7.97  ------ Preprocessing
% 59.43/7.97  
% 59.43/7.97  num_of_splits:                          0
% 59.43/7.97  num_of_split_atoms:                     0
% 59.43/7.97  num_of_reused_defs:                     0
% 59.43/7.97  num_eq_ax_congr_red:                    135
% 59.43/7.97  num_of_sem_filtered_clauses:            1
% 59.43/7.97  num_of_subtypes:                        0
% 59.43/7.97  monotx_restored_types:                  0
% 59.43/7.97  sat_num_of_epr_types:                   0
% 59.43/7.97  sat_num_of_non_cyclic_types:            0
% 59.43/7.97  sat_guarded_non_collapsed_types:        0
% 59.43/7.97  num_pure_diseq_elim:                    0
% 59.43/7.97  simp_replaced_by:                       0
% 59.43/7.97  res_preprocessed:                       206
% 59.43/7.97  prep_upred:                             0
% 59.43/7.97  prep_unflattend:                        1
% 59.43/7.97  smt_new_axioms:                         0
% 59.43/7.97  pred_elim_cands:                        3
% 59.43/7.97  pred_elim:                              1
% 59.43/7.97  pred_elim_cl:                           1
% 59.43/7.97  pred_elim_cycles:                       3
% 59.43/7.97  merged_defs:                            0
% 59.43/7.97  merged_defs_ncl:                        0
% 59.43/7.97  bin_hyper_res:                          0
% 59.43/7.97  prep_cycles:                            4
% 59.43/7.97  pred_elim_time:                         0.001
% 59.43/7.97  splitting_time:                         0.
% 59.43/7.97  sem_filter_time:                        0.
% 59.43/7.97  monotx_time:                            0.
% 59.43/7.97  subtype_inf_time:                       0.
% 59.43/7.97  
% 59.43/7.97  ------ Problem properties
% 59.43/7.97  
% 59.43/7.97  clauses:                                45
% 59.43/7.97  conjectures:                            6
% 59.43/7.97  epr:                                    8
% 59.43/7.97  horn:                                   32
% 59.43/7.97  ground:                                 5
% 59.43/7.97  unary:                                  13
% 59.43/7.97  binary:                                 12
% 59.43/7.97  lits:                                   109
% 59.43/7.97  lits_eq:                                53
% 59.43/7.97  fd_pure:                                0
% 59.43/7.97  fd_pseudo:                              0
% 59.43/7.97  fd_cond:                                8
% 59.43/7.97  fd_pseudo_cond:                         7
% 59.43/7.97  ac_symbols:                             0
% 59.43/7.97  
% 59.43/7.97  ------ Propositional Solver
% 59.43/7.97  
% 59.43/7.97  prop_solver_calls:                      100
% 59.43/7.97  prop_fast_solver_calls:                 2191
% 59.43/7.97  smt_solver_calls:                       0
% 59.43/7.97  smt_fast_solver_calls:                  0
% 59.43/7.97  prop_num_of_clauses:                    99354
% 59.43/7.97  prop_preprocess_simplified:             62167
% 59.43/7.97  prop_fo_subsumed:                       27
% 59.43/7.97  prop_solver_time:                       0.
% 59.43/7.97  smt_solver_time:                        0.
% 59.43/7.97  smt_fast_solver_time:                   0.
% 59.43/7.97  prop_fast_solver_time:                  0.
% 59.43/7.97  prop_unsat_core_time:                   0.006
% 59.43/7.97  
% 59.43/7.97  ------ QBF
% 59.43/7.97  
% 59.43/7.97  qbf_q_res:                              0
% 59.43/7.97  qbf_num_tautologies:                    0
% 59.43/7.97  qbf_prep_cycles:                        0
% 59.43/7.97  
% 59.43/7.97  ------ BMC1
% 59.43/7.97  
% 59.43/7.97  bmc1_current_bound:                     -1
% 59.43/7.97  bmc1_last_solved_bound:                 -1
% 59.43/7.97  bmc1_unsat_core_size:                   -1
% 59.43/7.97  bmc1_unsat_core_parents_size:           -1
% 59.43/7.97  bmc1_merge_next_fun:                    0
% 59.43/7.97  bmc1_unsat_core_clauses_time:           0.
% 59.43/7.97  
% 59.43/7.97  ------ Instantiation
% 59.43/7.97  
% 59.43/7.97  inst_num_of_clauses:                    8252
% 59.43/7.97  inst_num_in_passive:                    2852
% 59.43/7.97  inst_num_in_active:                     2376
% 59.43/7.97  inst_num_in_unprocessed:                3024
% 59.43/7.97  inst_num_of_loops:                      2570
% 59.43/7.97  inst_num_of_learning_restarts:          0
% 59.43/7.97  inst_num_moves_active_passive:          194
% 59.43/7.97  inst_lit_activity:                      0
% 59.43/7.97  inst_lit_activity_moves:                0
% 59.43/7.97  inst_num_tautologies:                   0
% 59.43/7.97  inst_num_prop_implied:                  0
% 59.43/7.97  inst_num_existing_simplified:           0
% 59.43/7.97  inst_num_eq_res_simplified:             0
% 59.43/7.97  inst_num_child_elim:                    0
% 59.43/7.97  inst_num_of_dismatching_blockings:      1865
% 59.43/7.97  inst_num_of_non_proper_insts:           6472
% 59.43/7.97  inst_num_of_duplicates:                 0
% 59.43/7.97  inst_inst_num_from_inst_to_res:         0
% 59.43/7.97  inst_dismatching_checking_time:         0.
% 59.43/7.97  
% 59.43/7.97  ------ Resolution
% 59.43/7.97  
% 59.43/7.97  res_num_of_clauses:                     0
% 59.43/7.97  res_num_in_passive:                     0
% 59.43/7.97  res_num_in_active:                      0
% 59.43/7.97  res_num_of_loops:                       210
% 59.43/7.97  res_forward_subset_subsumed:            44
% 59.43/7.97  res_backward_subset_subsumed:           0
% 59.43/7.97  res_forward_subsumed:                   0
% 59.43/7.97  res_backward_subsumed:                  0
% 59.43/7.97  res_forward_subsumption_resolution:     0
% 59.43/7.97  res_backward_subsumption_resolution:    0
% 59.43/7.97  res_clause_to_clause_subsumption:       135751
% 59.43/7.97  res_orphan_elimination:                 0
% 59.43/7.97  res_tautology_del:                      0
% 59.43/7.97  res_num_eq_res_simplified:              0
% 59.43/7.97  res_num_sel_changes:                    0
% 59.43/7.97  res_moves_from_active_to_pass:          0
% 59.43/7.97  
% 59.43/7.97  ------ Superposition
% 59.43/7.97  
% 59.43/7.97  sup_time_total:                         0.
% 59.43/7.97  sup_time_generating:                    0.
% 59.43/7.97  sup_time_sim_full:                      0.
% 59.43/7.97  sup_time_sim_immed:                     0.
% 59.43/7.97  
% 59.43/7.97  sup_num_of_clauses:                     22886
% 59.43/7.97  sup_num_in_active:                      495
% 59.43/7.97  sup_num_in_passive:                     22391
% 59.43/7.97  sup_num_of_loops:                       513
% 59.43/7.97  sup_fw_superposition:                   18017
% 59.43/7.97  sup_bw_superposition:                   8243
% 59.43/7.97  sup_immediate_simplified:               2544
% 59.43/7.97  sup_given_eliminated:                   5
% 59.43/7.97  comparisons_done:                       0
% 59.43/7.97  comparisons_avoided:                    33
% 59.43/7.97  
% 59.43/7.97  ------ Simplifications
% 59.43/7.97  
% 59.43/7.97  
% 59.43/7.97  sim_fw_subset_subsumed:                 287
% 59.43/7.97  sim_bw_subset_subsumed:                 34
% 59.43/7.97  sim_fw_subsumed:                        163
% 59.43/7.97  sim_bw_subsumed:                        316
% 59.43/7.97  sim_fw_subsumption_res:                 0
% 59.43/7.97  sim_bw_subsumption_res:                 0
% 59.43/7.97  sim_tautology_del:                      22
% 59.43/7.97  sim_eq_tautology_del:                   1419
% 59.43/7.97  sim_eq_res_simp:                        6
% 59.43/7.97  sim_fw_demodulated:                     1679
% 59.43/7.97  sim_bw_demodulated:                     1
% 59.43/7.97  sim_light_normalised:                   345
% 59.43/7.97  sim_joinable_taut:                      0
% 59.43/7.97  sim_joinable_simp:                      0
% 59.43/7.97  sim_ac_normalised:                      0
% 59.43/7.97  sim_smt_subsumption:                    0
% 59.43/7.97  
%------------------------------------------------------------------------------
